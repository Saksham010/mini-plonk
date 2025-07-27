// Plonkish arithmetization
use std::fs;
use regex::Regex;
use std::io::BufReader;
use serde_json;
use std::collections::HashMap;
use ark_bn254::Fr; // Scalar field
use ark_ff::fields::Field;
 

const OPERATIONS:[&str;4] = ["*","+","-","/"];

// Macro to simulate default params
macro_rules! get_o{
    ($c: expr) => {
        get_o($c,0,0,0)
    };
}

fn get_o(c:&String,op_index:usize,index:usize,num:u32)-> (usize,char) {
    // Base case
    if index == 4{
        if num == 0{
            panic!("Parser error: No operator found");
        }
        return (op_index,c.chars().nth(op_index).expect("Parser error: Index out of bounds!!"));
    }

    if let Some(op_index) = c.find(OPERATIONS[index]){
        // If more than one index found
        if num > 1{
            panic!("Parser error: More than one operator found!!");
        }

        get_o(c,op_index,index+1,num+1)

    }else {
        get_o(c,op_index,index+1,num)
    }
}

//Fetch operand and save coeff in the coeff matrix
fn fetch_operand_and_save_coeff(_slice:&str,index:&usize,coeff_matrix:&mut Vec<Vec<String>>,_cindex:usize)->String{

    // Parse coefficients 
    let mut bracket_tracker:bool = false;
    let mut digit_tracker:bool = false;
    let mut temp:String = String::from("");
    for element in _slice.chars(){
        if element == '['{
            bracket_tracker = true; //Open bracket encountered
            temp = temp+ "-";//Neg sign for char coeff
        }else if element == ']'{
            if !bracket_tracker{
                panic!("Parser error: Neg coeff bracket closed without opening");
            }

            // Neg coeff commit
            coeff_matrix[*index][_cindex] = temp.clone();
            println!("Negative coeff: {:?}",temp);
            println!("Coeff matrix: {:?}", coeff_matrix);

            temp = String::from("");
            bracket_tracker = false;


        }else{
            // Neg coeff
            if bracket_tracker{
                let _ = element.to_digit(10).expect("Parser error: Unable to parse neg coeff");
                temp = temp + element.to_string().as_str();

            }else{
                //If it's a positive coefficient
                if let Some(val) = element.to_digit(10){
                    digit_tracker = true;
                    temp = temp + char::from_digit(val, 10).expect("Parser error: Unable to convert from digit to char!!").to_string().as_str();
                }else{
                    // If its operand after coefficient
                    if digit_tracker{
                        //Save digit
                        coeff_matrix[*index][_cindex] = temp.clone();
                        println!("Positive coeff: {:?}",temp);
                        println!("Coeff matrix: {:?}", coeff_matrix);

                        temp = String::from("") + element.to_string().as_str(); // Apppend the alphabet
                        digit_tracker = false;
                    }else{
                        // If its operand after neg coeff or starts with operand                        
                        temp = temp + element.to_string().as_str();
                    }

                }
            }
        }

    }

    let operand = temp.clone();
    // println!("Operand: {:?}",&operand);
    operand

}

//Get left,right,output from constraint
fn get_lro(c:&String,index:&usize,coeff_matrix:&mut Vec<Vec<String>>)->(String,String,String,char){
    println!("{:?}",c);


    //Get operators
    let (op_index,op) = get_o!(c);
    println!("Found operator: {:?} at index: {:?}",op,op_index);

    // Seperate left, right and output operations
    let l_r_o:Vec<&str> = c.split(op).collect();
    let l:&str = l_r_o[0];
    let _r_o:&str = l_r_o[1];

    let r_o:Vec<&str> = _r_o.split("=").collect();
    let r:&str = r_o[0];
    let o:&str = r_o[1];

    println!("Left : {:?}",l);
    println!("Right : {:?}",r);
    println!("Out : {:?}",o);

    // Parse coefficients 
    let l_operand = fetch_operand_and_save_coeff(l,index,coeff_matrix,0);
    let mut r_operand = fetch_operand_and_save_coeff(r,index,coeff_matrix,1);
    let o_operand = fetch_operand_and_save_coeff(o,index,coeff_matrix,2);

    // Convert sub op to add op and div op to mul
    let mut operator:char = op;
    if op == '-'{
        operator = '+';
        let val = if &coeff_matrix[*index][1] == "" {"1"} else {&coeff_matrix[*index][1]};
      
        println!("Value to parse: {:?}",val);
        if let Ok(val) = val.parse::<i32>(){
            //Change sign
            coeff_matrix[*index][1] = (val*(-1)).to_string();
            println!("Update coeff matrix: {:?}",coeff_matrix);

        }else{panic!("Parser error: Not a valid coefficient in coeff matrix!!")} 
    }else if op == '/'{
        operator = '*';
        r_operand  = "{".to_string()+&r_operand+"}"; // {} => inverse sign
    }

    (l_operand,r_operand,o_operand,operator)

}

//Read witness values
fn read_witness(path:&str)-> HashMap<String,String>{
    let file = fs::File::open(path).expect("File error: Error opening {:?} !!");
    let reader = BufReader::new(file);
    let witness_values:HashMap<String,String> = serde_json::from_reader(reader).expect("Serde error: Cannot read json!!");
    witness_values
}

//Convert i32 to fr
fn get_fr_from_i32(num:i32)->Fr{
    let num_fr = if num <0{
        // If negative value
        -Fr::from((num*-1) as u64) //Negative a positive scalar field
    }else{
        // If positive
        Fr::from(num as u64)
    };
    num_fr
}
fn main() {
    let circuit = fs::read_to_string("./plonk.circuit").unwrap().replace("\r\n",",");
    let circuit_end = circuit.chars().nth(circuit.len()-1).expect("Index out of bounds");
    println!("{:?}",circuit);

    let mut constraints:Vec<String> = Vec::new(); // List of constraints
    // //Parse circuit
    let mut temp:String = String::from("");
    for c in circuit.chars() {
        if c == ',' || c == circuit_end{
            if c == circuit_end {
                temp = temp+c.to_string().as_str();
            }
            constraints.push(temp.clone());
            temp = "".to_string();
            continue;
        }
        temp = temp+c.to_string().as_str();
    }

    println!("Constraints: {:?}",constraints);

    // Generate trace from the constraint

    // 0.a) Create coefficient matrix (n*3)
    let mut coeff_matrix:Vec<Vec<String>> = vec![vec![String::from("");3];constraints.len()];
    let mut operand_list:Vec<Vec<String>> = Vec::new();
    let mut operator_list:Vec<char> = vec!['0';constraints.len()];
    println!("Initialized operand list: {:?}",operand_list);
    // a) Transform into multiplication and addition gates
    let mut index:usize = 0;
    for c in constraints{
        let (l_operand,r_operand,o_operand,operator) = get_lro(&c,&index,&mut coeff_matrix);
        operand_list.push(vec![l_operand,r_operand,o_operand]);
        operator_list[index] = operator;
        index = index+1;
    }

    println!("Final coeff matrix: {:?}",coeff_matrix);
    println!("Operand_list: {:?}",operand_list);
    println!("Operator list: {:?}",operator_list);

    // Fetch witness json value for the operands
    let witness:HashMap<String,String> = read_witness("./src/witness.json");
    let mut operand_val_list:Vec<Vec<Fr>> = Vec::new();
    //Check if witness matches the circuit
    for (constraint_no,op_list) in operand_list.iter().enumerate(){
        let mut temp:Vec<Fr> = Vec::new();
        for operand in op_list {
            let mut invertible:bool = false;
            let mut _operand = operand.clone();
            // Checks for invertible operator
            if _operand.find("{").is_some() && _operand.find("}").is_some(){
                //Invertible
                invertible = true;
                let re = Regex::new(r"\{([a-zA-Z]+)\}").unwrap();
                if let Some(val) = re.captures(&operand) {
                    _operand = val[1].to_string();  //Update the operand
                }

            }
            // Check if the witness containst the key or not
            if !witness.contains_key(&_operand){
                panic!("Witness doesn't match the circuit!!");
            }else{
                let value = witness.get(&_operand).expect("Hashmap Error: Matching key not found!!");
                let num:i32 = value.parse().expect("Parsing error: Invalid number!!");
                let mut num_fr = get_fr_from_i32(num);

                // Convert to finite field element
                if invertible{
                    //Invert 
                    num_fr = num_fr.inverse().expect("Inverse error: No inverse exists for zero");
                }
                temp.push(num_fr.clone());
            }
        }

        //Push the temp and clear
        operand_val_list.push(temp);
    }

    println!("Operand value list: {:?}",operand_val_list);

    // Construct execution trace



    // Evaluate how the deterministic oracle with fiat shamir transformation will work


}
