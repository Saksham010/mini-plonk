// Plonkish arithmetization
use std::fs;
use regex::Regex;
use std::io::BufReader;
use serde_json;
use std::collections::HashMap;
use ark_bn254::Fr; // Scalar field
use ark_ff::fields::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, univariate::DensePolynomial}; 
use ark_poly::DenseUVPolynomial;
   
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

//Get evaluation from execution trace
fn get_evals(execution_trace:&Vec<Vec<Fr>>,col_index:usize)->Vec<Fr>{
    let mut eval_list:Vec<Fr> = Vec::new();
    let mut c_index = 0;
    for row in execution_trace{
        for val in row{
            if c_index == col_index{
                eval_list.push(*val);
                break;//Break this loop
            }

            c_index = c_index+1;
        }
        c_index=0;//Reset

    }
    eval_list
}

//Generate roots of unity
fn generate_evaluation_domain(size:usize)->Vec<Fr>{
    let domain = Radix2EvaluationDomain::<Fr>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<Fr> = domain.elements().collect(); 
    roots
}

// Get evaluation domain at i'th position
fn get_eval_at(i:usize,evaluation_domain:Vec<Fr>)->Fr{
    evaluation_domain[i]
}

//Get denseuv polynomial from vec
fn get_dense_uv_poly(coeff:Vec<Fr>)->DensePolynomial<Fr>{
    DensePolynomial::from_coefficients_vec(coeff)
}


//Lagrange interpolation
fn lagrange_interpolation(x:&Vec<Fr>,y:Vec<Fr>)->DensePolynomial<Fr>{
    if x.len() != y.len(){
        panic!("Interpolation error: X,Y length is not equal!!");
    }

    let mut lagrange_basis_poly:Vec<DensePolynomial<Fr>>=Vec::new();
    let mut interpolated_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![Fr::from(0)]);


    for i in 0..x.len(){    
        let mut li_x:DensePolynomial<Fr> = DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]);
        for k in x {
            // k != wi 
            if *k != x[i]{
                //(x-k)/(wi-k)
                // let denominator:Fr = x[i]-*k;
                // let denom_inv = denominator.inverse().expect("Inverse error: Division by zero!!");
                // let li:DensePolynomial<Fr> = get_dense_uv_poly(vec![-*k,Fr::from(1)]) * denom_inv;

                let t_li:DensePolynomial<Fr> = (get_dense_uv_poly(vec![Fr::from(0),Fr::from(1)]) - get_dense_uv_poly(vec![*k]))/get_dense_uv_poly(vec![x[i]-*k]); 
                li_x = li_x * t_li;
            }
            
        }
        // lagrange_basis_poly.push(li);
        interpolated_poly = interpolated_poly + get_dense_uv_poly(vec![y[i]]) * li_x;

    }
    println!("Interpolated polynomial: {:?}", &interpolated_poly);

    interpolated_poly

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
    for c in &constraints{
        let (l_operand,r_operand,o_operand,operator) = get_lro(c,&index,&mut coeff_matrix);
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

    // Convert coeff matrix element into finite field
    let mut coeff_matrix_fr:Vec<Vec<Fr>> = vec![vec![Fr::from(1u64);3];constraints.len()];

    for (cindex,coeff_list) in coeff_matrix.iter().enumerate(){
        for (_ci,celement) in coeff_list.iter().enumerate(){
            // No coeff -> 1
            if celement == ""{
                continue;
                // coeff_matrix_fr[cindex][_ci]=Fr::from(1u64); //Which is initialized by default
            }
            else{
                let num:i32 = celement.parse().expect("Parsing error: Invalid number!!");
                let num_fr = get_fr_from_i32(num);
                coeff_matrix_fr[cindex][_ci] = num_fr;
            }

        }

    }

    println!("Coeff_matrix_fr: {:?}",coeff_matrix_fr);

    // Construct execution trace
    // Wl | Wr | Wo | Qm | Ql | Qr | Qo | Qc
    let mut execution_trace:Vec<Vec<Fr>> = vec![vec![Fr::from(0u64);8];constraints.len()];

    for (i_c, coeff_fr_list) in coeff_matrix_fr.iter().enumerate() {
        for (i_w,witness_fr_list) in operand_val_list.iter().enumerate(){
            // Same row
            if i_c == i_w {
                // Iterate over the row's columns
                for (col_i, (coeff_fr, witness_fr)) in coeff_fr_list.iter().zip(witness_fr_list).enumerate(){
                    execution_trace[i_c][col_i] = coeff_fr*witness_fr;
                }
                //Instantiate selector for the constraint
                if operator_list[i_c] == '*'{
                    //Multiplication gate
                    execution_trace[i_c][3] = Fr::from(1u64); //Qm=1
                    execution_trace[i_c][6] = -Fr::from(1u64); //Qo=-1
                }else{
                    //Addition gate
                    execution_trace[i_c][4] = Fr::from(1u64); //Ql=1
                    execution_trace[i_c][5] = Fr::from(1u64); //Qr=1
                    execution_trace[i_c][6] = -Fr::from(1u64); //Qo=-1
                }

                break; //Break inner loop

            }
        }
    }
    println!("Execution trace: {:?}",execution_trace);

    //Roots of unity (1,w,w^2,w^3,w^4,..,w^n-1)
    let evaluation_domain:Vec<Fr> = generate_evaluation_domain(constraints.len());
    let wl_eval = get_evals(&execution_trace,0);
    let wr_eval = get_evals(&execution_trace,1);
    let wo_eval = get_evals(&execution_trace,2);
    let qm_eval = get_evals(&execution_trace,3);
    let ql_eval = get_evals(&execution_trace,4);
    let qr_eval = get_evals(&execution_trace,5);
    let qo_eval = get_evals(&execution_trace,6);
    let qc_eval = get_evals(&execution_trace,7);
    println!("-------------------------------------------------------------");
    println!("Evaluation domain : {:?}",&evaluation_domain);
    println!("Evaluation y: {:?}",&wl_eval );

    //Lagrange interpolation from the execution trace
    let wl_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,wl_eval);
    let wr_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,wr_eval);
    let wo_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,wo_eval);
    let qm_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qm_eval);
    let qr_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qr_eval);
    let qo_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qo_eval);
    let qc_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qc_eval);

    //Public inputs


    // Evaluate how the deterministic oracle with fiat shamir transformation will work

    // Linear combination



    // Proof generation


}
