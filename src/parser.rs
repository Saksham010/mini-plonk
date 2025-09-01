// Plonkish arithmetization
use std::fs;
use regex::Regex;
use std::io::BufReader;
use serde_json;
use std::collections::{HashMap,HashSet};
use ark_bn254::{Fr,FqConfig,G1Projective as G1, G2Projective as G2}; // Scalar field
use ark_ff::fields::{Field,PrimeField};
use ark_ff::{Fp,MontBackend,UniformRand};
use rand::thread_rng;

use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, univariate::DensePolynomial}; 
use ark_poly::DenseUVPolynomial;
use ark_poly::Polynomial;

use spongefish::codecs::arkworks_algebra::*;  
use spongefish::{DomainSeparator,DefaultHash};

use std::fs::File;
use std::io::{Result,Read,Cursor};
use ark_serialize::CanonicalSerialize;
use ark_serialize::Write;
use ark_serialize::CanonicalDeserialize;

use std::ops::Mul;



// use ark_ff::fields::PrimeField;
   
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
    let mut l_operand = fetch_operand_and_save_coeff(l,index,coeff_matrix,0);
    let mut r_operand = fetch_operand_and_save_coeff(r,index,coeff_matrix,1);
    let mut o_operand = fetch_operand_and_save_coeff(o,index,coeff_matrix,2);

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
        // (TOCHANGE) Done

        operator = '*';
        // r_operand  = "{".to_string()+&r_operand+"}"; // {} => inverse sign (CHANGED)

        // (left,right,out,operator) [left/right=out]  => [out*right=left] (out,right,left,operator) (Swap operands/coeff)
        let temp = o_operand;
        o_operand = l_operand;
        l_operand = temp;

        // Divide original out(new: left) and right coeff by left coeff (new: out)

        //Fetch left and right coefficient
        let val_left = if &coeff_matrix[*index][0] == "" {"1".to_string()} else {coeff_matrix[*index][0].clone()};
        let val_right = if &coeff_matrix[*index][1] == "" {"1".to_string()} else {coeff_matrix[*index][1].clone()};

        //Update coefficient matrix : [2,3,1] => [1/2,3/2,1] as 2a/3b=r becomes (1/2)r*(3/2)b = a
        coeff_matrix[*index][0] = "1/".to_string() + &val_left; //Update left
        coeff_matrix[*index][1] = val_right.to_string()+"/"+&val_left;

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
    //(TODO Limit to the size of required domain)
    let domain = Radix2EvaluationDomain::<Fr>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<Fr> = domain.elements().collect(); 
    println!("Evaluation domain elements: {:?}",roots);
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

// Sample random field elements
fn sample_random_scalars(num_of_scalars:i32)->Vec<Fr>{
    let mut scalar_arr:Vec<Fr> = Vec::new();
    for i in 0..num_of_scalars{
        let mut rng = thread_rng();
        let random_fr: Fr = Fr::rand(&mut rng);
        scalar_arr.push(random_fr);
    }
    scalar_arr
}

// Vanishing polynomial (Zh(x)) (For roots of unity)
fn compute_vanishing_poly(eval_domain:&Vec<Fr>)->DensePolynomial<Fr>{

    let x_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![Fr::from(0),Fr::from(1)]); // x
    let mut x_n_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![Fr::from(1)]);
    for i in eval_domain{
        x_n_poly = x_n_poly*&x_poly;
        
    }
    let z_h_poly = x_n_poly - get_dense_uv_poly(vec![Fr::from(1)]); //x^n-1
    z_h_poly
}   

// s^k
fn get_eval_k(tau:Fr,times:usize)->Fr{
    let mut t_final =Fr::from(1u8);
    for _ in 0..times{
        t_final = t_final*tau;
    }
    t_final

}

// Load srs
fn load_srs_from_file(file_name:&str) -> Result<Vec<G1>>{
    let mut final_srs:Vec<G1> = Vec::new();

    let mut file = File::open(file_name).unwrap();
    println!("Loading buffer....");

    //Buffer to load the file
    let mut buffer:Vec<u8> = Vec::new();
    file.read_to_end(&mut buffer).unwrap();

    println!("Buffer loaded....");

    let mut cursor = Cursor::new(&buffer[..]);

    //Deserialze the file
    while (cursor.position() as usize) < cursor.get_ref().len(){ 

        //Read the length
        let mut element_len =[0u8];
        cursor.read_exact(&mut element_len).unwrap(); // Read x length

        let mut x_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut x_element).unwrap(); //Read x 

        cursor.read_exact(&mut element_len).unwrap(); // Read y length
        let mut y_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut y_element).unwrap(); //Read y 

        cursor.read_exact(&mut element_len).unwrap(); // Read z length
        let mut z_element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut z_element).unwrap(); //Read z

        //Deseralize
        let mut cursorx = Cursor::new(x_element);
        let mut cursory = Cursor::new(y_element);
        let mut cursorz = Cursor::new(z_element);

        let deserialized_x:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorx).unwrap();
        let deserialized_y:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursory).unwrap();
        let deserialized_z:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorz).unwrap();

        let element:G1 = G1::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check

        final_srs.push(element);
    }

    Ok(final_srs)
}

//Compute commitment [a]1
fn compute_commitment(srs:&Vec<G1>,x_poly:DensePolynomial<Fr>)->G1{
    let mut val_commitment:G1 = *srs.get(0).expect("Index out of bounds"); // g^1

    for (i,coeff) in x_poly.coeffs().iter().enumerate(){ // Ensure order of a_poly.coeffs()
        // We get powers of tau from KZG setup and use here
        let g_i_tau:G1 = *srs.get(i).expect("Index out of bounds");
        let g_i_tau_s:G1 = g_i_tau.mul(*coeff);
        val_commitment = val_commitment + g_i_tau_s; // g^tau^2^a * g^tau*b * g^1^c = g^(a*tau^2 + b*tau + c) (As * requires pairing g^a * g^b is done using + operation)
    }
    val_commitment
}

// Get position of character from matrix 
fn get_position_from_matrix<T:std::cmp::PartialEq>(element:T,matrix:&Vec<Vec<T>>)->Vec<(usize,usize)>{
    let mut index_pair_list:Vec<(usize,usize)> = Vec::new();

    for (i,row) in matrix.iter().enumerate(){
        for (j,col) in row.iter().enumerate(){
            if *col == element{
                index_pair_list.push((i,j));
            }
        }
    }

    index_pair_list
}

//Permutation function sigma(i) -> H' (Rotation of equivalence class)
fn permutation_function(i:usize,gate_no:usize,operand_map:&HashMap<String,Vec<Fr>>,evaluation_domain_h_k1_k2:&Vec<Fr>,position_matrix:&Vec<Vec<Fr>>,operand_list:&Vec<Vec<String>>)->Fr{
    assert!(i<3*gate_no); //(w^0...k1w^0....k2w^0...k2w^n-1)

    let w:Fr = evaluation_domain_h_k1_k2[i];
    let indexpair_list:Vec<(usize,usize)> = get_position_from_matrix(w,&position_matrix);
    assert!(indexpair_list.len()==1);//Position matrix have unique w^i/k1w^i/k2w^i
    
    let (_i,_j):(usize,usize) = indexpair_list[0];

    let operand = &operand_list[_i][_j];
    let roots_unity_set:&Vec<Fr> = operand_map.get(operand).expect("Permutation map error!! No permutation set for operand found.");
    let set_len = roots_unity_set.len();
    let mut permuted_w:Fr = Fr::from(0u64);

    for (i,val) in roots_unity_set.iter().enumerate(){
        if *val == w{
            let permuted_index:usize = (i+1)%set_len; //Get the permuted index
            permuted_w = roots_unity_set[permuted_index];
        }
    }

    // println!("Unpermuted w: {:?}",w);
    // println!("Permuted w: {:?}",&permuted_w);
    // println!("Operand: {:?}",operand);
    // println!("ROU SET : {:?}",roots_unity_set);
    permuted_w
}

//Get witness (L,R,O) from execution trace
fn get_witness_from_trace(pos:usize,index:usize,execution_trace:&Vec<Vec<Fr>>)->Fr{
    assert!(pos<=3); //left,right,out
    let mut witness:Fr = Fr::from(0);
    for (i,row) in execution_trace.iter().enumerate(){
        if i == index{
            witness = row[pos];
        }
    }
    witness
}

//Compute lagrange basis Li(x) 
fn compute_lagrange_basis(i:usize,evaluation_domain:&Vec<Fr>)->DensePolynomial<Fr>{

    let w_i = evaluation_domain[i]; //w_i
    let mut lagrange_basis_i:DensePolynomial<Fr> = DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]); //1
    for k in evaluation_domain{
        if *k != w_i{
            let ratio:DensePolynomial<Fr> = (DensePolynomial::from_coefficients_vec(vec![Fr::from(0),Fr::from(1)])-DensePolynomial::from_coefficients_vec(vec![*k]))/DensePolynomial::from_coefficients_vec(vec![(w_i - *k)]); // (x-k)/(wi-k)
            lagrange_basis_i = lagrange_basis_i * ratio;
        }
    }
    lagrange_basis_i

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
            // Checks for invertible operator (TO SKIP NO LONGER USE)
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
                if invertible{ //(TO SKIP NO LONGER USE)
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
                //If coeff is divisive eg:1/2
                let div_index_str = match celement.find("/"){
                    Some(div_index) => div_index.to_string(),
                    None => "-1".to_string()
                };

                let div_index:i32 = div_index_str.parse().expect("Parsing error: Invalid number!!");
                println!("Div index: {:?}",div_index);
                // If divisble
                if div_index >= 0{
                    let left_val = &celement[..div_index as usize];
                    let right_val = &celement[(div_index+1) as usize..];
                    let left_val_num:i32 = left_val.parse().expect("Parsing error: Invalid number!!");
                    let right_val_num:i32 = right_val.parse().expect("Parsing error: Invalid number!!");
                    let left_val_fr = get_fr_from_i32(left_val_num);
                    let right_val_fr = get_fr_from_i32(right_val_num);
                    let div_value_fr = left_val_fr/right_val_fr;
                    coeff_matrix_fr[cindex][_ci] = div_value_fr;
                }else{

                    let num:i32 = celement.parse().expect("Parsing error: Invalid number!!");
                    let num_fr = get_fr_from_i32(num);
                    coeff_matrix_fr[cindex][_ci] = num_fr;
                }
            }

        }

    }

    println!("Coeff_matrix_fr: {:?}",coeff_matrix_fr);

    // Construct execution trace
    // Wl | Wr | Wo | Qm | Ql | Qr | Qo | Qc
    let mut execution_trace:Vec<Vec<Fr>> = vec![vec![Fr::from(0u64);8];constraints.len()];

    // Fill execution trace
    for (i, row) in coeff_matrix_fr.iter().enumerate() {
        //Fetch coefficient and operands for a given gate
        let left_coeff = coeff_matrix_fr[i][0];
        let right_coeff = coeff_matrix_fr[i][1];
        let left_witness = operand_val_list[i][0];
        let right_witness = operand_val_list[i][1];
        let out_witness = operand_val_list[i][2];
        let operator = operator_list[i];

        //Update execution trace

        //Multiplication operation
        if operator == '*'{

            execution_trace[i][0] = left_witness; //Wl
            execution_trace[i][1] = right_witness; //Wr
            execution_trace[i][2] = out_witness; //Wo
            execution_trace[i][3] = left_coeff*right_coeff; //Qm=1 or scaled eg: 2a*3b=r => 6(a*b)
            execution_trace[i][6] = -Fr::from(1u64); //Qo=-1

        }else if operator == '+'{
            //Addition operation

            execution_trace[i][0] = left_witness; //Wl
            execution_trace[i][1] = right_witness; //Wr
            execution_trace[i][2] = out_witness; //Wo
            execution_trace[i][4] = left_coeff; //Ql=coeff
            execution_trace[i][5] = right_coeff; //Qr=coeff
            execution_trace[i][6] = -Fr::from(1u64); //Qo=-1

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
    let ql_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,ql_eval);
    let qr_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qr_eval);
    let qo_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qo_eval);
    let qc_poly:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,qc_eval);

    //Public inputs (Scrapped)
    
    // (Round 1)

    // Sample 9 random field elements
    let random_scalars_b:Vec<Fr> = sample_random_scalars(9); // [b1,..,b9]

    // Compute vanishing polynomial ZH(x) over evaluation domain
    let z_h_poly = compute_vanishing_poly(&evaluation_domain);

    // Compute binding polynomial a(x),b(x) and c(x)
    let a_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![random_scalars_b[0],random_scalars_b[1]]) * &z_h_poly + &wl_poly;
    let b_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![random_scalars_b[2],random_scalars_b[3]]) * &z_h_poly + &wr_poly;
    let c_poly:DensePolynomial<Fr> = get_dense_uv_poly(vec![random_scalars_b[4],random_scalars_b[5]]) * &z_h_poly + &wo_poly;

    // Commit the bindig polynomials
    // let g1 = G1::generator(); //Generator on the curve G1Projective
    // let g2 = G2::generator(); //Generator on the curve G2projective

    //Fetch SRS
    let mut srs:Vec<G1> = load_srs_from_file("./kzg_srs.zkey").expect("Failed to load");

    let mut a_commitment:G1 = compute_commitment(&srs,a_poly);
    let mut b_commitment:G1 = compute_commitment(&srs,b_poly);
    let mut c_commitment:G1 = compute_commitment(&srs,c_poly);

    println!("a_commitment: {:?}",a_commitment);
    println!("b_commitment: {:?}",b_commitment);
    println!("c_commitment: {:?}",c_commitment);


    // Round 2

    //(Preprcessing section)
    
    // 2.1 Create cosets
    let k1_k2:Vec<Fr> = sample_random_scalars(2); // [k1,k2]
    let mut eval_domain_h:Vec<Fr> = evaluation_domain.clone(); // H
    let eval_domain_h_k1:&Vec<Fr> = &evaluation_domain.iter().map(|w|{w*&k1_k2[0]}).collect(); // k1H
    let eval_domain_h_k2:&Vec<Fr> = &evaluation_domain.iter().map(|w|{w*&k1_k2[1]}).collect(); // k2H
    eval_domain_h.extend(eval_domain_h_k1.iter().clone());
    eval_domain_h.extend(eval_domain_h_k2.iter().clone());
    let evaluation_domain_h_k1_k2 = eval_domain_h; // H' = {H U k1H U k2H}

    // 2.2 Create permutation function
    // 2.2.a Create a matrix with LRO, with position values from the coset H' 
    // L | R | O
    let mut position_matrix:Vec<Vec<Fr>> = vec![vec![Fr::from(0u64);3];constraints.len()];
    //Fill positionn matrix with value from cosets      w^0 | k1*w^0 | k2*w^0
    let circuit_size = constraints.len(); // n
    for (i,row) in position_matrix.clone().iter().enumerate(){
        position_matrix[i][0] = evaluation_domain_h_k1_k2[i];
        position_matrix[i][1] = evaluation_domain_h_k1_k2[i+circuit_size];
        position_matrix[i][2] = evaluation_domain_h_k1_k2[i+2*circuit_size];
    } 
    println!("Position matrix: {:?}",&position_matrix);
    // 2.2.b Read circuit and add the position to a set, eg: a ->{w,k1w,k2w^2}
    //Map of set of positions Eg: a -> {1,w^2}
    let mut operand_map:HashMap<String,Vec<Fr>> = HashMap::new();

    for operands_gate in &operand_list{
        for operand in operands_gate{
            //Check if the operand has already been checked
            if !operand_map.contains_key(operand) {
                let index_list:Vec<(usize,usize)> = get_position_from_matrix(operand.to_string(),&operand_list);

                //Extract positions
                let mut position_set:Vec<Fr> = Vec::new();
                for (i,j) in index_list {
                    position_set.push(position_matrix[i][j]);
                }
                
                operand_map.insert(operand.to_string(),position_set);

            }

        }        
    }
    println!("Operand map: {:?}",operand_map);

    // Create permutation polynomials
    let mut permuted_root_unity_y:Vec<Fr> = Vec::new();
    let mut permuted_root_unity_k1_y:Vec<Fr> = Vec::new();
    let mut permuted_root_unity_k2_y:Vec<Fr> = Vec::new();

    for i in 0..circuit_size as i32{ //0-(n-1)

        let permuted_root_unity:Fr = permutation_function(i as usize,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list);
        let permuted_root_unity_k1:Fr = permutation_function(i as usize +circuit_size,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list);
        let permuted_root_unity_k2:Fr = permutation_function(i as usize +2*circuit_size,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list);

        permuted_root_unity_y.push(permuted_root_unity);
        permuted_root_unity_k1_y.push(permuted_root_unity_k1);
        permuted_root_unity_k2_y.push(permuted_root_unity_k2);
    }

    let permutation_poly_sigma_1:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_y);
    let permutation_poly_sigma_2:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_k1_y);
    let permutation_poly_sigma_3:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_k2_y);

    println!("Sigma1 :{:?}",permutation_poly_sigma_1);
    println!("Sigma2 :{:?}",permutation_poly_sigma_2);
    println!("Sigma3 :{:?}",permutation_poly_sigma_3);


    //Preprocessed transcript
    let mut transcript_final:Vec<Fr> = Vec::new();
    let transcript_0 = [
        Fr::from(circuit_size as u64), //n
        k1_k2[0], // k1
        k1_k2[1], // k2
        permutation_function(circuit_size as usize,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list) // Sigma(n)
    ];
    transcript_final.extend(&transcript_0);
    transcript_final.extend(qm_poly.coeffs()); //qm(x)
    transcript_final.extend(ql_poly.coeffs()); //ql(x)
    transcript_final.extend(qr_poly.coeffs()); //qr(x)
    transcript_final.extend(qo_poly.coeffs()); //qo(x)
    transcript_final.extend(qc_poly.coeffs()); //qc(x)
    transcript_final.extend(permutation_poly_sigma_1.coeffs()); //Sigma1(x)
    transcript_final.extend(permutation_poly_sigma_2.coeffs()); //Sigma2(x)
    transcript_final.extend(permutation_poly_sigma_3.coeffs()); //Sigma3(x)

    // Evaluate how the deterministic oracle with fiat shamir transformation will work

    let domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("bn254-plonk"),
        transcript_final.len(),
        "full_transcript",
    );

    let domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        2,               // number of scalars for the challenge
        "challenge 1",         // label for the challenge
    );

    let mut prover_state = domsep.to_prover_state();
  
    // Add transcript
    prover_state.add_scalars(&transcript_final).expect("Fiat shamir error!! Scalar addition failed");  
    

    //Round 2 (Generate challenges)  
    // Generate challenge for beta and gamma
    let [beta,gamma]: [Fr; 2] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    //Compute permutation polynomial accumulations
    let mut permutation_poly_y:Vec<Fr> = vec![Fr::from(1)]; // Set z(w^0) = 1 [evals for interpolating permutation poly]
    for i in 1..circuit_size{
        let mut cumulative_product:Fr = Fr::from(1);
        for j in 1..i{
                        // (wi + beta*w^i+ gamma) * (wn+i + beta*k1w^i+ gamma) * (w2n+i + beta*k2w^i+ gamma)
            let f_i:Fr = (get_witness_from_trace(0,j,&execution_trace) + beta*evaluation_domain_h_k1_k2[j] + gamma)
                         *(get_witness_from_trace(1,j,&execution_trace) + beta*evaluation_domain_h_k1_k2[j+circuit_size] + gamma)
                         *(get_witness_from_trace(2,j,&execution_trace) + beta*evaluation_domain_h_k1_k2[j+2*circuit_size] + gamma); 

            let g_i:Fr = (get_witness_from_trace(0,j,&execution_trace) + beta*permutation_function(j as usize,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list) + gamma)
                         *(get_witness_from_trace(1,j,&execution_trace) + beta*permutation_function(j as usize + circuit_size,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list) + gamma)
                         *(get_witness_from_trace(2,j,&execution_trace) + beta*permutation_function(j as usize + 2*circuit_size,circuit_size,&operand_map,&evaluation_domain_h_k1_k2,&position_matrix,&operand_list) + gamma); 

            let div:Fr = f_i/g_i;
            cumulative_product = cumulative_product * div;
        }
        permutation_poly_y.push(cumulative_product);
    }
     
    //Evaluation domain 
    let z_poly_half:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permutation_poly_y); // (w^0,1),(w,y1)...
    // let l_basis_0:DensePolynomial<Fr> = compute_lagrange_basis(0,&evaluation_domain);
    // (b7x^2+ b8x+ b9)Zh(x) + z'(x)
    let z_permutation_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(random_scalars_b[8]),Fr::from(random_scalars_b[7]),Fr::from(random_scalars_b[6])]) * z_h_poly + z_poly_half;
    let z_commitment:G1 = compute_commitment(&srs,z_permutation_poly.clone());

    println!("Permutation polynomial: {:?}",z_permutation_poly);
    println!("Z_commitment: {:?}",z_commitment);

    println!("Permutation polynomial eval: {:?}",z_permutation_poly.evaluate(&evaluation_domain[0]));


    // Round 3


}
