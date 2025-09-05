// Plonkish arithmetization
use std::fs;
use regex::Regex;
use std::io::BufReader;
use serde_json;
use std::collections::{HashMap,HashSet};
use ark_bn254::{Bn254,Fr,FqConfig,Fq2Config,G1Projective as G1, G2Projective as G2}; // Scalar field
use ark_ff::fields::{Field,PrimeField};
use ark_ff::{Fp,Fp2,MontBackend,UniformRand,QuadExtField,Fp2ConfigWrapper};
use rand::thread_rng;
use ark_ec::pairing::Pairing;

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

use std::ops::{Mul};

use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait

// Enum for proof
#[derive(Debug)]
#[derive(Clone)]
enum ProofElement{
    Group(G1),
    Field(Fr)
}

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
    let domain = Radix2EvaluationDomain::<Fr>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<Fr> = domain.elements().collect(); 
    println!("Evaluation domain elements: {:?}",roots);
    roots[0..size].to_vec() //(Limit to the size of required domain for size which is not powers of 2)
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
    // println!("Interpolated polynomial: {:?}", &interpolated_poly);

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

// Load SRS
fn load_srs_from_file(file_name:&str) -> Result<(Vec<G1>,Vec<G2>)>{
    let mut final_srs_one:Vec<G1> = Vec::new();
    let mut final_srs_two:Vec<G2> = Vec::new();

    let mut file = File::open(file_name).unwrap();
    println!("Loading buffer....");

    //Buffer to load the file
    let mut buffer:Vec<u8> = Vec::new();
    file.read_to_end(&mut buffer).unwrap();

    println!("Buffer loaded....");

    let mut cursor = Cursor::new(&buffer[..]);

    let mut index = 0;

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

        //G2 element
        if index == 0 || index == 1{
            let deserialized_x:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorx).unwrap();
            let deserialized_y:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursory).unwrap();
            let deserialized_z:QuadExtField<Fp2ConfigWrapper<Fq2Config>> = Fp2::deserialize_uncompressed(&mut cursorz).unwrap();

            let element:G2 = G2::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            final_srs_two.push(element);
        }else{
            let deserialized_x:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorx).unwrap();
            let deserialized_y:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursory).unwrap();
            let deserialized_z:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorz).unwrap();

            let element:G1 = G1::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            final_srs_one.push(element);
        }

        //Update index 
        index = index+1;
    }

    Ok((final_srs_one,final_srs_two))
}

//Compute commitment [a]1
fn compute_commitment(srs:&Vec<G1>,x_poly:DensePolynomial<Fr>)->G1{

    // println!("Poly: {:?}",&x_poly);
        // println!("Coeffs: {:?}",&x_poly.coeffs());
    //If polynomial is empty
    if x_poly.coeffs().len() == 0{ 
        let g_i_tau:G1 = *srs.get(0).expect("Index out of bounds");
        let g_i_tau_s:G1 = g_i_tau.mul(Fr::from(0));
        return g_i_tau_s;
    }

    // let mut val_commitment:G1 = *srs.get(0).expect("Index out of bounds"); // g^1
    let mut val_commitment:Vec<G1> = Vec::new();

    for (i,coeff) in x_poly.coeffs().iter().enumerate(){ // Ensure order of a_poly.coeffs()
        // We get powers of tau from KZG setup and use here
        let g_i_tau:G1 = *srs.get(i).expect("Index out of bounds");
        let g_i_tau_s:G1 = g_i_tau.mul(*coeff);
        // val_commitment = val_commitment + g_i_tau_s; // g^tau^2^a * g^tau*b * g^1^c = g^(a*tau^2 + b*tau + c) (As * requires pairing g^a * g^b is done using + operation)
       if val_commitment.len() == 0{
            val_commitment.push(g_i_tau_s);
        }else{
            val_commitment[0] = val_commitment[0] + g_i_tau_s;
        }    
    }
    val_commitment[0]
}
//Compute commitment in fr: [a]1
fn compute_commitment_fr_g1(srs:&Vec<G1>,x_:Fr)->G1{

    let x_poly = DensePolynomial::from_coefficients_vec(vec![x_]);
    let mut val_commitment:Vec<G1> = Vec::new();
    // let mut val_commitment:G1 = *srs.get(0).expect("Index out of bounds"); // g^1

    for (i,coeff) in x_poly.coeffs().iter().enumerate(){ // Ensure order of a_poly.coeffs()
        // We get powers of tau from KZG setup and use here
        let g_i_tau:G1 = *srs.get(i).expect("Index out of bounds");
        let g_i_tau_s:G1 = g_i_tau.mul(*coeff);

        if val_commitment.len() == 0{
            val_commitment.push(g_i_tau_s);
        }else{
            val_commitment[0] = val_commitment[0] + g_i_tau_s;
        }
        // val_commitment = val_commitment + g_i_tau_s; // g^tau^2^a * g^tau*b * g^1^c = g^(a*tau^2 + b*tau + c) (As * requires pairing g^a * g^b is done using + operation)
    }
    val_commitment[0]
}
//Compute commitment in g2: [a]2
fn compute_commitment_g2(srs:&Vec<G2>,x_poly:DensePolynomial<Fr>)->G2{
    // let mut val_commitment:G2 = *srs.get(0).expect("Index out of bounds"); // g^1
    let mut val_commitment:Vec<G2> = Vec::new();


    for (i,coeff) in x_poly.coeffs().iter().enumerate(){ // Ensure order of a_poly.coeffs()
        // We get powers of tau from KZG setup and use here
        let g_i_tau:G2 = *srs.get(i).expect("Index out of bounds");
        let g_i_tau_s:G2 = g_i_tau.mul(*coeff);
        if val_commitment.len() == 0{
            val_commitment.push(g_i_tau_s);
        }else{
            val_commitment[0] = val_commitment[0] + g_i_tau_s;
        }
        // val_commitment = val_commitment + g_i_tau_s; // g^tau^2^a * g^tau*b * g^1^c = g^(a*tau^2 + b*tau + c) (As * requires pairing g^a * g^b is done using + operation)
    }
    val_commitment[0]
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

//Get polynomial from Fr
fn get_poly_from_fr(val:Fr)->DensePolynomial<Fr>{
    DensePolynomial::from_coefficients_vec(vec![val])
}

// z(wx)
fn compute_shifted_polynomial(poly_z: &DensePolynomial<Fr>,w: &Fr) -> DensePolynomial<Fr> {
    // Get the coefficients of z(x)
    let z_coeffs = poly_z.coeffs();

    // Create a vector to store the new coefficients
    let mut zw_coeffs = Vec::with_capacity(z_coeffs.len());

    // Initialize w_power to w^0 = 1
    let mut w_power = Fr::from(1);

    // Iterate through the coefficients of z(x)
    for coeff in z_coeffs {
        // The new coefficient for the term x^i is z_i * w^i
        let new_coeff = coeff * &w_power;
        zw_coeffs.push(new_coeff);

        // // Update w_power for the next iteration (w^(i+1))
        w_power *= w;
    }

    // Create and return the new DensePolynomial
    DensePolynomial::from_coefficients_vec(zw_coeffs)
}

// x^n for any n
fn get_x_n_poly(n:usize)->DensePolynomial<Fr>{

    let mut coefficients:Vec<Fr> = Vec::new();
    for i in 0..=n{
        if i == n{
            coefficients.push(Fr::from(1));
        }else{
            coefficients.push(Fr::from(0));
        }
    }
    DensePolynomial::from_coefficients_vec(coefficients)
}

// Takes a polynomial's coeffecient and only keeps the range values
fn split_polynomial(poly:&DensePolynomial<Fr>,start:usize,end:usize)->DensePolynomial<Fr>{
    let mut coeffs:Vec<Fr> = poly.coeffs().to_vec();
    for i in 0..coeffs.len(){
        if i >= start && i <= end{
            continue;
        }else{
            coeffs[i] = Fr::from(0);
        }

    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

// Get G1 element from ProofElement 
fn get_g1_element(element:&ProofElement)->G1{
    let commitment = if let ProofElement::Group(g1_element) = element {
        g1_element.clone()
    }else {
        panic!("Expected a G1 element");
    };
    commitment
}

// Get Fr element from ProofElement 
fn get_fr_element(element:&ProofElement)->Fr{
    let opening = if let ProofElement::Field(fr_element) = element {
        fr_element.clone()
    }else {
        panic!("Expected a Fr element");
    };
    opening
}

//Generate proof string
fn generate_proof_string(proof:Vec<ProofElement>)->String{
    let mut proof_binary:Vec<u8> = Vec::new();
    for (i,p) in proof.iter().enumerate(){

        //For G1 elements
        if i >=0 && i <= 8{

            let _element:G1 = get_g1_element(&p);
            let(element_x,element_y,element_z) = (_element.x,_element.y,_element.z);

            let mut serialized_data_x = Vec::new();
            let mut serialized_data_y = Vec::new();
            let mut serialized_data_z = Vec::new();

            element_x.serialize_uncompressed(&mut serialized_data_x);
            element_y.serialize_uncompressed(&mut serialized_data_y);
            element_z.serialize_uncompressed(&mut serialized_data_z);

            let x_len: Vec<u8> = vec![serialized_data_x.len() as u8];
            let y_len: Vec<u8> = vec![serialized_data_y.len() as u8];
            let z_len: Vec<u8> = vec![serialized_data_z.len() as u8];

            proof_binary.extend(x_len);
            proof_binary.extend(serialized_data_x);
            proof_binary.extend(y_len);
            proof_binary.extend(serialized_data_y);
            proof_binary.extend(z_len);
            proof_binary.extend(serialized_data_z);    
        }else{
            // For Fr element
            let element:Fr = get_fr_element(&p);
            let mut serialized_data = Vec::new();
            element.serialize_uncompressed(&mut serialized_data);
            let data_len: Vec<u8> = vec![serialized_data.len() as u8];
            proof_binary.extend(data_len);
            proof_binary.extend(serialized_data); 
        }
    }

    let proof_string = general_purpose::STANDARD.encode(proof_binary.clone());
    proof_string
    
}

// Parse proof string
fn parse_proof(proof:&str) -> Vec<ProofElement>{
    let proof_binary:Vec<u8> =  general_purpose::STANDARD.decode(proof).expect("Invalid proof !!");
    let mut cursor = Cursor::new(&proof_binary[..]);
    let mut iteration_no = 0;
    let mut deserialized_proof:Vec<ProofElement> = Vec::new();

    //Deserialize proof elements
    while (cursor.position() as usize) < cursor.get_ref().len(){ 
        // G1 elements
        if iteration_no < 9 {

            //Read the length
            let mut element_len =[0u8];

            cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read x length
            let mut x_element: Vec<u8> = vec![0u8;element_len[0] as usize];
            cursor.read_exact(&mut x_element).expect("Invalid proof !!"); //Read x 

            cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read y length
            let mut y_element: Vec<u8> = vec![0u8;element_len[0] as usize];
            cursor.read_exact(&mut y_element).expect("Invalid proof !!"); //Read y 

            cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read z length
            let mut z_element: Vec<u8> = vec![0u8;element_len[0] as usize];
            cursor.read_exact(&mut z_element).expect("Invalid proof !!"); //Read z

            //Deseralize
            let mut cursorx = Cursor::new(x_element);
            let mut cursory = Cursor::new(y_element);
            let mut cursorz = Cursor::new(z_element);

            //G1 elements
            let deserialized_x:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorx).expect("Invalid proof !!");
            let deserialized_y:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursory).expect("Invalid proof !!");
            let deserialized_z:Fp<MontBackend<FqConfig,4>,4> = Fp::deserialize_uncompressed(&mut cursorz).expect("Invalid proof !!");
    
            let element:G1 = G1::new_unchecked(deserialized_x, deserialized_y, deserialized_z); //Note only unchecked returns projective representation, since we construct from already existing group we can ignore the check
            deserialized_proof.push(ProofElement::Group(element)); //Push the element
            
        }else {
            // Fr elements

            //Read the length
            let mut element_len =[0u8];
            cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read element length
            let mut element: Vec<u8> = vec![0u8;element_len[0] as usize];
            cursor.read_exact(&mut element).expect("Invalid proof !!"); //Read element

            //Deseralize
            let mut cursor_element = Cursor::new(element);
            let deserialized_element:Fr = Fp::deserialize_uncompressed(&mut cursor_element).expect("Invalid proof !!");
            deserialized_proof.push(ProofElement::Field(deserialized_element)); //Push the element
        }

        iteration_no = iteration_no+1;

    }

    deserialized_proof
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
    let (srs,srs_two):(Vec<G1>,Vec<G2>) = load_srs_from_file("./kzg_srs.zkey").expect("Failed to load");

    let mut a_commitment:G1 = compute_commitment(&srs,a_poly.clone());
    let mut b_commitment:G1 = compute_commitment(&srs,b_poly.clone());
    let mut c_commitment:G1 = compute_commitment(&srs,c_poly.clone());

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
    // println!("OPERANDLIST: {:?}",&operand_list);
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

    let permutation_poly_sigma_1:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_y.clone());
    let permutation_poly_sigma_2:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_k1_y.clone());
    let permutation_poly_sigma_3:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permuted_root_unity_k2_y.clone());

    // println!("Sigma1 :{:?}",permutation_poly_sigma_1);
    // println!("Sigma2 :{:?}",permutation_poly_sigma_2);
    // println!("Sigma3 :{:?}",permutation_poly_sigma_3);
    // println!("->>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
    // println!("EVALUATION DOMAIN: {:?}",&evaluation_domain);
    // println!("------------------------------------------------------------------------------");
    // println!("EVALUATION DOMAIN(K1): {:?}",&eval_domain_h_k1);
    // println!("------------------------------------------------------------------------------");
    // println!("EVALUATION DOMAIN(K2): {:?}",&eval_domain_h_k2);
    // println!("------------------------------------------------------------------------------");
    // println!("permuted_root_unity_y: {:?}",&permuted_root_unity_y);
    // println!("------------------------------------------------------------------------------");
    // println!("permuted_root_unity_k1_y: {:?}",&permuted_root_unity_k1_y);
    // println!("------------------------------------------------------------------------------");
    // println!("permuted_root_unity_k2_y: {:?}",&permuted_root_unity_k2_y);
    // println!("->>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");



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

    let mut domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("bn254-plonk"),
        transcript_final.len(),
        "full_transcript",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        2,               // number of scalars for the challenge
        "Round 1 challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as GroupDomainSeparator<G1>>::add_points(
        domsep,
        1,
        "Round 2",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Round 3 challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as GroupDomainSeparator<G1>>::add_points(
        domsep,
        3,
        "Round 3",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Round 4 challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::add_scalars(
        domsep,
        6,
        "Round 4",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Round 4 challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as GroupDomainSeparator<G1>>::add_points(
        domsep,
        9,
        "Round 5",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<Fr>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Verifier challenge",         // label for the challenge
    );


    let mut prover_state = domsep.to_prover_state();
  
    // Add transcript
    prover_state.add_scalars(&transcript_final).expect("Fiat shamir error!! Scalar addition failed");  
    

    //Round 2 (Generate challenges)  
    // Generate challenge for beta and gamma
    let [beta,gamma]: [Fr; 2] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    //Compute permutation polynomial accumulations
    // let mut permutation_poly_y:Vec<Fr> = vec![Fr::from(1)]; // Set z(w^0) = 1 [evals for interpolating permutation poly]
    let mut permutation_poly_y:Vec<Fr> = vec![Fr::from(1)]; // Set z(w^0) = 1 [evals for interpolating permutation poly]

    //Clever optimization from plonk paper on grandproduct argument
    for i in 0..circuit_size-1{
        let mut cumulative_product:Fr = Fr::from(1);
        for j in 0..=i{
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
    let z_poly_half:DensePolynomial<Fr> = lagrange_interpolation(&evaluation_domain,permutation_poly_y.clone()); // (w^0,1),(w,y1)...

    let l_basis_0:DensePolynomial<Fr> = compute_lagrange_basis(0,&evaluation_domain);
    // (b7x^2+ b8x+ b9)Zh(x) + z'(x)
    let z_permutation_poly = DensePolynomial::from_coefficients_vec(vec![Fr::from(random_scalars_b[8]),Fr::from(random_scalars_b[7]),Fr::from(random_scalars_b[6])]) * &z_h_poly + z_poly_half;
    let z_commitment:G1 = compute_commitment(&srs,z_permutation_poly.clone());

    //Push commitment to transcript
    prover_state.add_points(&[z_commitment]).expect("Fiat shamir error!! Group element addition failed");  


    // Round 3
    //(Generate challenge for quotient polynomial)
    let [alpha]: [Fr; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    let x_poly:DensePolynomial<Fr> = DensePolynomial::from_coefficients_vec(vec![Fr::from(0), Fr::from(1)]); // x
    let f_x:DensePolynomial<Fr> = (&a_poly+&x_poly*beta+get_poly_from_fr(gamma))* (&b_poly+&x_poly*(k1_k2[0]*beta)+get_poly_from_fr(gamma))* (&c_poly+&x_poly*(k1_k2[1]*beta)+get_poly_from_fr(gamma));
    let g_x:DensePolynomial<Fr> = (&a_poly+&permutation_poly_sigma_1*beta+get_poly_from_fr(gamma))* (&b_poly+&permutation_poly_sigma_2*beta+get_poly_from_fr(gamma))* (&c_poly+&permutation_poly_sigma_3*beta+get_poly_from_fr(gamma));
    let z_permutation_poly_wx:DensePolynomial<Fr> = compute_shifted_polynomial(&z_permutation_poly,&evaluation_domain[1]); // z(wx)

    //Compute random scalar for this round
    let random_scalars_r3:Vec<Fr> = sample_random_scalars(2); // b10,b11

    // Compute t1(x),t2(x),t3(x)
    assert!(z_permutation_poly.clone().evaluate(&evaluation_domain[1]) == z_permutation_poly_wx.clone().evaluate(&evaluation_domain[0]) );

    let t_one_poly:DensePolynomial<Fr> = (&a_poly*&ql_poly + &b_poly*&qr_poly + &c_poly*&qo_poly + &a_poly*&b_poly*&qm_poly + &qc_poly);
    let t_two_poly:DensePolynomial<Fr> = ((&f_x * &z_permutation_poly) - (&g_x * &z_permutation_poly_wx));
    let t_three_poly:DensePolynomial<Fr> = ((&z_permutation_poly - DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]))*&l_basis_0);
    let t_quotient_poly:DensePolynomial<Fr> = (&t_one_poly + &t_two_poly*alpha + &t_three_poly*alpha*alpha)/&z_h_poly;

    // Split t(x) into tlow (n-1) , thigh (n-1), tmid (n+5)

    // Compute polynomials
    let x_n_poly:DensePolynomial<Fr> = get_x_n_poly(circuit_size); // x^n
    let x_2n_poly:DensePolynomial<Fr> = get_x_n_poly(2*circuit_size);// x^2n

    let t_low_poly_prime:DensePolynomial<Fr> = split_polynomial(&t_quotient_poly,0,circuit_size-1);
    let t_mid_poly_prime:DensePolynomial<Fr> = (split_polynomial(&t_quotient_poly,circuit_size,2*circuit_size-1))/&x_n_poly;
    let t_high_poly_prime:DensePolynomial<Fr> = (split_polynomial(&t_quotient_poly,2*circuit_size,3*circuit_size+5))/&x_2n_poly;

    //Compute final polynomial
    let t_quotient_poly_final:DensePolynomial<Fr> = &t_low_poly_prime + &x_n_poly*&t_mid_poly_prime + &x_2n_poly*&t_high_poly_prime;

    //Get random scalars
    let b10:Fr = random_scalars_r3[0];
    let b11:Fr = random_scalars_r3[1];

    //Divide mid and high to get lower degrees for commitment and commit scalars
    let t_low_poly = &t_low_poly_prime + &x_n_poly*b10; //t'low(x) + x^n*b10 
    let t_mid_poly = &t_mid_poly_prime - get_poly_from_fr(b10) + &x_n_poly*b11; // t'mid(x) - b10 + x^n *b11
    let t_high_poly = &t_high_poly_prime - get_poly_from_fr(b11); // t'high(x) - b11

    //Compute commitment
    let t_low_commitment:G1 = compute_commitment(&srs,t_low_poly.clone());
    let t_mid_commitment:G1 = compute_commitment(&srs,t_mid_poly.clone());
    let t_high_commitment:G1 = compute_commitment(&srs,t_high_poly.clone());

    //Add commitment to fiat shamir state
    prover_state.add_points(&[t_low_commitment,t_mid_commitment,t_high_commitment]).expect("Fiat shamir error!! Group element addition failed");  


    // (ROUND 4)
    // Get the challenge
    let [z_challenge]: [Fr; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");

    //Compute openings
    let a_opening:Fr = a_poly.evaluate(&z_challenge);
    let b_opening:Fr = b_poly.evaluate(&z_challenge);
    let c_opening:Fr = c_poly.evaluate(&z_challenge);
    let z_w_opening:Fr = z_permutation_poly_wx.evaluate(&z_challenge);
    let sigma_1_opening:Fr = permutation_poly_sigma_1.evaluate(&z_challenge);
    let sigma_2_opening:Fr = permutation_poly_sigma_2.evaluate(&z_challenge);

    //Add commitment to fiat shamir state
    prover_state.add_scalars(&[a_opening,b_opening,c_opening,z_w_opening,sigma_1_opening,sigma_2_opening]).expect("Fiat shamir error!! Group element addition failed");  

    // (Round 5)
    // Get the challenge
    let [v_challenge]: [Fr; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");

    // Construct lineararization polynomial r(x)
    let linearization_poly_r:DensePolynomial<Fr> = 
        (&qm_poly*a_opening*b_opening + &ql_poly*a_opening + &qr_poly*b_opening + &qo_poly*c_opening + &qc_poly) 
        + get_poly_from_fr(alpha) * ( &z_permutation_poly*(a_opening + beta*z_challenge + gamma)* (b_opening + beta*k1_k2[0]*z_challenge + gamma)* (c_opening + beta*k1_k2[1]*z_challenge + gamma) - (&(get_poly_from_fr(c_opening)+&permutation_poly_sigma_3*beta+get_poly_from_fr(gamma)) * z_w_opening * (a_opening+beta*sigma_1_opening+gamma) * (b_opening+beta*sigma_2_opening+gamma)))
        + (&(&z_permutation_poly - get_poly_from_fr(Fr::from(1))) * l_basis_0.evaluate(&z_challenge) * alpha*alpha) 
        - (&(&t_low_poly + &t_mid_poly*x_n_poly.evaluate(&z_challenge) + &t_high_poly *x_2n_poly.evaluate(&z_challenge)) * z_h_poly.evaluate(&z_challenge));


    println!("Linearization poly eval at z: {:?}",linearization_poly_r.evaluate(&z_challenge));

    // Construct opening proof polynomial
    let w_opening_z_poly:DensePolynomial<Fr> = (&linearization_poly_r  // r(x)
                                             + &(&a_poly - get_poly_from_fr(a_opening))*v_challenge // (a(x)-a_opening)*v
                                             + &(&b_poly - get_poly_from_fr(b_opening))*v_challenge*v_challenge // (b(x)-b_opening)*v^2
                                             + &(&c_poly - get_poly_from_fr(c_opening))*v_challenge*v_challenge*v_challenge // (c(x)-c_opening)*v^3
                                             + &(&permutation_poly_sigma_1 - get_poly_from_fr(sigma_1_opening))*v_challenge*v_challenge*v_challenge*v_challenge // (Sigma1(x)-sigma1_opening)*v^4
                                             + &(&permutation_poly_sigma_2 - get_poly_from_fr(sigma_2_opening))*v_challenge*v_challenge*v_challenge*v_challenge*v_challenge) // (Sigma2(x)-sigma2_opening)*v^5
                                             / (DensePolynomial::from_coefficients_vec(vec![Fr::from(-z_challenge),Fr::from(1)])); // (x-z_challenge)   

    let w_opening_zw_poly:DensePolynomial<Fr> = (z_permutation_poly - get_poly_from_fr(z_w_opening)) //(z(x) - z_w_opening)/(x-z_challenge*w)
                                              / ((DensePolynomial::from_coefficients_vec(vec![Fr::from(-(z_challenge*&evaluation_domain[1])),Fr::from(1)])));


    //Compute commitments
    let w_opening_z_commitment:G1 = compute_commitment(&srs,w_opening_z_poly);
    let w_opening_zw_commitment:G1 = compute_commitment(&srs,w_opening_zw_poly);

    let proof:Vec<ProofElement> = vec![
        ProofElement::Group(a_commitment),
        ProofElement::Group(b_commitment),
        ProofElement::Group(c_commitment),
        ProofElement::Group(z_commitment),
        ProofElement::Group(t_low_commitment),
        ProofElement::Group(t_mid_commitment),
        ProofElement::Group(t_high_commitment),
        ProofElement::Group(w_opening_z_commitment),
        ProofElement::Group(w_opening_zw_commitment),
        ProofElement::Field(a_opening),
        ProofElement::Field(b_opening),
        ProofElement::Field(c_opening),
        ProofElement::Field(z_w_opening),
        ProofElement::Field(sigma_1_opening),
        ProofElement::Field(sigma_2_opening)
    ];

    // Add proof for fiat shamir
    prover_state.add_points(&[a_commitment,b_commitment,c_commitment,z_commitment,t_low_commitment,t_mid_commitment,t_high_commitment,w_opening_z_commitment,w_opening_zw_commitment]).expect("Fiat shamir error!! Group element addition failed");  

    // Convert proof to string
    let proof_string = generate_proof_string(proof.clone());
    println!("Proof:{:?}",proof_string);

    //Verifier

    // Convert the proof string back to list of ProofElement
    let proof_vr:Vec<ProofElement> = parse_proof(&proof_string);

    //1. Validate proof elements
    for (i,element) in proof_vr.iter().enumerate(){
        match *element { 
            ProofElement::Group(G1) => {if i >8 {panic!("Invalid proof!!: Proof has more than 9 commitment");}},
            ProofElement::Field(Fr) => {if i <= 8 {panic!("Invalid proof!!: Parsing proof failed");}},
            _ => {panic!("Invalid proof!!: Cannot parse the proof")}
        }

    }

    //Retrieve proof elements
    let a_commitment_:G1 = get_g1_element(&proof_vr[0]); 
    let b_commitment_:G1 = get_g1_element(&proof_vr[1]); 
    let c_commitment_:G1 = get_g1_element(&proof_vr[2]); 
    let z_commitment_:G1 = get_g1_element(&proof_vr[3]); 
    let t_low_commitment_:G1 = get_g1_element(&proof_vr[4]); 
    let t_mid_commitment_:G1 = get_g1_element(&proof_vr[5]); 
    let t_high_commitment_:G1 = get_g1_element(&proof_vr[6]); 
    let w_opening_z_commitment_:G1 = get_g1_element(&proof_vr[7]); 
    let w_opening_zw_commitment_:G1 = get_g1_element(&proof_vr[8]);

    let a_opening_:Fr = get_fr_element(&proof_vr[9]);
    let b_opening_:Fr = get_fr_element(&proof_vr[10]);
    let c_opening_:Fr = get_fr_element(&proof_vr[11]);
    let z_w_opening_:Fr = get_fr_element(&proof_vr[12]);
    let sigma_1_opening_:Fr = get_fr_element(&proof_vr[13]);
    let sigma_2_opening_:Fr = get_fr_element(&proof_vr[14]);

    //Compute necessary commitments
    let qm_commitment_:G1 = compute_commitment(&srs,qm_poly);
    let ql_commitment_:G1 = compute_commitment(&srs,ql_poly);
    let qr_commitment_:G1 = compute_commitment(&srs,qr_poly);
    let qo_commitment_:G1 = compute_commitment(&srs,qo_poly);
    let qc_commitment_:G1 = compute_commitment(&srs,qc_poly);
    let sigma_1_commitment_:G1 = compute_commitment(&srs,permutation_poly_sigma_1);
    let sigma_2_commitment_:G1 = compute_commitment(&srs,permutation_poly_sigma_2);
    let sigma_3_commitment_:G1 = compute_commitment(&srs,permutation_poly_sigma_3);
    let x_commitment_g2_:G2 = compute_commitment_g2(&srs_two,x_poly.clone());
    let one_g2_commitment:G2 = compute_commitment_g2(&srs_two,get_poly_from_fr(Fr::from(1)));

    let alpha_ = alpha;
    let beta_ = beta;
    let gamma_ = gamma;
    let z_challenge_ = z_challenge;
    let v_challenge_ = v_challenge;
    let k1_ = k1_k2[0];
    let k2_ = k1_k2[1];

    let l_basis_0_eval_:Fr = l_basis_0.evaluate(&z_challenge_);
    let z_h_poly_ = z_h_poly;

    //Compute new challenge for batching
    let [u_challenge]: [Fr; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");

    let g_0:G1 = compute_commitment_fr_g1(&srs,Fr::from(1));

    // Compute linearization commitment [r]1

    let linearlization_commitment_:G1 = (qm_commitment_*a_opening_*b_opening_ +ql_commitment_*a_opening_ +qr_commitment_*b_opening_ + qo_commitment_*c_opening_ + qc_commitment_)
                                     + ( (z_commitment_*(a_opening_+beta_*z_challenge_+gamma_)*(b_opening_+beta_*z_challenge_*k1_+gamma_)*(c_opening_+beta_*z_challenge_*k2_+gamma_) )
                                     - ( (sigma_3_commitment_*beta_+compute_commitment_fr_g1(&srs,c_opening_+gamma_))*(a_opening_+beta*sigma_1_opening_+gamma_)* (b_opening_+beta*sigma_2_opening_+gamma_)*z_w_opening_))*alpha_
                                     + ((z_commitment_ - compute_commitment_fr_g1(&srs,Fr::from(1)))*l_basis_0_eval_*alpha_*alpha_)
                                     - ((t_low_commitment_ + t_mid_commitment_*x_n_poly.evaluate(&z_challenge_) + t_high_commitment_*x_2n_poly.evaluate(&z_challenge_))*z_h_poly_.evaluate(&z_challenge));

    let f_commitment_:G1 = linearlization_commitment_ 
                         + (a_commitment_- compute_commitment_fr_g1(&srs,a_opening_))*v_challenge 
                         + (b_commitment_- compute_commitment_fr_g1(&srs,b_opening_))*v_challenge*v_challenge
                         + (c_commitment_- compute_commitment_fr_g1(&srs,c_opening_))*v_challenge*v_challenge*v_challenge
                         + (sigma_1_commitment_- compute_commitment_fr_g1(&srs,sigma_1_opening_))*v_challenge*v_challenge*v_challenge*v_challenge
                         + (sigma_2_commitment_- compute_commitment_fr_g1(&srs,sigma_2_opening_))*v_challenge*v_challenge*v_challenge*v_challenge*v_challenge;

    let e_commitment_:G1 = z_commitment_ - compute_commitment_fr_g1(&srs,z_w_opening_);

    // Batch evaluation check
    let left_pairing_part = Bn254::pairing(w_opening_z_commitment_+w_opening_zw_commitment_*u_challenge,x_commitment_g2_);
    let right_pairing_part = Bn254::pairing(w_opening_z_commitment_*z_challenge_ +w_opening_zw_commitment_*u_challenge*z_challenge_*evaluation_domain[1]+f_commitment_+e_commitment_*u_challenge,one_g2_commitment);

    assert_eq!(left_pairing_part,right_pairing_part);

    println!("Proof verified!!");
}

