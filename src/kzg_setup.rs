use std::env;
use ark_bn254::{Bn254,FqConfig,Fq2Config,FrConfig,Fr,G1Projective as G1, G2Projective as G2};
use ark_ff::{Fp,Fp2, MontBackend,QuadExtField,Fp2ConfigWrapper,Zero};
use ark_ec::PrimeGroup; // Import the trait  
use ark_std::UniformRand;  
use rand::rngs::OsRng; 
use ark_serialize::CanonicalSerialize;
use ark_serialize::Write;
use ark_serialize::CanonicalDeserialize;
use std::fs::File;
use std::io::{Result,Read,Cursor};

use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

#[derive(Debug)]
enum KeyElement{
    GroupOne(G1),
    GroupTwo(G2)
}

// Retrieve G1 from Key Element
fn get_g1_element(element:&KeyElement)->G1{
    let commitment = if let KeyElement::GroupOne(g1_element) = element {
        g1_element.clone()
    }else {
        panic!("Expected a G1 element");
    };
    commitment
}
// Retrieve G2 from Key Element
fn get_g2_element(element:&KeyElement)->G2{
    let commitment = if let KeyElement::GroupTwo(g2_element) = element {
        g2_element.clone()
    }else {
        panic!("Expected a G2 element");
    };
    commitment
}

// Hash string to u64
fn hash_to_u64(s: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}

//Compute pow(tau,n)
fn compute_powers_of_tau(tau:Fr,n:i32)-> Fr{
    let mut element:Fr = Fr::from(1u8);
    if n == 0{
        element = Fr::from(1u8);
    }else{
        for _ in 0..n{
            element = element*tau;
        }
    }
    element

}

//Compute SRS (Structured reference string)
fn compute_srs(generator_one:G1,generator_two:G2,tau:Fr,circuit_size:i32) -> Vec<KeyElement>{
    let mut elements:Vec<KeyElement> = Vec::new();

    // For group2 {g^0,g^1} 
    for i in 0..=1{
        let ptau:Fr = compute_powers_of_tau(tau,i);
        elements.push(KeyElement::GroupTwo(generator_two * ptau));
    }

    // {w^0,...,w^(n+5)}
    for i in 0..=circuit_size+5{
        let ptau:Fr = compute_powers_of_tau(tau,i);
        elements.push(KeyElement::GroupOne(generator_one * ptau));

    }
    elements // First two is in G2 and rest in G1
}

// Combine srs two and one
fn combine_srs(srs_one:Vec<G1>,srs_two:Vec<G2>)->Vec<KeyElement>{
    let mut elements:Vec<KeyElement> = Vec::new();

    //Push srs_two first
    for e in srs_two{
        elements.push(KeyElement::GroupTwo(e));
    }

    //Push srs_one first
    for e in srs_one{
        elements.push(KeyElement::GroupOne(e));
    }
    elements
}

//Save the SRS to binary file
fn save_srs_to_file(srs:Vec<KeyElement>,file_name:&str) -> Result<()>{
    let mut file = File::create(file_name).unwrap();
    for (i,element) in srs.iter().enumerate(){
        //G2 element 
        if i == 0 || i == 1{
            let _element:G2 = get_g2_element(&element);
            let(element_x,element_y,element_z) = (_element.x,_element.y,_element.z);

            let mut serialized_data_x = Vec::new();
            let mut serialized_data_y = Vec::new();
            let mut serialized_data_z = Vec::new();

            let _ = element_x.serialize_uncompressed(&mut serialized_data_x);
            let _ = element_y.serialize_uncompressed(&mut serialized_data_y);
            let _ = element_z.serialize_uncompressed(&mut serialized_data_z);

            let x_len: Vec<u8> = vec![serialized_data_x.len() as u8];
            let y_len: Vec<u8> = vec![serialized_data_y.len() as u8];
            let z_len: Vec<u8> = vec![serialized_data_z.len() as u8];

            file.write_all(&x_len).unwrap();
            file.write_all(&mut serialized_data_x).unwrap();

            file.write_all(&y_len).unwrap();
            file.write_all(&mut serialized_data_y).unwrap();

            file.write_all(&z_len).unwrap();
            file.write_all(&mut serialized_data_z).unwrap();
        }else{
            let _element:G1 = get_g1_element(&element);
            let(element_x,element_y,element_z) = (_element.x,_element.y,_element.z);

            let mut serialized_data_x = Vec::new();
            let mut serialized_data_y = Vec::new();
            let mut serialized_data_z = Vec::new();

            let _ = element_x.serialize_uncompressed(&mut serialized_data_x);
            let _ = element_y.serialize_uncompressed(&mut serialized_data_y);
            let _ = element_z.serialize_uncompressed(&mut serialized_data_z);

            let x_len: Vec<u8> = vec![serialized_data_x.len() as u8];
            let y_len: Vec<u8> = vec![serialized_data_y.len() as u8];
            let z_len: Vec<u8> = vec![serialized_data_z.len() as u8];

            file.write_all(&x_len).unwrap();
            file.write_all(&mut serialized_data_x).unwrap();

            file.write_all(&y_len).unwrap();
            file.write_all(&mut serialized_data_y).unwrap();

            file.write_all(&z_len).unwrap();
            file.write_all(&mut serialized_data_z).unwrap();

        }
    }

    Ok(())
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
fn main(){
    let args:Vec<String> = env::args().collect();
    let mut rng = OsRng;
    let g1 = G1::generator(); //Generator on the curve
    let g2 = G2::generator(); //Generator on the curve G2projective

    if args.len() == 1{
        panic!("No mode specified!!")
    }
    
    //Check cli args
    if args[1] == String::from("create-ceremony"){
        if args.len() == 2 {
            panic!("No circuit size specified");
        }else{
            println!("Args: {:?}",args);
            let circuit_size:i32 = args[2].parse().expect("Not a valid number"); //Upper bound on degree of the committed polynomial (d)

            //Create random powers of tau for kzg
            let tau = Fr::rand(&mut rng);

            let srs:Vec<KeyElement> = compute_srs(g1,g2,tau,circuit_size);         
            // println!("SRS: {:?}",srs);

            //Save the KZG srs in binary file
            save_srs_to_file(srs,"kzg_srs.zkey").unwrap();

            println!("Key generated succesfully!!");
        }
    }else if args[1] == String::from("contribute-randomness"){
        if args[2].is_empty(){
            panic!("No randomness found");
        }else{
            let randomess:String = args[2].clone();
            let hash_u64 = hash_to_u64(&randomess.to_string());
            let randomness_num_fr = Fr::from(hash_u64);

            //Fetch SRS
            let (mut srs_one,mut srs_two):(Vec<G1>,Vec<G2>) = load_srs_from_file("./kzg_srs.zkey").unwrap();

            //Modify SRS_one with randomness
            for (index,element) in srs_one.clone().iter().enumerate(){
                // let val = *element.clone();
                srs_one[index] = *element * randomness_num_fr;
            }
            //Modify SRS_two with randomness
            for (index,element) in srs_two.clone().iter().enumerate(){
                // let val = *element.clone();
                srs_two[index] = *element * randomness_num_fr;
            }

            // Combine srs
            let updated_srs:Vec<KeyElement> = combine_srs(srs_one,srs_two);

            //Overwrite SRS
            save_srs_to_file(updated_srs,"kzg_srs.zkey");

            println!("Randomness added succesfully!!");

        }

    }else {
        panic!("Invalid argument!!");
    }
    println!("Argument : {:?}",args);

}