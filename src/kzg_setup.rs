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
fn compute_srs(generator:G1,tau:Fr,circuit_size:i32) -> Vec<G1>{
    let mut elements:Vec<G1> = Vec::new();
    // {w^0,...,w^(n+5)}
    for i in 0..=circuit_size+5{
        let ptau:Fr = compute_powers_of_tau(tau,i);
        println!("PTAU: {:?}",&ptau);
        println!("G_PTAU: {:?}",generator*ptau);
        elements.push(generator * ptau);

    }
    elements
}

//Save the SRS to binary file
fn save_srs_to_file(srs:Vec<G1>,file_name:&str) -> Result<()>{
    let mut file = File::create(file_name).unwrap();
    for element in srs{
        let(element_x,element_y,element_z) = (element.x,element.y,element.z);

        let mut serialized_data_x = Vec::new();
        let mut serialized_data_y = Vec::new();
        let mut serialized_data_z = Vec::new();

        element_x.serialize_uncompressed(&mut serialized_data_x);
        element_y.serialize_uncompressed(&mut serialized_data_y);
        element_z.serialize_uncompressed(&mut serialized_data_z);

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

    Ok(())
}

// Load SRS
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
fn main(){
    let args:Vec<String> = env::args().collect();
    let mut rng = OsRng;
    let g1 = G1::generator(); //Generator on the curve
    // let g2 = G2::generator(); //Generator on the curve G2projective

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
            let srs:Vec<G1> = compute_srs(g1,tau,circuit_size);
            println!("SRS: {:?}",srs);

            //Save the KZG srs in binary file
            save_srs_to_file(srs,"kzg_srs.zkey").unwrap();
        }
    }else if args[1] == String::from("contribute-randomness"){
        if args[2].is_empty(){
            panic!("No randomness found");
        }else{
            let randomess:String = args[2].clone();
            let hash_u64 = hash_to_u64(&randomess.to_string());
            let randomness_num_fr = Fr::from(hash_u64);

            //Fetch SRS
            let mut srs:Vec<G1> = load_srs_from_file("./kzg_srs.zkey").unwrap();

            //Modify SRS with randomness
            for (index,element) in srs.clone().iter().enumerate(){
                // let val = *element.clone();
                srs[index] = *element * randomness_num_fr;
            }

            //Overwrite SRS
            save_srs_to_file(srs,"kzg_srs.zkey");
        }

    }else {
        panic!("Invalid argument!!");
    }
    println!("Argument : {:?}",args);

}