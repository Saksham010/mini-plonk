use std::env;
use ark_bn254::{Fr,G1Projective as G, G2Projective as G2};
use rand::rngs::OsRng; 

//Compute pow(tau,n)
fn compute_powers_of_tau(tau:Fr,n:i32)-> Fr{
    let mut element:Fr = Fr::from(1u8);
    if n == 0{
        element = Fr::from(1u8);
    }else{
        for i in 0..n{
            element = element*tau;
        }
    }
    element

}

//Compute SRS (Structured reference string)
fn compute_srs(generator:G1Projective,tau:Fr,circuit_size:i32) -> Vec<G1Projective>{
    let mut elements:Vec<G1Projective> = Vec::new();
    for i in 0..circuit_size{
        let ptau:Fr = compute_powers_of_tau(tau,i);
        elements.push(g * ptau);

    }
    elements
}

fn main(){
    let args:Vec<String> = env::args().collect();
    let mut rng = OsRng;
    let g1 = G::generator(); //Generator on the curve
    // let g2 = G2::generator(); //Generator on the curve G2projective
    
    //Check cli args
    if args[1] == String::from("create-ceremony"){
        if args[2].is_empty() {
            panic!("No circuit size specified");
        }else{
            let circuit_size:i32 = args[2].parse().expect("Not a valid number");

            //Create random powers of tau for kzg
            let tau = Fr::rand(&mut rng);
            let srs:Vec<G1Projective> = compute_srs(g1,tau,circuit_size);
            println!("SRS: {:?}",srs);

        }
    }else if args[1] == String::from("contribute-randomness"){
        if args[2].is_empty(){
            panic!("No randomness found");
        }else{
            let randomess:String = args[2];
        }

    }
    println!("Argument : {:?}",args);

}