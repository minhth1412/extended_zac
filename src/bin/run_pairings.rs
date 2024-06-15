extern crate pairing_plus as pairing;
extern crate pointproofs;
extern crate plum;
extern crate rand;
extern crate itertools;
use pairing::serdes::SerDes;
use pointproofs::pairings::param::paramgen_from_seed;
use pointproofs::pairings::*;
use plum::StandardBloomFilter;
use itertools::Itertools;
use rand::Rng;

//read file line by line
//use std::fs::File;
//use std::io::{self, BufRead};
//use std::path::Path;

//read csv
//extern crate csv;
//use csv::Error;

//use std::env;
//use std::error::Error;
//use std::ffi::OsString;
//use std::fs::File;
//use std::process;

fn setcommit(
	prover_params: &ProverParams,
	values: Vec<String>,
	bloom: &mut plum::StandardBloomFilter<str>
	)-> (Vec<Vec<u8>>,Commitment) {
    for i in 0..values.len() {
    	println!("Item value: {}.", values[i]);
     	bloom.insert(&values[i]);
    }
		
	println!("Bloom vector size: {}",bloom.optimal_m);	    
	println!("Bloom vector: {:?}",bloom.bitmap);
	let mut init_values: Vec<Vec<u8>> = Vec::with_capacity(bloom.optimal_m);
	for i in 0..bloom.optimal_m {
    	let x = bloom.bitmap[i] as i32;
    	let y = format!("{}", x);
	    let v = y.into_bytes();
	    // println!( "{:#?}", v );
	    init_values.push(v);
	}
    // println!( "init values  {:?}", init_values );
    // generate the commitment, and (de)serialize it
    let com = Commitment::new(&prover_params, &init_values).unwrap();
   	
   	return (init_values,com);
}

// Create function ZKEDB.CommitDB to create a commitment for a set of items, input includes the set_id, n and pp (public parameters)
// and the output is the commitment of the set of items - cm
// Pseudo code:
// cm ← ZKEDB.CommitDB( D, r, pp)
    // 1: for i ← 1 to N do
    // 2:   Di ← {x ∈ K : D(x) = i}
    // 3:   if Di ̸ = ∅ then
    // 4:       Ci ← ZAC.Com( Di ∪ | Di|, r, pp) ▷ Assuming that | Di| ̸ ∈ K
    // 5:   else
    // 6:       ri ←$- {0, 1}∗ where ri ̸ ∈ K
    // 7:       Ci ← ZAC.Com({0, ri}, r, pp) ▷ Assuming that 0 ̸ ∈ K
    // 8: CN +1 ← ZAC.Com(K, r, pp)
    // 9: cm ← {C1, . . . , CN , CN +1}

fn create_commit (
    set_id: Vec<String>,        /* A set of data keys */
    db: &std::collections::HashMap<String, u32>,    /* A hashmap that contains the key-value pairs */
    d: &mut Vec<Vec<String>>,        /* A vector, contains the sub-vector of keys that have the same value as index */
    prover_params: &ProverParams,       /* A set including prover parameters for values from 1 to n (n is right below)*/
    n: u32,
    bloom: &mut plum::StandardBloomFilter<str>) -> Vec<Commitment>  /* Bloom filter parameter */
    /* The function returns a vector containing commitments of values from 1 to n */    
{    
    // Initialize variables
    let mut cm: Vec<Commitment> = Vec::new();
    
    // Push the keys to the sub-vector of d based on their values
    for (key, val) in db.iter() {
        d[*val as usize].push(key.to_string());
    }
    println!("D: {:?}", d);

    // Generate commitments for each value from 1 to n
    for i in 1..n+1 {
        // Case sub-vector is empty
        if d[i as usize].is_empty() {
            let mut ri = rand::thread_rng().gen_range(1..=n);
            // Check if ri exists in the set_id or not, if exist, create a new ri
            while set_id.contains(&ri.to_string()) {
                ri = rand::thread_rng().gen_range(1..=n);
            }
            println!("D: {:?}", vec![0.to_string(), ri.to_string()]);
            // create commitment for this case
            let (_, ci) = setcommit(&prover_params, vec![0.to_string(), ri.to_string()], bloom);
            cm.push(ci);
        } else {
            let mut temp_arr = d[i as usize].clone();
            let size_d = d.len();
            temp_arr.push(size_d.to_string());
            println!("D: {:?}", temp_arr);
            let (_, ci) = setcommit(&prover_params, temp_arr, bloom);
            cm.push(ci);
        }
    }
    
    // Generate the final commitment for the provided set_id: C_{N+1}
    let (_, ci) = setcommit(&prover_params, set_id, bloom);
    cm.push(ci);
    
    // return the vector of commitments cm
    cm
}
    
// Function to change the set of items to indexes in the bloom filter that matches the items
fn settobloom(
        items: &Vec<&str>,
        bloom: &mut plum::StandardBloomFilter<str>
    )-> Vec<usize> {
    let mut res: Vec<usize>=vec![];
    for i in items {
	    let mut idx = bloom.item_to_indexes(i);
	    println!( "indexes {:?}", idx );
	    res.append(&mut idx);
    }
    let res: Vec<_> = res.into_iter().unique().collect();
    println!( "combined indexes {:?}", res );
    return res;
}

fn setprove(
        prover_params: &ProverParams,
        init_values: &Vec<Vec<u8>>,
        //item: &str,
        items: &Vec<&str>,
        bloom: &mut plum::StandardBloomFilter<str>,
        com: &Commitment
    )-> Proof {
    //let idx = bloom.item_to_indexes(item);
    let idx = settobloom(items,bloom);
    println!( "indexes {:?}", idx );
    
    let n_proof = idx.len();
    println!("number of indexes:{}",n_proof);
    
    let mut proofs: Vec<Proof> = Vec::with_capacity(n_proof);

    let mut value_sub_vector: Vec<&[u8]> = vec![];
    for index in &idx {
        let proof = Proof::new(&prover_params, &init_values, *index).unwrap();
        proofs.push(proof);
        value_sub_vector.push(&[49]);
    }
            
    //println!("value sub vector:{:?}",value_sub_vector);
	let agg_proof=Proof::same_commit_aggregate(&com,
		&proofs,
		&idx,
    	&value_sub_vector,
    	bloom.optimal_m).unwrap();
    	
   	let mut proof_bytes: Vec<u8> = vec![];
    assert!(agg_proof.serialize(&mut proof_bytes, true).is_ok());
    println!("Aggregated Proof: {:02x?}", proof_bytes);
    
   	return agg_proof;
}

fn setverify(
        verifier_params: &VerifierParams,
        com: &Commitment,
        //item: &str,
        items: &Vec<&str>,
        bloom: &mut plum::StandardBloomFilter<str>,
        agg_proof: Proof
    )-> bool {

   // let idx = bloom.item_to_indexes(item);
    let idx = settobloom(items,bloom);
    println!("Indexes of item: {:?}",idx);
    let n_proof = idx.len();
    	
    let value_sub_vector = vec![&[49]; n_proof];
    let res=agg_proof.same_commit_batch_verify(&verifier_params, 
    	&com, 
    	&idx, 
    	&value_sub_vector);
  	
  	/* //Verify each proof
	let mut res;
 	for i in 0..n_proof {
        res = proofs[i].verify(&verifier_params, &com, [49], idx[i]);
        println!("Proof at index {}:{}",idx[i],res);
        if res==false{
        	return false;
		}
    }*/
    return res;
}

/*
fn testcommit(n: u8, S: &mut [String]) {
    let items_count = 10; //1_000_000;
    let fp_rate = 0.01;
    let mut bloom = StandardBloomFilter::<str>::new(items_count, fp_rate);

    let n = bloom.optimal_m;//16usize;
    let seed = "This is a very very very very very very long Seed";
    // generate the parameters, and performs pre_computation
    let (mut prover_params, verifier_params) =
        //paramgen_from_seed("This is Leo's Favourite very very long Seed", 0, n).unwrap();
        paramgen_from_seed(seed, 0, n).unwrap();
    prover_params.precomp_256(); // precomp_256, or nothing, as you wish

    let (init_values,old_com) = setcommit(&prover_params,vec,&mut bloom);

    let mut old_commitment_bytes: Vec<u8> = vec![];
    assert!(old_com.serialize(&mut old_commitment_bytes, true).is_ok());
    assert_eq!(
        old_com,
        Commitment::deserialize(&mut old_commitment_bytes[..].as_ref(), true).unwrap()
    );

    println!("\nCommitment:  {:02x?}\n", old_commitment_bytes);
    println!("Bloom filter array: {:?}", init_values);

    return old_commitment_bytes;
}
*/

// Function to get init_values of the BF
fn get_init_values (bloom: &mut plum::StandardBloomFilter<str>) -> Vec<Vec<u8>> {
    let mut init_values: Vec<Vec<u8>> = Vec::with_capacity(bloom.optimal_m);
    for i in 0..bloom.optimal_m {
        let x = bloom.bitmap[i] as i32;
        let y = format!("{}", x);
        let v = y.into_bytes();
        init_values.push(v);
    }
    return init_values;
}

fn database_query (db: &std::collections::HashMap<String, u32>, x: &str) -> Vec<u32> {
    let mut ret: Vec<u32> = Vec::new();
    for (key, val) in db.iter() {
        if key == x {
            ret.push(*val);
            break;
        }
    }
    return ret;
}

// This function below will create prove for any input key if it exists in the vector commitment or not
// Pseudo code:
// ZKEDB.ProveDB( cm, db, x, r, pp)
// 1: Ret = db(QC)           -> In this case, QC is the query case that contains the key x and D(QC) is the value of the key x
// 2: if Ret = ∅ then
// 3:     Cn+1 ← Extract from cm (last element
// 4:     Proof ← ZAC.ProveN( Cn+1, K, {x}, r, pp)      (create prove that x is not in the set K)
// 5: else
// 6:     Cv ← Extract from cm (with index = Ret = D(QC) = v)
// 7:     Proof ← ZAC.ProveM( Cv, Dv, {x}, r, pp)     (create prove that x is in the set Dv. This implies that x is in the set K)
// 8: return Proof
fn prove_q (
    vec_key: Vec<String>,
    cm: Vec<Commitment>,
    ret: Vec<u32>,
    d: &Vec<Vec<String>>,
    x: &str,
    prover_params: &ProverParams,
    init_values: &Vec<Vec<u8>>,
    bloom: &mut plum::StandardBloomFilter<str>) -> Proof
{
    if ret.len() == 0 {
        // Call ZKEDB.ProveN( Cn+1, K, {x}, r, pp)
        let ci = cm.last().unwrap();    // This is Cn+1
        // K is vec_key, x is the query key, r is the randomness, pp is the public parameters in the bloom variable
        let proof = setprove(&prover_params, &init_values, &vec![x], bloom, ci);
        return proof;
    } else {
        // Call ZKEDB.ProveM( Cv, Dv, {x}, r, pp)
        let ci = &cm[ret[0].clone() as usize];
        let proof = setprove(&prover_params, &init_values, &vec![x], bloom, ci);
        return proof;
    }
}


// This function below will verify the proof for any input key if it exists in the vector commitment or not
// Pseudo code:
// ZKEDB.VerifyQ( cm, db, x, Proof, pp )
// 1: Ret = db(QC)           -> In this case, QC is the query case that contains the key x and D(QC) is the value of the key x

fn verify_q (
    verifier_params: &VerifierParams,
    cm: Vec<Commitment>,
    ret: Vec<u32>,
    x: &str,
    bloom: &mut plum::StandardBloomFilter<str>,
    proof: Proof) -> bool
{    
    if ret.len() == 0 {
        let ci = cm.last().unwrap();
        let res = setverify(&verifier_params, ci, &vec![x], bloom, proof);
        return res;
    } else {
        let ci = &cm[ret[0].clone() as usize];
        let res = setverify(&verifier_params, &ci, &vec![x], bloom, proof);
        return res;
    }
}


fn main() {
    // let vec=read_csv("../../data/input.csv");
    
    let items_count = 5; //1_000_000;
    let fp_rate = 0.01;
    
    let mut bloom = StandardBloomFilter::<str>::new(items_count, fp_rate);
    let n = bloom.optimal_m;//16usize;
    // create vector d, contains n + 1 sub_vector of keys that have the same value as index or empty
    let mut _d: Vec<Vec<String>> = vec![Vec::new(); n + 1];
    let seed = "This is a very very very very very very long Seed";

    // generate the parameters, and performs pre_computation
    let (mut prover_params, verifier_params) =
        //paramgen_from_seed("This is Leo's Favourite very very long Seed", 0, n).unwrap();
        paramgen_from_seed(seed, 0, n).unwrap();
    prover_params.precomp_256(); // precomp_256, or nothing, as you wish

    // --------------------- Generate data ---------------------
    // create vector of keys
	let mut vec_key: Vec<String> = Vec::new();
    for i in 0..items_count {
        let character = (b'A' + (i - 1) as u8) as char;
        vec_key.push(character.to_string());
    }
    println!("Vector of keys: {:?}", vec_key);

    // Create the hashmap that contain key-value pairs
    let mut map: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    for i in 0..items_count {
        map.insert(vec_key[i].clone(), rand::thread_rng().gen_range(1..=n as u32));
    }
    // ---------------------------------------------------------

    // Create init_values contains bytes type of bloom filter, and old_com is the commitment of the set of items
    //let (init_values,old_com) = setcommit(&prover_params,vec_key, &mut bloom);

    let vec_cm = create_commit(vec_key.clone(), &map, &mut _d, &prover_params, n as u32, &mut bloom);
    let init_values = get_init_values(&mut bloom);
    println!("Commitment: {:?}", vec_cm);
    
    // let mut old_commitment_bytes: Vec<Vec<u8>> = vec![];
    // assert!(old_com.serialize(&mut old_commitment_bytes, true).is_ok());
    /*
    assert_eq!(
        old_com,
        Commitment::deserialize(&mut old_commitment_bytes[..].as_ref(), true).unwrap()
    );*/

    println!("\nCommitment:  {:02x?}\n", vec_cm);
    println!("Bloom filter array: {:?}", init_values);
    
    let check_items = "A";
    let ret = database_query(&map, check_items);

    // let agg_proof=setprove(&prover_params, 
    // 	&init_values, 
	// 	&check_items,
	// 	&mut bloom,
	// 	&old_com);
    
    let agg_proof = prove_q(vec_key.clone(), vec_cm.clone(), ret.clone(), &_d,&check_items, &prover_params, &init_values,  &mut bloom);
		
	// let res = setverify(&verifier_params,
    //     &old_com,
    //     &check_items,
    //     &mut bloom,
    //     agg_proof);

    let res = verify_q(&verifier_params, vec_cm.clone(), ret.clone(),&check_items, &mut bloom, agg_proof);

	println!("result of verification:{}",res);

    /*let check_item="item1";
	let agg_proof=setprove(&prover_params, 
		&init_values, 
		check_item,
		&mut bloom,
		&old_com);
	
	let res = setverify(&verifier_params,
        &old_com,
        check_item,
        &mut bloom,
        agg_proof);
	println!("result of verification:{}",res);
	
	let set1=vec!["item1","item5"];
	settobloom(set1,&mut bloom);*/

}

