

fn test() -> () {}

fn test2() -> i64 {
    let x = 32;
    let _y = test();
    return x;
}

// fn test_div(a: i64) -> i64 {
//     return a / 0;
// }

fn test_add(a: i64, b: f64) -> f64 {
    let res = a as f64 + b;
    return res;
}

fn main() ->  () {
    println!("Hello World!");
    let _z = test2();
    return ();
}
