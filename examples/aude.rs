use aude::*;

use std::io::{self, Write};

fn main() {
    println!("=== Aude 0.1 ===");
    println!("Type `help` for more information.");
    loop {
        print!("> ");
        let mut input = String::new();
        io::stdout().flush().unwrap();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {}
            Err(_) => {
                println!("ERROR: Could not read input");
                continue;
            }
        };

        match input.trim() {
            "" => {
                // Print separator for readability.
               print!("\n------------------------------------<o=o");
               println!("o=o>------------------------------------\n");
               continue;
            }
            "bye" => break,
            "help" => println!("{}", include_str!("../assets/help/help.txt")),
            x if input.starts_with("echo ") => {
                match parsing::parse_str(&x[5..]) {
                    Ok(mut x) => {
                        x.analyze();
                        println!("{:?}", x);
                    }
                    Err(err) => {
                        println!("ERROR:\n{}", err);
                    }
                }
            }
            x => {
                match parsing::parse_str(x) {
                    Ok(mut x) => {
                        x.analyze();
                        println!("\n{}", x);
                        let ref mut ctx = vec![];
                        if let Some(mut y) = x.ty(ctx) {
                            y.analyze();
                            println!("\nty: {}", y);
                        }
                        if let Some(mut y) = x.deriv(ctx) {
                            y.analyze();
                            println!("\nD: {}", y);
                        }
                        println!("");
                    }
                    Err(err) => {
                        println!("ERROR:\n{}", err);
                    }
                }
            }
        }
    }
}
