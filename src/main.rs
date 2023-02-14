use std::env;
use ExprU::*;
use Token::*;
use ParseErr::*;
use RuntimeErr::*;
use std::fmt;

fn main() {
    // bare-bones CLI
    let output = match &env::args().collect::<Vec<String>>()[..] {
        [_, input] => match run(input.clone()) {
            Ok(value) => value.to_string(),
            Err(e) => e.to_string(),
        },
        _ => "error - expected exactly one argument.".to_owned(),
    };

    println!("{}", output)
}

#[derive(Clone, Debug, PartialEq)]
enum Token {
    ParenTok(char),
    OpTok(String),
    FloatTok(f32),
}

#[derive(Clone, Debug, PartialEq)]
enum ExprU {
    OperatorU {
        name: String,
        left: Box<ExprU>,
        right: Box<ExprU>,
    },
    FloatU(f32),
}

impl fmt::Display for ExprU {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            FloatU(x) =>
                x.to_string(),

            OperatorU { name, left, right }  =>
                format!("{} {} {}", left, name, right),
        };

        write!(f, "{}", s)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum ParseErr {
    OperatorMissingValuesErr { name: String },
    UnexpectedTokenErr(Token),
    MismatchedParenthesesErr,
    UnrecognizedParenErr(char),
    AstNotUnifiedErr
}

impl fmt::Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            OperatorMissingValuesErr { name } => 
                format!("missing values for operator {}", name),

            UnexpectedTokenErr(tok) =>
                format!("unexpected token: {}", token_name(tok)),
            
            MismatchedParenthesesErr =>
                "mismatched parentheses".to_owned(),

            UnrecognizedParenErr(symbol) =>
                format!("unrecognized paren: {}", symbol),

            AstNotUnifiedErr =>
                "ast not unified".to_owned()
        };

        write!(f, "{}", msg)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum RuntimeErr {
    DivideByZeroErr,
    InvalidOperatorErr { name: String }
}

impl fmt::Display for RuntimeErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            DivideByZeroErr =>
                "divide by zero error".to_owned(),
            
            InvalidOperatorErr { name } =>
                format!("encountered invalid operator {}", name)
        };

        write!(f, "{}", msg)
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Err {
    ParseErr(ParseErr),
    RuntimeErr(RuntimeErr)
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Err::ParseErr(e) => e.to_string(),
            Err::RuntimeErr(e) => e.to_string(),
        };

        write!(f, "{}", msg)
    }
}

fn mk_operatoru(name: String, left: ExprU, right: ExprU) -> ExprU {
    OperatorU {
        name: name,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn tokenize(input: String) -> Vec<Token> {
    let strs = input.split_whitespace();
    let mut tokens = vec![];

    for s in strs {
        let tok = match s {
            "(" => ParenTok('('),
            ")" => ParenTok(')'),
            x => x
                .parse::<f32>()
                .map_or_else(|_| OpTok(s.to_owned()), |n| FloatTok(n)),
        };
        tokens.push(tok);
    }

    tokens
}

fn precedence(op: &Token) -> u32 {
    match op {
        OpTok(symbol) if ["*", "/"].contains(&symbol.as_str()) => 1,
        OpTok(symbol) if ["+", "-"].contains(&symbol.as_str()) => 0,
        _ => 0,
    }
}

fn token_name(tok: &Token) -> String {
    match tok {
        OpTok(name) => name.clone(),
        FloatTok(x) => x.to_string(),
        ParenTok(symbol) => symbol.to_string(),
    }
}

fn parse_operator(e: Token, l: Option<ExprU>, r: Option<ExprU>) -> Result<ExprU, ParseErr> {
    match (e, l, r) {
        // if there are two values, merge them into the ast
        (OpTok(name), Some(x), Some(y)) => Ok(mk_operatoru(name, y, x)),

        // if there are less than two values on the stack, there's an error
        (OpTok(name), _, _) => Err(OperatorMissingValuesErr { name: name.to_owned()}),

        (tok, _, _) => Err(UnexpectedTokenErr(tok)),
    }
}

// uses shunting yard to build the AST from a Vec of tokens
fn parse(tokens: Vec<Token>) -> Result<ExprU, ParseErr> {
    let mut values = vec![];
    let mut operators = vec![];

    for tok in tokens {
        match tok {
            // values move to the value stack
            FloatTok(x) => values.push(FloatU(x)),

            // left parens move to the operator stack
            ParenTok(symbol) if symbol == '(' => operators.push(tok),

            // right parens pops operators to the value stack till we see a left paren
            ParenTok(symbol) if symbol == ')' => loop {
                match operators.pop() {
                    // if there's nothing to pop, there are mismatched parens
                    None => return Err(MismatchedParenthesesErr),
                    Some(op) => {
                        // stop when we see a left paren
                        if op == ParenTok('(') {
                            break;
                        // otherwise merge the values on the value stack with the operator
                        } else {
                            let ast = parse_operator(op, values.pop(), values.pop())?;
                            values.push(ast);
                        }
                    }
                }
            },

            OpTok(_) => loop {
                match operators.pop() {
                    // push this onto the stack if its empty
                    None => {
                        operators.push(tok.clone());
                        break;
                    }

                    // if there is an operator on the stack, and it's not lower precedence
                    Some(op2 @ OpTok(_)) if precedence(&op2) >= precedence(&tok) => {
                        let ast = parse_operator(op2, values.pop(), values.pop())?;
                        values.push(ast);
                    }

                    // if it's something else, like a left paren, put it back and push this op on top
                    Some(op2) => {
                        operators.push(op2);
                        operators.push(tok.clone());
                        break;
                    }
                }
            },

            ParenTok(symbol) => return Err(UnrecognizedParenErr(symbol)),
        }
    }

    loop {
        match operators.pop() {
            None => match &values[..] {
                [ast] => return Ok(ast.clone()),
                _ => return Err(AstNotUnifiedErr),
            },
            Some(op) => {
                let ast = parse_operator(op, values.pop(), values.pop())?;
                values.push(ast);
            }
        }
    }
}

fn eval(expr: ExprU) -> Result<ExprU, RuntimeErr> {
    match expr {
        FloatU(x) => Ok(FloatU(x)),

        OperatorU { name, left, right } => match (*left, *right) {
            (FloatU(x), FloatU(y)) => match name.as_str() {
                "+" => Ok(FloatU(x + y)),
                "*" => Ok(FloatU(x * y)),
                "-" => Ok(FloatU(x - y)),
                "/" => {
                    if y == 0.0 {
                        Err(DivideByZeroErr)
                    } else {
                        Ok(FloatU(x / y))
                    }
                }
                op => Err(InvalidOperatorErr { name: op.to_owned() }),
            },

            (xu, yu) => eval(mk_operatoru(name, eval(xu)?, eval(yu)?)),
        },
    }
}

fn run(input: String) -> Result<ExprU, Err> {
    parse(tokenize(input)).map_err(Err::ParseErr)
        .and_then(|parsed| eval(parsed).map_err(Err::RuntimeErr))
}

#[cfg(test)]
mod test {
    use super::*;

    fn run(input: &str) -> Result<ExprU, Err> {
        super::run(input.to_owned())
    }

    fn mk_operatoru(name: &str, left: ExprU, right: ExprU) -> ExprU {
        super::mk_operatoru(name.to_owned(), left, right)
    }

    #[test]
    fn black_box_tests() {
        assert_eq!(run("1"), Ok(FloatU(1.0)));
        assert_eq!(run("1 + 2"), Ok(FloatU(3.0)));
        assert_eq!(run("1 + 2 * 3"), Ok(FloatU(7.0)));
        assert_eq!(run("( 1 + 2 ) * 3"), Ok(FloatU(9.0)));
        assert_eq!(run("1 + 2 + 3"), Ok(FloatU(6.0)));
        assert_eq!(run("1 * 2 + 1"), Ok(FloatU(3.0)));
        assert_eq!(run("1 +"), Err(Err::ParseErr(OperatorMissingValuesErr { name: "+".to_owned() })));
        assert_eq!(run("( 1 ) )"), Err(Err::ParseErr(MismatchedParenthesesErr)));
        assert_eq!(run("1 $ 2"), Err(Err::RuntimeErr(InvalidOperatorErr { name: "$".to_owned() })));
        assert_eq!(run("1 / 0"), Err(Err::RuntimeErr(DivideByZeroErr)));
    }

    #[test]
    fn tokenize_tests() {
        assert_eq!(
            tokenize("1 + 2".to_owned()),
            vec![FloatTok(1.0), OpTok("+".to_owned()), FloatTok(2.0)]
        );
    }

    #[test]
    fn parse_tests() {
        assert_eq!(
            parse(vec![FloatTok(1.0), OpTok("+".to_owned()), FloatTok(2.0)]),
            Ok(mk_operatoru("+", FloatU(1.0), FloatU(2.0)))
        );
    }
}
