use std::collections::VecDeque;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    DivideByZero,
    StackUnderflow,
    InvalidCommand,
    NoInstructions,
}


#[derive(Debug, Default)]
pub struct Interpreter {
    pub instructions: VecDeque<String>,
    pub stack: Vec<i32>,
    operations_map: HashMap<String, String>,
    traceback_instructions: VecDeque<String>,
    traceback_stack: Vec<i32>,
    // + още полета за поддръжка на .back() метода
}

impl Interpreter {
    /// Конструира нов интерпретатор с празен стек и никакви инструкции.
    pub fn new() -> Self {
        let mut map:HashMap<String, String> = HashMap::new();
        map.insert(String::from("pop"),String::from("push"));
        map.insert(String::from("push"),String::from("pop"));
        map.insert(String::from("add"),String::from("sub"));
        map.insert(String::from("sub"),String::from("add"));
        map.insert(String::from("mul"),String::from("div"));
        map.insert(String::from("div"),String::from("mul"));
        Self{instructions: VecDeque::new(), 
            stack: Vec::new(), 
            operations_map: map,
            traceback_instructions: VecDeque::new(), 
            traceback_stack: Vec::new()}
    }

    /// Добавя инструкции от дадения списък към края на `instructions`. Примерно:
    ///
    /// interpreter.add_instructions(&[
    ///     "PUSH 1",
    ///     "PUSH 2",
    ///     "ADD",
    /// ]);
    ///
    /// Инструкциите не се интерпретират, само се записват.
    ///
      // let mut instruction;
      //   let mut operation;
      //   let mut value;
      //   for inst in instructions{
      //       instruction = inst.trim().split_whitespace();
      //       operation = instruction.next().unwrap();
      //       self.instructions.push_back(operation.to_string());
      //       if operation == "push"{
      //           value = instruction.next().unwrap().parse::<i32>().unwrap();
      //           self.stack.push(value);
      //       }
    pub fn add_instructions(&mut self, instructions: &[&str]) {
        for inst in instructions{
            self.instructions.push_back(inst.to_string());
        }
    }

    /// Връща mutable reference към инструкцията, която ще се изпълни при
    /// следващия `.forward()` -- първата в списъка/дека.
    ///
    pub fn current_instruction(&mut self) -> Option<&mut String> {
        Some(&mut self.instructions[0])
    }

    /// Интерпретира първата инструкция в `self.instructions` по правилата описани по-горе. Записва
    /// някаква информация за да може успешно да се изпълни `.back()` в по-нататъшен момент.
    ///
    /// Ако няма инструкции, връща `RuntimeError::NoInstructions`. Другите грешки идват от
    /// обясненията по-горе.
    ///
    pub fn forward(&mut self) -> Result<(), RuntimeError> {
        if self.instructions.is_empty(){
            return Err(RuntimeError::NoInstructions);
        }
        let mut instruction = self.instructions[0].clone().to_lowercase();
        let mut operation = instruction.trim().split_whitespace().collect::<Vec<&str>>();
        let mut operation_value = operation[0];
        if !self.operations_map.contains_key(operation_value){
            return Err(RuntimeError::InvalidCommand);
        }
        let reverse_value = self.operations_map.get(operation_value).unwrap().to_string();
        if operation_value == "push"{
            if  operation.len() != 2 || !operation[1].parse::<i32>().is_ok(){
                return Err(RuntimeError::InvalidCommand);
            }
            else {
                self.pop_values();
                self.traceback_stack.push(operation[1].parse::<i32>().unwrap());
                self.stack.push(operation[1].parse::<i32>().unwrap());
                self.traceback_instructions.push_back(reverse_value);
            }
        }
        else if operation_value == "pop" {
            if self.stack.is_empty(){
                return Err(RuntimeError::StackUnderflow);
            }
            if operation.len() != 1{
                return Err(RuntimeError::InvalidCommand);
            }
            else {
                let mut poped_value = self.stack[self.stack.len()-1];
                self.pop_values();
                self.traceback_stack.push(poped_value);
                self.traceback_instructions.push_back(reverse_value);
            }
        }
        else if vec!["add","sub","div","mul"].iter().any(|&i| i==operation_value){
            if self.stack.len() < 2{
                return Err(RuntimeError::StackUnderflow);
            }
            let first_value = self.stack[self.stack.len()-1];
            let second_value = self.stack[self.stack.len()-2];
            if operation_value == "div"{
                if second_value == 0 {
                    return Err(RuntimeError::DivideByZero);
                }
                else {
                    self.pop_values();
                    self.stack.push(first_value/second_value);
                    self.push_values(first_value,second_value,&reverse_value);
                }
            }
            else if operation_value == "mul"{
                self.pop_values();
                self.stack.push(first_value*second_value);
                self.push_values(first_value,second_value,&reverse_value);
            }
            else if operation_value == "add"{
                self.pop_values();
                self.stack.push(first_value+second_value);
                self.push_values(first_value,second_value,&reverse_value);
            }
            else if operation_value == "sub"{
                self.pop_values();
                self.stack.push(first_value-second_value);
                self.push_values(first_value,second_value,&reverse_value);
            }
        }
        Ok(())
    }
    fn push_values(&mut self,first_value:i32, second_value:i32, reverse_value:&String) {
        self.traceback_stack.push(second_value);
        self.traceback_stack.push(first_value);
        self.traceback_instructions.push_back(reverse_value.to_string());
    }

    fn pop_values(&mut self) {
        let instruction = self.instructions[0].clone().to_lowercase();
        let operation = instruction.trim().split_whitespace().collect::<Vec<&str>>()[0];
        self.instructions.pop_front();
        if operation != "push"{
            self.stack.pop();
            if operation != "pop"{
                self.stack.pop();
            }
        }      
    }
    /// Вика `.forward()` докато не свършат инструкциите (може и да се имплементира по други
    /// начини, разбира се) или има грешка.
    ///
    pub fn run(&mut self) -> Result<(), RuntimeError> {
        loop {
            match self.forward() {
                Err(RuntimeError::NoInstructions) => return Ok(()),
                Err(e) => return Err(e),
                _ => (),
            }
        }
    }

    /// "Обръща" последно-изпълнената инструкция с `.forward()`. Това може да се изпълнява отново и
    /// отново за всяка инструкция, изпълнена с `.forward()` -- тоест, не пазим само последната
    /// инструкция, а списък/стек от всичките досега.
    ///
    /// Ако няма инструкция за връщане, очакваме `RuntimeError::NoInstructions`.
    ///
    pub fn back(&mut self) -> Result<(), RuntimeError> {
        println!("{:?}", self.traceback_stack);
        if self.traceback_instructions.is_empty(){
            return Err(RuntimeError::NoInstructions);
        }
        let mut operation = self.traceback_instructions.pop_back().unwrap().clone();
          if operation == "push"{
            let push_value = self.traceback_stack.pop().unwrap();
            self.stack.push(push_value);
            self.instructions.push_front("pop".to_string().to_uppercase());
        }
        else if operation == "pop"{
            let value = self.traceback_stack.pop().unwrap();
            self.stack.pop();
            self.instructions.push_front(format!(r#"push {}"#, value).to_uppercase());
        }
        else if vec!["add","sub","div","mul"].iter().any(|&i| i==operation){
            let first_value = self.traceback_stack.pop().unwrap();
            let second_value = self.traceback_stack.pop().unwrap();
            self.stack.pop();
            self.stack.push(second_value);
            self.stack.push(first_value);
            let mut rev_value = self.operations_map.get(&operation).unwrap().to_string();
            self.instructions.push_front(rev_value.to_string().to_uppercase());
        }
        Ok(())
    }
}