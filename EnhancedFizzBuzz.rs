use std::borrow::Cow;

pub struct FizzBuzzer {
    labels: [String; 3],
}

impl FizzBuzzer {
    pub fn new(labels: [String; 3]) -> Self {
        FizzBuzzer { labels }
    }

    /// Връщаме нова структура `FizzBuzzerIter`, която има връзка с оригиналния FizzBuzzer и
    /// каквото още ѝ трябва, за да може да връща резултати.
    pub fn iter(&self) -> FizzBuzzerIter {
        FizzBuzzerIter { fizzbuzzer:self, num:1}
    }
}

pub struct FizzBuzzerIter<'a> {
    fizzbuzzer: &'a FizzBuzzer,
    num: i32,
    // каквито други полета ви трябват
}

impl <'a>Iterator for FizzBuzzerIter<'a> {
    type Item =  Cow<'a, str>;    
    /// Очакваме всяко извикване на тази функция да връща следващото естествено число, започващо от
    /// 1:
    ///
    /// - Ако числото се дели на 3, връщаме `Cow::Borrowed`, държащо reference към `labels[0]`
    /// - Ако числото се дели на 5, връщаме `Cow::Borrowed`, държащо reference към `labels[1]`
    /// - Ако числото се дели на 15, връщаме `Cow::Borrowed`, държащо reference към `labels[2]`
    /// - Иначе, връщаме `Cow::Owned`, държащо числото, конвертирано до `String`
    ///
    fn next(&mut self) -> Option<Self::Item> {
        let mut label = "";
        let mut number = String::from("");
        if self.num % 15 == 0 {
            label = &self.fizzbuzzer.labels[2];
        }
        else if self.num % 3 == 0 {
            label = &self.fizzbuzzer.labels[0];
        }
        else if self.num % 5 == 0 {
            label = &self.fizzbuzzer.labels[1];
        }
        else {
            number = self.num.to_string();
        }
        self.num += 1;
        if label == "" {
            Some(Cow::Owned(number))
        }
        else {
            Some(Cow::Borrowed(label))
        }
    }
}