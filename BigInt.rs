use std::str::FromStr;
use std::cmp::Ordering;

fn bigint(s: &str) -> Bigint {
    Bigint::from_str(s).unwrap()
}

#[test]
fn test_basic() {
    assert_eq!(Bigint::new(), bigint("0"));
    assert!(Bigint::from_str("foobar").is_err());

    assert!(bigint("1").is_positive());
    assert!(bigint("-1").is_negative());

    assert_eq!(bigint("123") + bigint("456"), bigint("579"));
    assert_eq!(bigint("579") - bigint("456"), bigint("123"));

    assert!(bigint("123") > bigint("122"));
}

#[test]
fn test_if_zero_is_possitive_or_negattive() {
    assert_eq!(bigint("0").is_positive(),false);
    assert_eq!(bigint("-0").is_positive(),false);
    assert_eq!(bigint("+0").is_positive(),false);
    assert_eq!(bigint("0").is_negative(),false);
    assert_eq!(bigint("-0").is_negative(),false);
    assert_eq!(bigint("+0").is_negative(),false);
}

#[test]
#[should_panic]
fn test_form_str_when_exception_thrown_with_invalid_number1() {
    bigint("f1");
}

#[test]
#[should_panic]
fn test_form_str_when_exception_thrown_with_invalid_number2() {
    bigint("+ffd1");
}

#[test]
fn test_when_passed_value_is_empty(){
    assert_eq!(bigint(""), bigint("0"));
}


#[test]
fn test_if_possitive_and_negative_zeros_are_equal() {
    assert_eq!(bigint("+0"), bigint("-0"));
    assert_eq!(bigint("0"), bigint("-0"));
    assert_eq!(bigint("0"), bigint("+0"));
}

#[test]
fn test_partial_order_comparison_between_two_numbers(){
    assert!(bigint("214")>bigint("-12"));
    assert!(bigint("333")>bigint("3"));
    assert!(bigint("36")>bigint("34"));
    assert!(bigint("-34")>bigint("-36"));
    assert!(bigint("-364")>bigint("-34"));
    assert!(bigint("-0")==bigint("+0"));
}

#[test]
fn test_sum_of_numbers(){
    assert_eq!(bigint("12") + bigint("442"), bigint("454"));
    assert_eq!(bigint("442") + bigint("12"), bigint("454"));
    assert_eq!(bigint("120") + bigint("342"), bigint("462"));
    assert_eq!(bigint("12426") + bigint("944"), bigint("13370"));
    assert_eq!(bigint("-12426") + bigint("-944"), bigint("-13370"));
    assert_eq!(bigint("-120") + bigint("342"), bigint("222"));
    assert_eq!(bigint("120") + bigint("-342"), bigint("-222"));
    assert_eq!(bigint("-120") + bigint("120"), bigint("+0"));
    assert_eq!(bigint("-120") + bigint("120"), bigint("-0"));
    assert_eq!(bigint("0") + bigint("0"), bigint("+0"));
  }

 #[test]
fn test_substract_of_numbers(){
    assert_eq!(bigint("1208") - bigint("342"), bigint("866"));
    assert_eq!(bigint("350") - bigint("342"), bigint("8"));
    assert_eq!(bigint("5") - bigint("8"), bigint("-3"));
    assert_eq!(bigint("-5") - bigint("-8"), bigint("3"));
    assert_eq!(bigint("12") - bigint("442"), bigint("-430"));
    assert_eq!(bigint("-120") - bigint("-342"), bigint("222"));
    assert_eq!(bigint("-120") - bigint("+120"), bigint("-240"));
    assert_eq!(bigint("120") - bigint("120"), bigint("0"));
    assert_eq!(bigint("120") - bigint("120"), bigint("-0"));
    assert_eq!(bigint("120") - bigint("120"), bigint("+0"));
    assert_eq!(bigint("0") - bigint("0"), bigint("+0"));
  }

#[derive(Debug, PartialEq, Eq)]
pub struct Bigint {
    pub sign: i8,
    pub digits: Vec<u8>,
}

impl Bigint {
    /// Конструира нов Bigint със стойност "0" и положителен знак.
    /// Това може да означава празен вектор с цифри или масив с една цифра `0` -- ваш избор.
    ///
    pub fn new() -> Self {
        Self { sign:1, digits:vec!(0)}
    }

    /// Конструира нов Bigint с подадените цифри и знак.
    ///
    /// Тук е добро място където можете да вкарате малко валидация и нормализиране на входа -- да
    /// премахнете допълнителни нули или да се погрижите, че нулата винаги има консистентен знак.
    /// Стига да се погрижите винаги да използвате функцията при конструириане на нови Bigint-ове.
    ///
    /// Тази функция НЕ Е публична, така че НЕ Е задължителна -- ако не ви трябва, може смело да я
    /// изтриете.
    ///
    fn from_components(digits: Vec<u8>, sign: i8) -> Self {
        let digits_vector = Bigint::trim_leading_zeros(&digits);
        let sign_value = Bigint::get_sign_value(&digits, sign);
        Self{sign: sign_value, digits:digits_vector}
    }

    fn get_sign_value(v: &Vec<u8>, sign: i8) -> i8{
        return if v.cmp(&vec!(0)) == Ordering::Equal {1} else {sign}
    }

    fn custom_cmp(&self, other: &Bigint) -> Ordering {
        if self.digits.len() != other.digits.len(){
            return if self.digits.len() > other.digits.len() {Ordering::Greater} else {Ordering::Less}
        }
        return self.digits.cmp(&other.digits)
    }

    fn trim_leading_zeros(value: &Vec<u8>) -> Vec<u8>{
        if value.len() > 1 {
            let mut trimmed_vector:Vec<u8> = value.to_vec().into_iter().skip_while(|&x| x == 0).collect();
            if trimmed_vector.len() == 0 {
                trimmed_vector.push(0);
            }
            return trimmed_vector;
        }
        value.to_vec()  
    }

    fn convert_str_to_vec(s: &str) -> Vec<u8>{
        let mut v = Vec::new();
        for ch in s.chars() {
            v.push(ch as u8 - 48);
         }
         v
   }

    /// Връща `true` ако числото е положително. Нулата не е положителна.
    pub fn is_positive(&self) -> bool {
        if self.sign == -1 || self.digits.cmp(&vec!(0)) == Ordering::Equal {false} else {true}
    }

    /// Връща `true` ако числото е отрицателно. Нулата не е отрицателна.
    pub fn is_negative(&self) -> bool {
        if self.digits.cmp(&vec!(0)) == Ordering::Equal {false} else {!self.is_positive()}
    }
}


#[derive(Debug)]
pub struct ParseError;

impl FromStr for Bigint {
    type Err = ParseError;
    /*
    /// Очакваме низа да е във формат десетично цяло число с опционален знак, тоест всички тези
    /// неща би трябвало да върнат `Ok` резултат с конструиран Bigint:
    ///
    ///     Bigint::from_str("123")
    ///     Bigint::from_str("+123")
    ///     Bigint::from_str("-123")
    ///
    /// Това включва нулата, като имате предвид че, както казахме, +0 и -0 трябва да са
    /// еквивалентни.
    ///
    /// Ако подадения низ е празен, това връща същото като да сме подали "0".
    ///
    /// Ако подадения низ започва с нули, това няма значение -- игнорират се. Тоест, конструиране с
    /// "00123" ще е същото като конструиране с "123".
    ///
    /// Ако сме подали низ, който включва каквито и да е други символи освен цифрите 0-9 (и
    /// опционален начален знак), очакваме да върнете `ParseError`.
    */

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.chars().count() == 0{
            return Ok(Bigint::from_components(vec!(0), 1))
        }
        let mut starting_index = 0;
        let mut sign = 1;
        //Checking if we have a sign at the beggining and apply the need logic to it
        if s.as_bytes()[0] as char == '+' || s.as_bytes()[0] as char == '-'{
            sign = if s.as_bytes()[0] as char  == '+' {1} else {-1};
            starting_index = 1;
        }
        let digits = &s[starting_index..s.chars().count()];
        if digits.chars().all(char::is_numeric){
            return Ok(Bigint::from_components(Bigint::convert_str_to_vec(digits), sign));
        }
        Err(ParseError)
    }
}


impl PartialOrd for Bigint {
    /// Две цели числа винаги могат да се сравнят, така че "частичното" равенство е същото като
    /// пълното.
    ///
    fn partial_cmp(&self, other: &Bigint) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bigint {
    /// Ако едното от числата е положително, а другото -- отрицателно, положителното е по-голямо.
    ///
    /// Ако и двете числа са положителни, това с повече цифри е по-голямо. Ако имат еднакъв брой
    /// цифри, лексикографско сравнение на цифрите от по-значима към по-малко значима цифра ще ви
    /// върне по-голямото число. (Внимавайте с нулата -- тя има 1 цифра)
    ///
    /// Ако и двете числа са отрицателни, горната логика е същата, просто сравнението е обърнато
    /// (-1 е по-голямо от -2 и от -10).
    ///
    fn cmp(&self, other: &Bigint) -> Ordering {
        if self.sign != other.sign {
            return if self.sign == 1 {Ordering::Greater} else {Ordering::Less};
        }
        if self.digits.len() != other.digits.len(){
            return if self.digits.len() > other.digits.len() {Ordering::Greater} else {Ordering::Less}
        }
        return if self.sign == 1 {self.digits.cmp(&other.digits)} else {other.digits.cmp(&self.digits)}
    }
}


use std::ops::{Add, Sub};

impl Add for Bigint {
    type Output = Bigint;

    /// За да съберете две числа, първия въпрос е: какви са им знаците?
    ///
    /// - Ако и двете са положителни, събираме ги цифра по цифра и слагаме на резултата положителен
    ///   знак.
    /// - Ако и двете са отрицателни, пак можем да ги съберем цифра по цифра и да сложим
    ///   отрицателен знак на крайния резултат.
    /// - Ако имат различни знаци, намираме по-голямото *по абсолютна стойност*. Изваждаме цифрите
    ///   на по-малкото от по-голямото. Знака на резултата е знака на по-голямото по абсолютна
    ///   стойност. Ако са равни, резултата трябва да е нула (която винаги се очаква да е
    ///   положителна).
    ///
    /// При събиране цифра по цифра, не забравяйте да пренасяте "едно наум" ако резултата е
    /// по-голям от десетична цифра. При различна дължина на списъците от цифри, можете да
    /// запълните с нули, да внимавате с индексите, или нещо по средата.
    ///
    fn add(self, other: Self) -> Self {
        let mut v = Vec::new();
        let mut left_over = 0;
        let mut operation_result;
        let mut bigger_number = if self.custom_cmp(&other) == Ordering::Greater {self.digits.clone()} else {other.digits.clone()};
        let smaller_number = if self.custom_cmp(&other) == Ordering::Greater {&other.digits} else {&self.digits};
        let smaller_number_sign = if self.custom_cmp(&other) == Ordering::Greater {other.sign} else {self.sign};
        let bigger_number_sign = if self.custom_cmp(&other) == Ordering::Greater {self.sign} else {other.sign};
        let mut smaller_number_index = smaller_number.len()-1;
        let mut bigger_number_index = bigger_number.len()-1;
        loop {
            if self.sign==other.sign{
                operation_result = bigger_number[bigger_number_index] as i8 + smaller_number[smaller_number_index] as i8 + left_over;
            }else {
                operation_result = (bigger_number[bigger_number_index] as i8)*bigger_number_sign + (smaller_number[smaller_number_index] as i8)*smaller_number_sign + left_over;
            }
            if  operation_result >= 10 {
                left_over = 1;
                operation_result = operation_result % 10;
            }
            else if operation_result < 0{
                if bigger_number_sign == -1{
                    left_over = 0;
                    operation_result = operation_result*-1
                }
                else {
                    left_over = -1;
                    operation_result = operation_result + 10;
                }
            }
            else {
                left_over = 0;
            }
            v.push(operation_result as u8);
            if smaller_number_index == 0 { break; }
            smaller_number_index-=1;
            bigger_number_index-=1;
        }
        if bigger_number_index>0{
            let mut start_index_for_left_over_number = 0;
            if left_over != 0 {
                let mut biggest_left_digit = bigger_number[bigger_number_index-1] as i8;
                biggest_left_digit += left_over;
                if biggest_left_digit >= 0 {
                    bigger_number[bigger_number_index-1] = biggest_left_digit as u8;
                }
                else {
                    start_index_for_left_over_number = 1;
                    bigger_number[bigger_number_index-1] = 9;
                }
            }
            bigger_number[start_index_for_left_over_number..bigger_number_index].reverse();
            v.extend_from_slice(&bigger_number[0..bigger_number_index]);
        }
        v.reverse();
        let digits = Bigint::trim_leading_zeros(&v);
        let sign = Bigint::get_sign_value(&digits, bigger_number_sign);
        Self {digits:digits, sign:sign}
    }
}

impl Sub for Bigint {
    type Output = Bigint;

    /// Изваждането често се имплементира като събиране с отрицателен знак. Тоест, `A - B` е
    /// еквивалентно на `A + (-B)`. Можете да имплементирате изваждането като форма на събиране, и
    /// в него да пакетирате логиката. Или можете да проверите знаците и да разделите логиката по
    /// събиране и по изваждане между `add` и `sub`.
    ///
    /// При изваждане, също не забравяйте "едното наум", ако цифрата от която вадите е по-малката,
    /// което ще се преведе до едно "-1" на следващата цифра. Погрижете се винаги да вадите от
    /// по-голямото по абсолютна стойност число, и после сложете какъвто знак се налага.
    ///
    /// Внимавайте с типовете -- изваждане на unsigned от unsigned число може да се счупи.
    ///
    fn sub(self, other: Self) -> Self {
        let transformed_other = Bigint::from_components(other.digits, other.sign*-1);
        self.add(transformed_other)
    }
}