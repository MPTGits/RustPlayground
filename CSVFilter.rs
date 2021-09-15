use std::io::{self, Read, BufRead, BufReader, Write};

use std::collections::HashMap;

macro_rules! assert_match { 
    ($expr:expr, $pat:pat) => {
        if let $pat = $expr {
            // all good
        } else {
            assert!(false, "Expression {:?} does not match the pattern {:?}", $expr, stringify!($pat));
        }
    }
}

// За тестване на IO грешки:
struct ErroringReader {}

impl Read for ErroringReader {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::new(io::ErrorKind::Other, "read error!"))
    }
}

impl BufRead for ErroringReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        Err(io::Error::new(io::ErrorKind::Other, "fill_buf error!"))
    }

    fn consume(&mut self, _amt: usize) { }
}



 #[test]
fn test_string_parsing() {
    assert_eq!(skip_next("[test]", '['), Some("test]"));
    assert_eq!(take_until("one/two", '/'), ("one", "/two"));
    assert_eq!(take_and_skip("one/two", '/'), Some(("one", "two")));
}


 #[test]
fn test_skip_first_char() {
    assert_eq!(skip_next("[test]", ']'), None);
    assert_eq!(skip_next("", ']'), None);
    assert_eq!(skip_next("🥺test🥺", '🥺'), Some("test🥺"));
}

 #[test]
fn test_take_until_match() {
    assert_eq!(take_until("pooltest", 'l'), ("poo", "ltest"));
    assert_eq!(take_until("pooltest", 'f'), ("pooltest", ""));
    assert_eq!(take_until("", 'k'),("",""));
    assert_eq!(take_until("🥺test🥺okok", '🥺'),("","🥺test🥺okok"));
    assert_eq!(take_until("test🥺okok", '🥺'),("test","🥺okok"));
    assert_eq!(take_until("test🥺", '🥺'),("test","🥺"));
}

#[test]
fn test_take_until_match_excluding_value() {
    assert_eq!(take_and_skip("one/two", 'l'), None);
    assert_eq!(take_and_skip("k", 'k'),Some(("","")));
    assert_eq!(take_and_skip("", 'k'), None);
    assert_eq!(take_and_skip("🥺test🥺okok", '🥺'),Some(("","test🥺okok")));
    assert_eq!(take_and_skip("test🥺okok", '🥺'),Some(("test","okok")));
}

#[test]
fn test_csv_error() {
    //Error when reading
    assert_match!(Csv::new(ErroringReader {}).err(), Some(CsvError::IO(_)));
}

#[test]
fn test_csv_parse_line() {
    let reader = BufReader::new(r#"
    name, age, birth date
    "Douglas Adams", "42", "1952-03-11"
"#.trim().as_bytes());

let mut csv = Csv::new(reader).unwrap();
//No bracket at start
assert_match!(csv.parse_line(r#" Douglas Adams", "42", "1952-03-11"#).err(),
                             Some(CsvError::InvalidRow(_)));
//Fewer columns
assert_match!(csv.parse_line(r#" Douglas Adams", "1952-03-11"#).err(),
                             Some(CsvError::InvalidRow(_)));
//More columns
assert_match!(csv.parse_line(r#" Douglas Adams", "32", "valid" ,"1952-03-11"#).err(),
                             Some(CsvError::InvalidRow(_)));
//Valid scenario
let row = csv.parse_line(r#""Basic Name","13","2020-01-01""#).unwrap();
    assert_eq! {
        (row["name"].as_str(), row["age"].as_str(), row["birth date"].as_str()),
        ("Basic Name", "13", "2020-01-01"),
    };
}

#[test]
fn test_write_to_valid_scenario() {
    let data = r#"
        name, age, birth date
        "Gen Z. Person", "20"  ,  "2000-01-01"
    "#.trim().as_bytes();

    let mut csv = Csv::new(BufReader::new(data)).unwrap();
    let mut output = Vec::new();
    csv.write_to(&mut output).unwrap();

    let output_lines = output.lines().
        map(Result::unwrap).
        collect::<Vec<String>>();

    assert_eq!(output_lines, &[
        "name, age, birth date",
        "\"Gen Z. Person\", \"20\", \"2000-01-01\"",
    ]);
}

#[test]
fn test_iterator_with_no_filter() {
let reader = BufReader::new(r#"
    name, age, birth date
    "Douglas Adams", "42", "1952-03-11"
    "Gen Z. Person", "20", "2000-01-01"
    "Ada Lovelace", "36", "1815-12-10"
"#.trim().as_bytes());

let mut csv = Csv::new(reader).unwrap();
let filtered_names = csv.map(|row| row.unwrap()["name"].clone()).collect::<Vec<_>>();
//When no filter function
assert_eq!(filtered_names, &["Douglas Adams","Gen Z. Person", "Ada Lovelace"]);
}

#[test]
fn test_iterator_with_filter(){
    let reader = BufReader::new(r#"
    name, age, birth date
    "Douglas Adams", "42", "1952-03-11"
    "Gen Z. Person", "20", "2000-01-01"
    "Ada Lovelace", "36", "1815-12-10"
"#.trim().as_bytes());

let mut csv = Csv::new(reader).unwrap();
csv.apply_selection(|row| {
    let age = row.get("age").ok_or_else(|| CsvError::InvalidColumn(String::from("age")))?;
    let age = age.parse::<u32>().map_err(|_| CsvError::ParseError(String::from(age)));
    Ok(age.unwrap() > 40)
});
let filtered_names = csv.map(|row| row.unwrap()["name"].clone()).collect::<Vec<_>>();
assert_eq!(filtered_names, &["Douglas Adams"]);
}

#[test]
fn test_iterator_with_filter_fales_values_only(){
    let reader = BufReader::new(r#"
    name, age, birth date
    "Douglas Adams", "42", "1952-03-11"
    "Gen Z. Person", "20", "2000-01-01"
    "Ada Lovelace", "36", "1815-12-10"
"#.trim().as_bytes());

let mut csv = Csv::new(reader).unwrap();
csv.apply_selection(|row| {
    let age = row.get("age").ok_or_else(|| CsvError::InvalidColumn(String::from("age")))?;
    let age = age.parse::<u32>().map_err(|_| CsvError::ParseError(String::from(age)));
    Ok(age.unwrap() > 50)
});
let filtered_names = csv.map(|row| row.unwrap()["name"].clone()).collect::<Vec<_>>();
let expected:Vec<String> = Vec::new();
assert_eq!(filtered_names, expected);
}

#[test]
fn test_iterator_with_filter_error(){
    let reader = BufReader::new(r#"
    name, age, birth date
    "Douglas Adams", "42", "1952-03-11"
    "Gen Z. Person", "20", "2000-01-01"
    "Ada Lovelace", "36", "1815-12-10"
"#.trim().as_bytes());

let mut csv = Csv::new(reader).unwrap();
csv.apply_selection(|row| {
    Err(CsvError::InvalidColumn("Some".to_string()))
});
assert_match!(csv.next().unwrap().err(), Some(CsvError::InvalidColumn(_)));
}

#[derive(Debug)]
pub enum CsvError {
    IO(std::io::Error),
    ParseError(String),
    InvalidHeader(String),
    InvalidRow(String),
    InvalidColumn(String),
}

/// Проверява че следващия символ във входния низ `input` е точно `target`.
///
/// Ако низа наистина започва с този символ, връща остатъка от низа без него, пакетиран във
/// `Some`. Иначе, връща `None`. Примерно:
///
/// skip_next("(foo", '(') //=> Some("foo")
/// skip_next("(foo", ')') //=> None
/// skip_next("", ')')     //=> None
///
pub fn skip_next(input: &str, target: char) -> Option<&str> {
    let vec_chars = input.chars().collect::<Vec<char>>();
    if !vec_chars.is_empty() && vec_chars[0] == target {
        let (_, result) = input.split_at(vec_chars[0].len_utf8());
        return Some(result)
    }
    None
}
/// Търси следващото срещане на символа `target` в низа `input`. Връща низа до този символ и низа
/// от този символ нататък, в двойка.
///
/// Ако не намери `target`, връща оригиналния низ и празен низ като втори елемент в двойката.
///
/// take_until(" foo/bar ", '/') //=> (" foo", "/bar ")
/// take_until("foobar", '/')    //=> ("foobar", "")
///
pub fn take_until(input: &str, target: char) -> (&str, &str) {
        let vec_chars = input.chars().collect::<Vec<char>>();
        let mut curr_size = 0;
        for item in vec_chars {
            if skip_next(&item.to_string(), target) != None {
                return input.split_at(curr_size);
            }
            curr_size += item.len_utf8()    
        }
        (input,"")
}


/// Комбинация от горните две функции -- взема символите до `target` символа, и връща частта преди
/// символа и частта след, без самия символ. Ако символа го няма, връща `None`.
///
/// take_and_skip(" foo/bar ", '/') //=> Some((" foo", "bar "))
/// take_and_skip("foobar", '/')    //=> None
///
pub fn take_and_skip(input: &str, target: char) -> Option<(&str, &str)> {
    let (first_half, second_half) = take_until(input, target);
    if second_half == ""{
        return None;
    }
    let first_char = second_half.chars().collect::<Vec<char>>()[0];
    Some((first_half, skip_next(second_half,first_char).unwrap()))
}           

type Row = HashMap<String, String>;

pub struct Csv<R: BufRead> {
    pub columns: Vec<String>,
    reader: R,
    selection: Option<Box<dyn Fn(&Row) -> Result<bool, CsvError>>>,
}

impl<R: BufRead> Csv<R> {
    /// Конструира нова стойност от подадения вход. Третира се като "нещо, от което може да се чете
    /// ред по ред".
    ///
    /// Очакваме да прочетете първия ред от входа и да го обработите като заглавна част ("header").
    /// Това означава, че първия ред би трябвало да включва имена на колони, разделени със
    /// запетайки и може би празни места. Примерно:
    ///
    /// - name, age
    /// - name,age,birth date
    ///
    /// В случай, че има грешка от викане на методи на `reader`, тя би трябвало да е `io::Error`.
    /// върнете `CsvError::IO`, което опакова въпросната грешка.
    ///
    /// Ако първия ред е празен, прочитането ще ви върне 0 байта. Примерно, `read_line` връща
    /// `Ok(0)` в такъв случай. Това означава, че нямаме валиден header -- нито една колона няма,
    /// очакваме грешка `CsvError::InvalidHeader`.
    ///
    /// Ако има дублиране на колони -- две колони с едно и също име -- също върнете
    /// `CsvError::InvalidHeader`.
    ///
    /// Ако всичко е наред, върнете конструирана стойност, на която `columns` е списък с колоните,
    /// в същия ред, в който са подадени, без заобикалящите ги празни символи (използвайте
    /// `.trim()`).
    ///
    pub fn new(mut reader: R) -> Result<Self, CsvError> {
        let mut header = String::new();
        let bytes_read = reader.read_line(&mut header);
        match  bytes_read{
            Err(_) => return Err(CsvError::IO(io::Error::new(io::ErrorKind::Other, "reading from buffer error!"))),
            Ok(s) => if bytes_read.unwrap() == 0 { return Err(CsvError::InvalidHeader("Header row is missing!".to_string()))},
        };
        header = header.trim().to_string();
        let header_vec = header.split(",").map(|x| x.trim().to_string()).collect::<Vec<String>>();
        Ok(Self{columns: header_vec, reader: reader, selection: None})
    }

    /// Функцията приема следващия ред за обработка и конструира `Row` стойност
    /// (`HashMap<String, String>`) със колоните и съответсващите им стойности на този ред.
    ///
    /// Алгоритъма е горе-долу:
    ///
    /// 1. Изчистете реда с `.trim()`.
    /// 2. Очаквате, че реда ще започне със `"`, иначе връщате грешка.
    /// 3. Прочитате съдържанието от отварящата кавичка до следващата. Това е съдържанието на
    ///    стойността на текущата колона на този ред. Не го чистите от whitespace, просто го
    ///    приемате както е.
    /// 4. Ако не намерите затваряща кавичка, това е грешка.
    /// 5. Запазвате си стойността в един `Row` (`HashMap`) -- ключа е името на текущата колона,
    ///    до която сте стигнали, стойността е това, което току-що изпарсихте.
    /// 6. Ако нямате оставащи колони за обработка и нямате оставащо съдържание от реда, всичко
    ///    е ок. Връщате реда.
    /// 7. Ако нямате оставащи колони, но имате още от реда, или обратното, това е грешка.
    ///
    /// За този процес, помощните функции, които дефинирахме по-горе може да ви свършат работа.
    /// *Може* да използвате вместо тях `.split` по запетайки, но ще имаме поне няколко теста със
    /// вложени запетайки. Бихте могли и с това да се справите иначе, разбира се -- ваш избор.
    ///
    /// Внимавайте с празното пространство преди и след запетайки -- викайте `.trim()` на ключови
    /// места. Всичко в кавички се взема както е, всичко извън тях се чисти от whitespace.
    ///
    /// Всички грешки, които ще връщате, се очаква да бъдат `CsvError::InvalidRow`.
    ///
    pub fn parse_line(&mut self, line: &str) -> Result<Row, CsvError> {
        let mut splited_word;
        let mut line_to_parse = line.clone();
        let cleared_row = line.trim();
        let mut map: Row = HashMap::new();
        if skip_next(line, '"') == None{
            return Err(CsvError::InvalidRow("Missing bracket at row start!".to_string()));
        }
        for column in &self.columns{
            splited_word = take_and_skip(take_and_skip(line_to_parse, '"').unwrap().1, '"');
            if splited_word.is_none() {
                return Err(CsvError::InvalidRow("Row values are fewer than column number!".to_string()));
            };
            map.insert(column.to_string(), splited_word.unwrap().0.to_string());
            line_to_parse = splited_word.unwrap().1;
        }
        if line_to_parse != ""{ 
            return Err(CsvError::InvalidRow("Row values are than more than column number!".to_string()));
        }
        return Ok(map);
    }

    /// Подадената функция, "callback", се очаква да се запази и да се използва по-късно за
    /// филтриране -- при итерация, само редове, за които се връща `true` се очаква да се извадят.
    ///
    /// Би трябвало `callback` да се вика от `.next()` и от `.write_to()`, вижте описанията на тези
    /// методи за детайли.
    ///
    pub fn apply_selection<F>(&mut self, callback: F)
        where F: Fn(&Row) -> Result<bool, CsvError> + 'static
    {
        self.selection = Some(Box::new(callback));
    }

    /// Извикването на този метод консумира CSV-то и записва филтрираното съдържание в подадената
    /// `Write` стойност. Вижте по-долу за пример и детайли.
    ///
    /// Грешките, които се връщат са грешките, които идват от използваните други методи, плюс
    /// грешките от писане във `writer`-а, опаковани в `CsvError::IO`.
    ///
    /// В зависимост от това как си имплементирате метода, `mut` може би няма да ви трябва за
    /// `self` -- ако имате warning-и, просто го махнете.
    ///
    pub fn write_to<W: Write>(mut self, mut writer: W) -> Result<(), CsvError> {
        let mut row;
        let mut line: String = String::from("");
        let mut headers = self.columns.join(", ");
        headers.push_str("\n");
        let mut formatted_parsed_line = headers;
        while self.reader.read_line(&mut line).unwrap() != 0{
            row = match self.parse_line(&line.trim()) {
                Err(e) => return Err(e),
                Ok(val) => val,
            };
            for column in &self.columns{
                formatted_parsed_line.push_str(&format!(r#""{}", "#, &row[column]));
            }
            formatted_parsed_line.pop();
            formatted_parsed_line.pop();
            formatted_parsed_line.push_str("\n");
            match write!(writer, "{}",formatted_parsed_line){
                Err(_) => return Err(CsvError::IO(io::Error::new(io::ErrorKind::Other, "writing to buffer error!"))),
                Ok(_) => (),
            };
            formatted_parsed_line = String::from("");
            line = String::from("");
        }
        return Ok(());
    }
}

impl<R: BufRead> Iterator for Csv<R> {
    type Item = Result<Row, CsvError>;

    /// Итерацията се състои от няколко стъпки:
    ///
    /// 1. Прочитаме следващия ред от входа:
    ///     -> Ако има грешка при четене, връщаме Some(CsvError::IO(...))
    ///     -> Ако успешно се прочетат 0 байта, значи сме на края на входа, и няма какво повече да
    ///        четем -- връщаме `None`
    ///     -> Иначе, имаме успешно прочетен ред, продължаваме напред
    /// 2. Опитваме се да обработим прочетения ред със `parse_line`:
    ///     -> Ако има грешка при парсене, връщаме Some(CsvError-а, който се връща от `parse_line`)
    ///     -> Ако успешно извикаме `parse_line`, вече имаме `Row` стойност.
    /// 3. Проверяваме дали този ред изпълнява условието, запазено от `apply_selection`:
    ///     -> Ако условието върне грешка, връщаме тази грешка опакована във `Some`.
    ///     -> Ако условието върне Ok(false), *не* връщаме този ред, а пробваме следващия (обратно
    ///        към стъпка 1)
    ///     -> При Ok(true), връщаме този ред, опакован във `Some`
    ///
    /// Да, тази функция връща `Option<Result<...>>` :). `Option` защото може да има, може да няма
    /// следващ ред, `Result` защото четенето на реда (от примерно файл) може да не сработи.
    ///
    fn next(&mut self) -> Option<Self::Item> {
        let mut row;
        let mut line: String = String::from("");
        let mut read_bytes =  match self.reader.read_line(&mut line) {
            Err(_) => return Some(Err(CsvError::IO(io::Error::new(io::ErrorKind::Other, "reading from buffer error!")))),
            Ok(val) => val,
        };
        while read_bytes != 0 {
            row = match self.parse_line(&line.trim()) {
                Err(e) => return Some(Err(e)),
                Ok(val) => val,
            };
            if !self.selection.is_none() {
                match self.selection.as_ref().unwrap()(&row){
                    Err(e) => return Some(Err(e)),
                    Ok(false) => (),
                    Ok(true) => return Some(Ok(row)),
                }
            }
            else {
                return Some(Ok(row));
            }
            line = String::from("");
            read_bytes =   match self.reader.read_line(&mut line) {
                Err(_) => return Some(Err(CsvError::IO(io::Error::new(io::ErrorKind::Other, "reading from buffer error!")))),
                Ok(val) => val,
            };
        }
        return None;
    }
}