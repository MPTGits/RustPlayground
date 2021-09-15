/// Вход: променлива `n`, която описва броя елементи, които ще генерираме в резултата.
///
/// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
///
/// - String със съдържание "Fizz" ако числото се дели на 3, но не на 5
/// - String със съдържание "Buzz" ако числото се дели на 5, но не на 3
/// - String със съдържание "Fizzbuzz" ако числото се дели и на 3, и на 5
/// - Числото конвертирано до низ, във всички други случаи
///
/// Тоест, във `fizzbuzz(3)`, първия елемент ще бъде `String::from("1")`, втория
/// `String::from("2")`, последния `String::from("Fizz")`.
///
/// Ако `n` е 0, очакваме празен вектор за резултат.
///
pub fn fizzbuzz(n: usize) -> Vec<String> {
    let mut vec: Vec<String> = Vec::new();
    for num in 1..n+1 {
    	if num % 15 == 0 {
    		vec.push(String::from("Fizzbuzz"))
    	}
    	else if num % 3 == 0 {
    		vec.push(String::from("Fizz"))
    	}
    	else if num % 5 == 0 {
    		vec.push(String::from("Buzz"))
    	}
    	else {
    		vec.push(num.to_string())
    	}
    }
    vec
  }

/// Вход:
/// - променлива `n`, която описва броя елементи, които ще генерираме в резултата.
/// - променливи `k1` и `k2`, които са двата делителя, които ще използваме за заместване.
///
/// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
///
/// - String със съдържание "Fizz" ако числото се дели на k1, но не на k2
/// - String със съдържание "Buzz" ако числото се дели на k2, но не на k1
/// - String със съдържание "Fizzbuzz" ако числото се дели и на k1, и на k2
/// - Числото конвертирано до низ, във всички други случаи
///
/// Ако `n` е 0, очакваме празен вектор за резултат.
/// Ако `k1` или `k2` са 0 или 1, очакваме функцията да panic-не с каквото съобщение изберете.
///
pub fn custom_buzz(n: usize, k1: u8, k2: u8) -> Vec<String> {
    let fizzbuzzer = FizzBuzzer {
    	k1: k1,
    	k2: k2,
    	labels: [
                String::from("Fizz"),
                String::from("Buzz"),
                String::from("Fizzbuzz")
            ]
    };
    fizzbuzzer.take(n)
  }


/// Параметри:
/// - полета `k1` и `k2`, които са двата делителя, които ще използваме за заместване.
/// - поле `labels`, които са трите етикета, които съответстват на коефициентите
///
pub struct FizzBuzzer {
    pub k1: u8,
    pub k2: u8,
    pub labels: [String; 3],
}

impl FizzBuzzer {
    /// За всяко число от 1 до `n` включително, искаме съответстващия елемент в резултата да е:
    ///
    /// - Първия String от полето `labels` ако числото се дели на k1, но не на k2
    /// - Втория String от полето `labels` ако числото се дели на k2, но не на k1
    /// - Третия String от полето `labels` ако числото се дели и на k1, и на k2
    /// - Числото конвертирано до низ, във всички други случаи
    ///
    /// Ако `n` е 0, очакваме празен вектор за резултат.
    /// Ако `k1` или `k2` са 0 или 1, очакваме функцията да panic-не с каквото съобщение изберете.
    ///
    pub fn take(&self, n: usize) -> Vec<String> {
        let mut vec: Vec<String> = Vec::new();
    	if (self.k1 == 0 || self.k1 == 1) || (self.k2 == 0 || self.k2 == 1){
    		panic!("Value for delimeters must not be 0 or 1")
    	}	
    	for num in 1..n+1 {
    		if num % ((self.k1*self.k2) as usize) == 0 {
    			vec.push(String::from(&self.labels[2]))
    		}
    		else if num % (self.k1 as usize) == 0 {
    			vec.push(String::from(&self.labels[0]))
    		}
    		else if num % (self.k2 as usize) == 0 {
    			vec.push(String::from(&self.labels[1]))
    		}
    		else {
    			vec.push(num.to_string())
    		}
    	}
    	vec
  	}

    /// Параметъра `index` указва кой етикет от полето `labels` променяме, от 0 до 2. Ако подадения
    /// `index` е извън тези рамки, очакваме функцията да panic-не.
    ///
    /// Стойността `value` е низа, който ще сложим на този индекс в полето `labels`.
    ///
    pub fn change_label(&mut self, index: usize, value: &String) {
        if index > 2 || index < 0{
        	panic!("Invalid index number")
        }
        self.labels[index] = value.clone()
    }
}