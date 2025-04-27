use ark_std::fmt::Debug;
use std::vec;

// Utility function (can stay here or move elsewhere if more appropriate)
pub fn print_collection<T, F>(collection: &[Vec<T>], get_val_fn: F)
where
    T: Debug, // Ensure T implements the Debug trait
    F: Fn(&T) -> u128,  // get_val_fn should return a value that can be printed
{
    for (i, row) in collection.iter().enumerate() {
        print!("row_{}: ", i);
        for col in row.iter() {
            print!("{:?} ", get_val_fn(col)); // Print the value of the struct
        }
        println!();
    }
}

pub fn bit_decompose(input: usize, input_bit_len: usize, slice_len: usize) -> Vec<usize> {
    let max_input = (1 as usize) << input_bit_len;
    assert!(input < max_input);
    assert!(slice_len <= input_bit_len);
    assert!(slice_len != 0);
    assert!(input_bit_len % slice_len == 0);

    let output_bit_mask = ((1 as usize) << slice_len) - 1;
    let output_len = input_bit_len / slice_len;
    let mut output = Vec::with_capacity(output_len);

    for i in 0..output_len {
        let offset = (output_len - i - 1) * slice_len;
        let output_val = (input >> offset) & output_bit_mask;
        output.push(output_val);
    }
    output
}

pub fn bit_extend(
    input: usize,
    input_bit_len: usize,
    source_slice_len: usize,
    target_slice_len: usize,
) -> usize {
    let input_bits = bit_decompose(input, input_bit_len, source_slice_len);
    let mut output: usize = 0;
    let mut offset = target_slice_len - source_slice_len;
    for i in 0..input_bits.len() {
        output += input_bits[input_bits.len() - i - 1] << offset;
        offset += target_slice_len;
    }
    output
}

pub fn bit_extend_and_insert(
    input: usize,
    input_bit_len: usize,
    value_to_insert: usize,
    value_to_insert_bit_len: usize,
    source_slice_len: usize,
    target_slice_len: usize,
) -> usize {
    assert!(target_slice_len > source_slice_len);

    let value_to_insert_bits = bit_decompose(
        value_to_insert,
        value_to_insert_bit_len,
        target_slice_len - source_slice_len,
    );

    let mut input_bits: Vec<usize> = vec![0; value_to_insert_bits.len()];
    if source_slice_len != 0 {
        input_bits = bit_decompose(input, input_bit_len, source_slice_len);
    }
    assert_eq!(input_bits.len(), value_to_insert_bits.len());
    let mut output: usize = 0;
    let mut insertion_output: usize = 0;
    let mut offset: usize = target_slice_len - source_slice_len;
    let mut insertion_offset: usize = 0;
    for i in 0..input_bits.len() {
        let idx = input_bits.len() - i - 1;
        output += input_bits[idx] << offset;
        offset += target_slice_len;
        insertion_output += value_to_insert_bits[idx] << insertion_offset;
        insertion_offset += target_slice_len;
    }
    output + insertion_output
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bit_decompose() {
        // (001)(010)(111)(110)(001)
        let value: usize = 5617;
        let bits = bit_decompose(value, 15, 3);
        assert_eq!(bits.len(), 5);
        assert_eq!(bits[0], 1);
        assert_eq!(bits[1], 2);
        assert_eq!(bits[2], 7);
        assert_eq!(bits[3], 6);
        assert_eq!(bits[4], 1);
    }

    #[test]
    fn test_bit_extend() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let value: usize = 5617;
        // 4363923472  =>  (001[0000])(010[0000])(111[0000])(110[0000])(001[0000])
        let output = bit_extend(value, 15, 3, 7);
        assert_eq!(output, 4363923472);
    }

    #[test]
    fn test_bit_extend_and_insert() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let value: usize = 5617;
        // 316679 => (0100)(1101)(0101)(0000)(0111)
        let value_to_insert = 316679;
        // 5465010199  =>  (001[0100])(010[1101])(111[0101])(110[0000])(001[0111])
        let output = bit_extend_and_insert(value, 15, value_to_insert, 20, 3, 7);
        assert_eq!(output, 5465010199);
    }
} 