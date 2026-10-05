// EXPECT: line=6 rule=identifier-style
// EXPECT: line=10 rule=identifier-style
// #79 control: knowing that a codec member is a value must not silence the
// value rule. An UpperCamelCase alias of a plain number and an UpperCamelCase
// alias of the codec instance are both values and both need snake_case.
const PaletteSize: usize = 256;

const tick_ms: i32 = 100;

const Encoder = @import("std").base64.standard.Encoder;
