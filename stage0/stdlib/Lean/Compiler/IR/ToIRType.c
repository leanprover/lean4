// Lean compiler output
// Module: Lean.Compiler.IR.ToIRType
// Imports: public import Lean.Compiler.IR.Format public import Lean.Compiler.LCNF.MonoTypes
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_nameToIRType_spec__0(lean_object*);
static const lean_string_object l_Lean_IR_nameToIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.IR.ToIRType"};
static const lean_object* l_Lean_IR_nameToIRType___closed__0 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__0_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.IR.nameToIRType"};
static const lean_object* l_Lean_IR_nameToIRType___closed__1 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__1_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_IR_nameToIRType___closed__2 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_IR_nameToIRType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_nameToIRType___closed__3;
static const lean_string_object l_Lean_IR_nameToIRType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_IR_nameToIRType___closed__4 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__4_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_IR_nameToIRType___closed__5 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__5_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_IR_nameToIRType___closed__6 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__6_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_IR_nameToIRType___closed__7 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__7_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_IR_nameToIRType___closed__8 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__8_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_IR_nameToIRType___closed__9 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__9_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l_Lean_IR_nameToIRType___closed__10 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__10_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l_Lean_IR_nameToIRType___closed__11 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__11_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l_Lean_IR_nameToIRType___closed__12 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__12_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l_Lean_IR_nameToIRType___closed__13 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__13_value;
static const lean_string_object l_Lean_IR_nameToIRType___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l_Lean_IR_nameToIRType___closed__14 = (const lean_object*)&l_Lean_IR_nameToIRType___closed__14_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType___boxed(lean_object*);
static const lean_string_object l_Lean_IR_toIRType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.IR.toIRType"};
static const lean_object* l_Lean_IR_toIRType___closed__0 = (const lean_object*)&l_Lean_IR_toIRType___closed__0_value;
static lean_once_cell_t l_Lean_IR_toIRType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IR_toIRType___closed__1;
static const lean_string_object l_Lean_IR_toIRType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_IR_toIRType___closed__2 = (const lean_object*)&l_Lean_IR_toIRType___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIRType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_IR_nameToIRType_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_nameToIRType___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__1));
x_5 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__4));
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__5));
x_10 = lean_string_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__6));
x_12 = lean_string_dec_eq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__7));
x_14 = lean_string_dec_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__8));
x_16 = lean_string_dec_eq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__9));
x_18 = lean_string_dec_eq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__10));
x_20 = lean_string_dec_eq(x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__11));
x_22 = lean_string_dec_eq(x_6, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__12));
x_24 = lean_string_dec_eq(x_6, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__13));
x_26 = lean_string_dec_eq(x_6, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__14));
x_28 = lean_string_dec_eq(x_6, x_27);
if (x_28 == 0)
{
goto block_4;
}
else
{
lean_object* x_29; 
x_29 = lean_box(13);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_box(12);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_box(8);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_box(7);
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = lean_box(6);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_box(4);
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = lean_box(3);
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = lean_box(2);
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = lean_box(1);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = lean_box(9);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_box(0);
return x_39;
}
}
else
{
goto block_4;
}
}
else
{
goto block_4;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_IR_nameToIRType___closed__3, &l_Lean_IR_nameToIRType___closed__3_once, _init_l_Lean_IR_nameToIRType___closed__3);
x_3 = l_panic___at___00Lean_IR_nameToIRType_spec__0(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_nameToIRType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_nameToIRType(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_toIRType___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(49u);
x_4 = ((lean_object*)(l_Lean_IR_toIRType___closed__0));
x_5 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIRType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__4));
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__5));
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__6));
x_14 = lean_string_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__7));
x_16 = lean_string_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__8));
x_18 = lean_string_dec_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__9));
x_20 = lean_string_dec_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l_Lean_IR_toIRType___closed__2));
x_22 = lean_string_dec_eq(x_8, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__10));
x_24 = lean_string_dec_eq(x_8, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__11));
x_26 = lean_string_dec_eq(x_8, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__12));
x_28 = lean_string_dec_eq(x_8, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__13));
x_30 = lean_string_dec_eq(x_8, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l_Lean_IR_nameToIRType___closed__14));
x_32 = lean_string_dec_eq(x_8, x_31);
if (x_32 == 0)
{
goto block_4;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_33; 
x_33 = lean_box(13);
return x_33;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_34; 
x_34 = lean_box(12);
return x_34;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_35; 
x_35 = lean_box(8);
return x_35;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_36; 
x_36 = lean_box(7);
return x_36;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_37; 
x_37 = lean_box(6);
return x_37;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_38; 
x_38 = lean_box(5);
return x_38;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_39; 
x_39 = lean_box(4);
return x_39;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_40; 
x_40 = lean_box(3);
return x_40;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_41; 
x_41 = lean_box(2);
return x_41;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_42; 
x_42 = lean_box(1);
return x_42;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_43; 
x_43 = lean_box(9);
return x_43;
}
else
{
goto block_4;
}
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
return x_44;
}
else
{
goto block_4;
}
}
}
else
{
goto block_4;
}
}
else
{
goto block_4;
}
}
else
{
goto block_4;
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_IR_toIRType___closed__1, &l_Lean_IR_toIRType___closed__1_once, _init_l_Lean_IR_toIRType___closed__1);
x_3 = l_panic___at___00Lean_IR_nameToIRType_spec__0(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIRType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_toIRType(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
