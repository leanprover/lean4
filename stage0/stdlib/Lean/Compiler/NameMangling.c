// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: public import Lean.Setup import Init.Data.String.TakeDrop import Init.Data.UInt.Lemmas import Init.Omega import Init.Data.String.Lemmas.FindPos
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
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
uint32_t lean_uint32_land(uint32_t, uint32_t);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_U"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_u"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "__"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Internal_mangle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Internal_mangle___closed__0 = (const lean_object*)&l_String_Internal_mangle___closed__0_value;
LEAN_EXPORT lean_object* l_String_Internal_mangle(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_mangle___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "00"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_00"};
static const lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2 = (const lean_object*)&l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkMangledBoxedName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "___boxed"};
static const lean_object* l_Lean_mkMangledBoxedName___closed__0 = (const lean_object*)&l_Lean_mkMangledBoxedName___closed__0_value;
static const lean_string_object l_Lean_mkMangledBoxedName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_00__boxed"};
static const lean_object* l_Lean_mkMangledBoxedName___closed__1 = (const lean_object*)&l_Lean_mkMangledBoxedName___closed__1_value;
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkModuleInitializationPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "runtime_"};
static const lean_object* l_Lean_mkModuleInitializationPrefix___closed__0 = (const lean_object*)&l_Lean_mkModuleInitializationPrefix___closed__0_value;
static const lean_string_object l_Lean_mkModuleInitializationPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta_"};
static const lean_object* l_Lean_mkModuleInitializationPrefix___closed__1 = (const lean_object*)&l_Lean_mkModuleInitializationPrefix___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix___boxed(lean_object*);
static const lean_string_object l_Lean_mkModuleInitializationFunctionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initialize_"};
static const lean_object* l_Lean_mkModuleInitializationFunctionName___closed__0 = (const lean_object*)&l_Lean_mkModuleInitializationFunctionName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkPackageSymbolPrefix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "l_"};
static const lean_object* l_Lean_mkPackageSymbolPrefix___closed__0 = (const lean_object*)&l_Lean_mkPackageSymbolPrefix___closed__0_value;
static const lean_string_object l_Lean_mkPackageSymbolPrefix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lp_"};
static const lean_object* l_Lean_mkPackageSymbolPrefix___closed__1 = (const lean_object*)&l_Lean_mkPackageSymbolPrefix___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object*);
uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t v_n_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 10;
v___x_3_ = lean_uint32_dec_lt(v_n_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint32_t v___x_4_; uint32_t v___x_5_; 
v___x_4_ = 87;
v___x_5_ = lean_uint32_add(v_n_1_, v___x_4_);
return v___x_5_;
}
else
{
uint32_t v___x_6_; uint32_t v___x_7_; 
v___x_6_ = 48;
v___x_7_ = lean_uint32_add(v_n_1_, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_1_ = stack[0].m_num;
uint32_t v_res_8_;
v_res_8_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_1_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object* v_n_9_){
_start:
{
uint32_t v_n_boxed_10_; uint32_t v_res_11_; lean_object* v_r_12_; 
v_n_boxed_10_ = lean_unbox_uint32(v_n_9_);
lean_dec(v_n_9_);
v_res_11_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_boxed_10_);
v_r_12_ = lean_box_uint32(v_res_11_);
return v_r_12_;
}
}
uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t v_n_13_, lean_object* v_h_14_){
_start:
{
uint32_t v___x_15_; 
v___x_15_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_13_);
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__String_digitChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_n_13_ = stack[0].m_num;
uint32_t v_res_16_;
v_res_16_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar(v_n_13_, lean_box(0));
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object* v_n_17_, lean_object* v_h_18_){
_start:
{
uint32_t v_n_boxed_19_; uint32_t v_res_20_; lean_object* v_r_21_; 
v_n_boxed_19_ = lean_unbox_uint32(v_n_17_);
lean_dec(v_n_17_);
v_res_20_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar(v_n_boxed_19_, v_h_18_);
v_r_21_ = lean_box_uint32(v_res_20_);
return v_r_21_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object* v_n_22_, uint32_t v_val_23_, lean_object* v_s_24_){
_start:
{
lean_object* v_zero_25_; uint8_t v_isZero_26_; 
v_zero_25_ = lean_unsigned_to_nat(0u);
v_isZero_26_ = lean_nat_dec_eq(v_n_22_, v_zero_25_);
if (v_isZero_26_ == 1)
{
lean_dec(v_n_22_);
return v_s_24_;
}
else
{
lean_object* v_one_27_; lean_object* v_n_28_; uint32_t v___x_29_; uint32_t v___x_30_; uint32_t v___x_31_; uint32_t v___x_32_; uint32_t v___x_33_; uint32_t v_i_34_; uint32_t v___x_35_; lean_object* v___x_36_; 
v_one_27_ = lean_unsigned_to_nat(1u);
v_n_28_ = lean_nat_sub(v_n_22_, v_one_27_);
lean_dec(v_n_22_);
v___x_29_ = lean_uint32_of_nat(v_n_28_);
v___x_30_ = 2;
v___x_31_ = lean_uint32_shift_left(v___x_29_, v___x_30_);
v___x_32_ = lean_uint32_shift_right(v_val_23_, v___x_31_);
v___x_33_ = 15;
v_i_34_ = lean_uint32_land(v___x_32_, v___x_33_);
v___x_35_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_i_34_);
v___x_36_ = lean_string_push(v_s_24_, v___x_35_);
v_n_22_ = v_n_28_;
v_s_24_ = v___x_36_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__String_pushHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_22_ = stack[0].m_obj;
uint32_t v_val_23_ = stack[1].m_num;
lean_object* v_s_24_ = stack[2].m_obj;
lean_object* v_res_38_;
v_res_38_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v_n_22_, v_val_23_, v_s_24_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object* v_n_39_, lean_object* v_val_40_, lean_object* v_s_41_){
_start:
{
uint32_t v_val_boxed_42_; lean_object* v_res_43_; 
v_val_boxed_42_ = lean_unbox_uint32(v_val_40_);
lean_dec(v_val_40_);
v_res_43_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v_n_39_, v_val_boxed_42_, v_s_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* v_s_48_, lean_object* v_pos_49_, lean_object* v_r_50_){
_start:
{
lean_object* v___x_51_; uint8_t v_decide_52_; 
v___x_51_ = lean_string_utf8_byte_size(v_s_48_);
v_decide_52_ = lean_nat_dec_eq(v_pos_49_, v___x_51_);
if (v_decide_52_ == 0)
{
uint32_t v_c_53_; lean_object* v_pos_54_; uint32_t v___x_94_; uint8_t v___x_95_; 
v_c_53_ = lean_string_utf8_get_fast(v_s_48_, v_pos_49_);
v_pos_54_ = lean_string_utf8_next_fast(v_s_48_, v_pos_49_);
lean_dec(v_pos_49_);
v___x_94_ = 65;
v___x_95_ = lean_uint32_dec_le(v___x_94_, v_c_53_);
if (v___x_95_ == 0)
{
goto v___jp_89_;
}
else
{
uint32_t v___x_96_; uint8_t v___x_97_; 
v___x_96_ = 90;
v___x_97_ = lean_uint32_dec_le(v_c_53_, v___x_96_);
if (v___x_97_ == 0)
{
goto v___jp_89_;
}
else
{
goto v___jp_81_;
}
}
v___jp_55_:
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 95;
v___x_57_ = lean_uint32_dec_eq(v_c_53_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = lean_uint32_to_nat(v_c_53_);
v___x_59_ = lean_unsigned_to_nat(256u);
v___x_60_ = lean_nat_dec_lt(v___x_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(65536u);
v___x_62_ = lean_nat_dec_lt(v___x_58_, v___x_61_);
lean_dec(v___x_58_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_unsigned_to_nat(8u);
v___x_64_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0));
v___x_65_ = lean_string_append(v_r_50_, v___x_64_);
v___x_66_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_63_, v_c_53_, v___x_65_);
v_pos_49_ = v_pos_54_;
v_r_50_ = v___x_66_;
goto _start;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_unsigned_to_nat(4u);
v___x_69_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1));
v___x_70_ = lean_string_append(v_r_50_, v___x_69_);
v___x_71_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_68_, v_c_53_, v___x_70_);
v_pos_49_ = v_pos_54_;
v_r_50_ = v___x_71_;
goto _start;
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v___x_58_);
v___x_73_ = lean_unsigned_to_nat(2u);
v___x_74_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2));
v___x_75_ = lean_string_append(v_r_50_, v___x_74_);
v___x_76_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_73_, v_c_53_, v___x_75_);
v_pos_49_ = v_pos_54_;
v_r_50_ = v___x_76_;
goto _start;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_79_ = lean_string_append(v_r_50_, v___x_78_);
v_pos_49_ = v_pos_54_;
v_r_50_ = v___x_79_;
goto _start;
}
}
v___jp_81_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_string_push(v_r_50_, v_c_53_);
v_pos_49_ = v_pos_54_;
v_r_50_ = v___x_82_;
goto _start;
}
v___jp_84_:
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 48;
v___x_86_ = lean_uint32_dec_le(v___x_85_, v_c_53_);
if (v___x_86_ == 0)
{
goto v___jp_55_;
}
else
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 57;
v___x_88_ = lean_uint32_dec_le(v_c_53_, v___x_87_);
if (v___x_88_ == 0)
{
goto v___jp_55_;
}
else
{
goto v___jp_81_;
}
}
}
v___jp_89_:
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 97;
v___x_91_ = lean_uint32_dec_le(v___x_90_, v_c_53_);
if (v___x_91_ == 0)
{
goto v___jp_84_;
}
else
{
uint32_t v___x_92_; uint8_t v___x_93_; 
v___x_92_ = 122;
v___x_93_ = lean_uint32_dec_le(v_c_53_, v___x_92_);
if (v___x_93_ == 0)
{
goto v___jp_84_;
}
else
{
goto v___jp_81_;
}
}
}
}
else
{
lean_dec(v_pos_49_);
return v_r_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object* v_s_98_, lean_object* v_pos_99_, lean_object* v_r_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_98_, v_pos_99_, v_r_100_);
lean_dec_ref(v_s_98_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle(lean_object* v_s_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_106_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_103_, v___x_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle___boxed(lean_object* v_s_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_String_Internal_mangle(v_s_107_);
lean_dec_ref(v_s_107_);
return v_res_108_;
}
}
uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_zero_112_; uint8_t v_isZero_113_; 
v_zero_112_ = lean_unsigned_to_nat(0u);
v_isZero_113_ = lean_nat_dec_eq(v_x_109_, v_zero_112_);
if (v_isZero_113_ == 1)
{
lean_dec(v_x_111_);
lean_dec(v_x_109_);
return v_isZero_113_;
}
else
{
lean_object* v___x_114_; uint8_t v_decide_115_; 
v___x_114_ = lean_string_utf8_byte_size(v_x_110_);
v_decide_115_ = lean_nat_dec_eq(v_x_111_, v___x_114_);
if (v_decide_115_ == 0)
{
lean_object* v_one_116_; lean_object* v_n_117_; uint32_t v_ch_121_; uint32_t v___x_127_; uint8_t v___x_128_; 
v_one_116_ = lean_unsigned_to_nat(1u);
v_n_117_ = lean_nat_sub(v_x_109_, v_one_116_);
lean_dec(v_x_109_);
v_ch_121_ = lean_string_utf8_get_fast(v_x_110_, v_x_111_);
v___x_127_ = 48;
v___x_128_ = lean_uint32_dec_le(v___x_127_, v_ch_121_);
if (v___x_128_ == 0)
{
goto v___jp_122_;
}
else
{
uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_129_ = 57;
v___x_130_ = lean_uint32_dec_le(v_ch_121_, v___x_129_);
if (v___x_130_ == 0)
{
goto v___jp_122_;
}
else
{
goto v___jp_118_;
}
}
v___jp_118_:
{
lean_object* v___x_119_; 
v___x_119_ = lean_string_utf8_next_fast(v_x_110_, v_x_111_);
lean_dec(v_x_111_);
v_x_109_ = v_n_117_;
v_x_111_ = v___x_119_;
goto _start;
}
v___jp_122_:
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 97;
v___x_124_ = lean_uint32_dec_le(v___x_123_, v_ch_121_);
if (v___x_124_ == 0)
{
lean_dec(v_n_117_);
lean_dec(v_x_111_);
return v_decide_115_;
}
else
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 102;
v___x_126_ = lean_uint32_dec_le(v_ch_121_, v___x_125_);
if (v___x_126_ == 0)
{
lean_dec(v_n_117_);
lean_dec(v_x_111_);
return v_decide_115_;
}
else
{
goto v___jp_118_;
}
}
}
}
else
{
lean_dec(v_x_111_);
lean_dec(v_x_109_);
return v_isZero_113_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_109_ = stack[0].m_obj;
lean_object* v_x_110_ = stack[1].m_obj;
lean_object* v_x_111_ = stack[2].m_obj;
uint8_t v_res_131_;
v_res_131_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_109_, v_x_110_, v_x_111_);
stack->m_num = v_res_131_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_132_, v_x_133_, v_x_134_);
lean_dec_ref(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t v_c_137_){
_start:
{
uint32_t v___x_149_; uint8_t v___x_150_; 
v___x_149_ = 48;
v___x_150_ = lean_uint32_dec_le(v___x_149_, v_c_137_);
if (v___x_150_ == 0)
{
goto v___jp_138_;
}
else
{
uint32_t v___x_151_; uint8_t v___x_152_; 
v___x_151_ = 57;
v___x_152_ = lean_uint32_dec_le(v_c_137_, v___x_151_);
if (v___x_152_ == 0)
{
goto v___jp_138_;
}
else
{
uint32_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_uint32_sub(v_c_137_, v___x_149_);
v___x_154_ = lean_uint32_to_nat(v___x_153_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
v___jp_138_:
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 97;
v___x_140_ = lean_uint32_dec_le(v___x_139_, v_c_137_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 102;
v___x_143_ = lean_uint32_dec_le(v_c_137_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
uint32_t v___x_145_; uint32_t v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_145_ = 87;
v___x_146_ = lean_uint32_sub(v_c_137_, v___x_145_);
v___x_147_ = lean_uint32_to_nat(v___x_146_);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_137_ = stack[0].m_num;
lean_object* v_res_156_;
v_res_156_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_137_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object* v_c_157_){
_start:
{
uint32_t v_c_boxed_158_; lean_object* v_res_159_; 
v_c_boxed_158_ = lean_unbox_uint32(v_c_157_);
lean_dec(v_c_157_);
v_res_159_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_boxed_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object* v_k_160_, lean_object* v_s_161_, lean_object* v_p_162_, lean_object* v_acc_163_){
_start:
{
lean_object* v_zero_164_; uint8_t v_isZero_165_; 
v_zero_164_ = lean_unsigned_to_nat(0u);
v_isZero_165_ = lean_nat_dec_eq(v_k_160_, v_zero_164_);
if (v_isZero_165_ == 1)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_k_160_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_p_162_);
lean_ctor_set(v___x_166_, 1, v_acc_163_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; uint8_t v_decide_169_; 
v___x_168_ = lean_string_utf8_byte_size(v_s_161_);
v_decide_169_ = lean_nat_dec_eq(v_p_162_, v___x_168_);
if (v_decide_169_ == 0)
{
uint32_t v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_string_utf8_get_fast(v_s_161_, v_p_162_);
v___x_171_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v___x_170_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v___x_172_; 
lean_dec(v_acc_163_);
lean_dec(v_p_162_);
lean_dec(v_k_160_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v_val_173_; lean_object* v_one_174_; lean_object* v_n_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_val_173_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_val_173_);
lean_dec_ref_known(v___x_171_, 1);
v_one_174_ = lean_unsigned_to_nat(1u);
v_n_175_ = lean_nat_sub(v_k_160_, v_one_174_);
lean_dec(v_k_160_);
v___x_176_ = lean_string_utf8_next_fast(v_s_161_, v_p_162_);
lean_dec(v_p_162_);
v___x_177_ = lean_unsigned_to_nat(4u);
v___x_178_ = lean_nat_shiftl(v_acc_163_, v___x_177_);
lean_dec(v_acc_163_);
v___x_179_ = lean_nat_lor(v___x_178_, v_val_173_);
lean_dec(v_val_173_);
lean_dec(v___x_178_);
v_k_160_ = v_n_175_;
v_p_162_ = v___x_176_;
v_acc_163_ = v___x_179_;
goto _start;
}
}
else
{
lean_object* v___x_181_; 
lean_dec(v_acc_163_);
lean_dec(v_p_162_);
lean_dec(v_k_160_);
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object* v_k_182_, lean_object* v_s_183_, lean_object* v_p_184_, lean_object* v_acc_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v_k_182_, v_s_183_, v_p_184_, v_acc_185_);
lean_dec_ref(v_s_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object* v_n_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
lean_object* v_zero_190_; uint8_t v_isZero_191_; 
v_zero_190_ = lean_unsigned_to_nat(0u);
v_isZero_191_ = lean_nat_dec_eq(v_n_187_, v_zero_190_);
if (v_isZero_191_ == 1)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_h__2_189_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_apply_1(v_h__1_188_, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v_one_194_; lean_object* v_n_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_188_);
v_one_194_ = lean_unsigned_to_nat(1u);
v_n_195_ = lean_nat_sub(v_n_187_, v_one_194_);
v___x_196_ = lean_apply_1(v_h__2_189_, v_n_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object* v_n_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(v_n_197_, v_h__1_198_, v_h__2_199_);
lean_dec(v_n_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object* v_motive_201_, lean_object* v_n_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
lean_object* v_zero_205_; uint8_t v_isZero_206_; 
v_zero_205_ = lean_unsigned_to_nat(0u);
v_isZero_206_ = lean_nat_dec_eq(v_n_202_, v_zero_205_);
if (v_isZero_206_ == 1)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v_h__2_204_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_1(v_h__1_203_, v___x_207_);
return v___x_208_;
}
else
{
lean_object* v_one_209_; lean_object* v_n_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_203_);
v_one_209_ = lean_unsigned_to_nat(1u);
v_n_210_ = lean_nat_sub(v_n_202_, v_one_209_);
v___x_211_ = lean_apply_1(v_h__2_204_, v_n_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* v_motive_212_, lean_object* v_n_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(v_motive_212_, v_n_213_, v_h__1_214_, v_h__2_215_);
lean_dec(v_n_213_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_h__1_218_);
v___x_220_ = lean_box(0);
v___x_221_ = lean_apply_1(v_h__2_219_, v___x_220_);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_223_; 
lean_dec(v_h__2_219_);
v_val_222_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v_x_217_, 1);
v___x_223_ = lean_apply_1(v_h__1_218_, v_val_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* v_motive_224_, lean_object* v_x_225_, lean_object* v_h__1_226_, lean_object* v_h__2_227_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_h__1_226_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_apply_1(v_h__2_227_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
lean_dec(v_h__2_227_);
v_val_230_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v_x_225_, 1);
v___x_231_ = lean_apply_1(v_h__1_226_, v_val_230_);
return v___x_231_;
}
}
}
uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* v_s_232_, lean_object* v_p_233_){
_start:
{
lean_object* v___x_234_; uint8_t v_decide_235_; 
v___x_234_ = lean_string_utf8_byte_size(v_s_232_);
v_decide_235_ = lean_nat_dec_eq(v_p_233_, v___x_234_);
if (v_decide_235_ == 0)
{
uint32_t v_b_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v_b_236_ = lean_string_utf8_get_fast(v_s_232_, v_p_233_);
v___x_237_ = 95;
v___x_238_ = lean_uint32_dec_eq(v_b_236_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 120;
v___x_240_ = lean_uint32_dec_eq(v_b_236_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 117;
v___x_242_ = lean_uint32_dec_eq(v_b_236_, v___x_241_);
if (v___x_242_ == 0)
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 85;
v___x_244_ = lean_uint32_dec_eq(v_b_236_, v___x_243_);
if (v___x_244_ == 0)
{
uint32_t v___x_245_; uint8_t v___x_246_; 
lean_dec(v_p_233_);
v___x_245_ = 48;
v___x_246_ = lean_uint32_dec_le(v___x_245_, v_b_236_);
if (v___x_246_ == 0)
{
return v___x_244_;
}
else
{
uint32_t v___x_247_; uint8_t v___x_248_; 
v___x_247_ = 57;
v___x_248_ = lean_uint32_dec_le(v_b_236_, v___x_247_);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(8u);
v___x_250_ = lean_string_utf8_next_fast(v_s_232_, v_p_233_);
lean_dec(v_p_233_);
v___x_251_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_249_, v_s_232_, v___x_250_);
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(4u);
v___x_253_ = lean_string_utf8_next_fast(v_s_232_, v_p_233_);
lean_dec(v_p_233_);
v___x_254_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_252_, v_s_232_, v___x_253_);
return v___x_254_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(2u);
v___x_256_ = lean_string_utf8_next_fast(v_s_232_, v_p_233_);
lean_dec(v_p_233_);
v___x_257_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_255_, v_s_232_, v___x_256_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; 
v___x_258_ = lean_string_utf8_next_fast(v_s_232_, v_p_233_);
lean_dec(v_p_233_);
v_p_233_ = v___x_258_;
goto _start;
}
}
else
{
lean_dec(v_p_233_);
return v_decide_235_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_232_ = stack[0].m_obj;
lean_object* v_p_233_ = stack[1].m_obj;
uint8_t v_res_260_;
v_res_260_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_232_, v_p_233_);
stack->m_num = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* v_s_261_, lean_object* v_p_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_261_, v_p_262_);
lean_dec_ref(v_s_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* v_prev_265_, lean_object* v_next_266_){
_start:
{
if (lean_obj_tag(v_prev_265_) == 1)
{
lean_object* v_str_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v_decide_273_; 
v_str_270_ = lean_ctor_get(v_prev_265_, 1);
v___x_271_ = lean_string_utf8_byte_size(v_str_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v_decide_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
if (v_decide_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint32_t v___x_278_; uint32_t v___x_279_; uint8_t v___x_280_; 
lean_inc_ref(v_str_270_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_str_270_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_sub(v___x_271_, v___x_275_);
v___x_277_ = l_String_Slice_posLE(v___x_274_, v___x_276_);
lean_dec_ref_known(v___x_274_, 3);
v___x_278_ = lean_string_utf8_get_fast(v_str_270_, v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = 95;
v___x_280_ = lean_uint32_dec_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
goto v___jp_267_;
}
else
{
return v___x_280_;
}
}
else
{
goto v___jp_267_;
}
}
else
{
goto v___jp_267_;
}
v___jp_267_:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_next_266_, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation_0interp(lean_interpreter_value* stack)
{
lean_object* v_prev_265_ = stack[0].m_obj;
lean_object* v_next_266_ = stack[1].m_obj;
uint8_t v_res_281_;
v_res_281_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_265_, v_next_266_);
stack->m_num = v_res_281_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* v_prev_282_, lean_object* v_next_283_){
_start:
{
uint8_t v_res_284_; lean_object* v_r_285_; 
v_res_284_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_282_, v_next_283_);
lean_dec_ref(v_next_283_);
lean_dec(v_prev_282_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* v_x_289_){
_start:
{
switch(lean_obj_tag(v_x_289_))
{
case 0:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_290_;
}
case 1:
{
lean_object* v_pre_291_; lean_object* v_str_292_; lean_object* v_m_293_; 
v_pre_291_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_pre_291_);
v_str_292_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_str_292_);
lean_dec_ref_known(v_x_289_, 2);
v_m_293_ = l_String_Internal_mangle(v_str_292_);
lean_dec_ref(v_str_292_);
if (lean_obj_tag(v_pre_291_) == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_m_293_, v___x_294_);
if (v___x_295_ == 0)
{
return v_m_293_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0));
v___x_297_ = lean_string_append(v___x_296_, v_m_293_);
lean_dec_ref(v_m_293_);
return v___x_297_;
}
}
else
{
lean_object* v_m1_298_; lean_object* v___y_300_; uint8_t v___x_303_; 
lean_inc(v_pre_291_);
v_m1_298_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_291_);
v___x_303_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_pre_291_, v_m_293_);
lean_dec(v_pre_291_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___y_300_ = v___x_304_;
goto v___jp_299_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2));
v___y_300_ = v___x_305_;
goto v___jp_299_;
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_string_append(v_m1_298_, v___y_300_);
v___x_302_ = lean_string_append(v___x_301_, v_m_293_);
lean_dec_ref(v_m_293_);
return v___x_302_;
}
}
}
default: 
{
lean_object* v_pre_306_; 
v_pre_306_ = lean_ctor_get(v_x_289_, 0);
if (lean_obj_tag(v_pre_306_) == 0)
{
lean_object* v_i_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v_i_307_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_i_307_);
lean_dec_ref_known(v_x_289_, 2);
v___x_308_ = l_Nat_reprFast(v_i_307_);
v___x_309_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v_i_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc(v_pre_306_);
v_i_311_ = lean_ctor_get(v_x_289_, 1);
lean_inc(v_i_311_);
lean_dec_ref_known(v_x_289_, 2);
v___x_312_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_306_);
v___x_313_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_314_ = lean_string_append(v___x_312_, v___x_313_);
v___x_315_ = l_Nat_reprFast(v_i_311_);
v___x_316_ = lean_string_append(v___x_314_, v___x_315_);
lean_dec_ref(v___x_315_);
v___x_317_ = lean_string_append(v___x_316_, v___x_313_);
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* v_n_318_, lean_object* v_pre_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_318_);
v___x_321_ = lean_string_append(v_pre_319_, v___x_320_);
lean_dec_ref(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object* v_s_324_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_328_ = lean_string_utf8_byte_size(v_s_324_);
v___x_329_ = lean_unsigned_to_nat(2u);
v___x_330_ = lean_nat_dec_le(v___x_329_, v___x_328_);
if (v___x_330_ == 0)
{
goto v___jp_325_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_nat_sub(v___x_328_, v___x_329_);
v___x_334_ = lean_string_memcmp(v_s_324_, v___x_331_, v___x_333_, v___x_332_, v___x_329_);
lean_dec(v___x_333_);
if (v___x_334_ == 0)
{
goto v___jp_325_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__1));
v___x_336_ = lean_string_append(v_s_324_, v___x_335_);
return v___x_336_;
}
}
v___jp_325_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__0));
v___x_327_ = lean_string_append(v_s_324_, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object* v_moduleName_337_, lean_object* v_pkg_x3f_338_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_338_) == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_340_ = l_Lean_Name_mangle(v_moduleName_337_, v___x_339_);
return v___x_340_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_val_341_ = lean_ctor_get(v_pkg_x3f_338_, 0);
v___x_342_ = l_String_Internal_mangle(v_val_341_);
v___x_343_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_344_ = lean_string_append(v___x_342_, v___x_343_);
v___x_345_ = l_Lean_Name_mangle(v_moduleName_337_, v___x_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object* v_moduleName_346_, lean_object* v_pkg_x3f_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_mkModuleInitializationStem(v_moduleName_346_, v_pkg_x3f_347_);
lean_dec(v_pkg_x3f_347_);
return v_res_348_;
}
}
lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t v_phases_351_){
_start:
{
switch(v_phases_351_)
{
case 0:
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__0));
return v___x_352_;
}
case 1:
{
lean_object* v___x_353_; 
v___x_353_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__1));
return v___x_353_;
}
default: 
{
lean_object* v___x_354_; 
v___x_354_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_354_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkModuleInitializationPrefix_0interp(lean_interpreter_value* stack)
{
uint8_t v_phases_351_ = stack[0].m_num;
lean_object* v_res_355_;
v_res_355_ = l_Lean_mkModuleInitializationPrefix(v_phases_351_);
stack->m_obj
 = v_res_355_;
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix___boxed(lean_object* v_phases_356_){
_start:
{
uint8_t v_phases_boxed_357_; lean_object* v_res_358_; 
v_phases_boxed_357_ = lean_unbox(v_phases_356_);
v_res_358_ = l_Lean_mkModuleInitializationPrefix(v_phases_boxed_357_);
return v_res_358_;
}
}
lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object* v_moduleName_360_, lean_object* v_pkg_x3f_361_, uint8_t v_phases_362_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_363_ = l_Lean_mkModuleInitializationPrefix(v_phases_362_);
v___x_364_ = ((lean_object*)(l_Lean_mkModuleInitializationFunctionName___closed__0));
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
v___x_366_ = l_Lean_mkModuleInitializationStem(v_moduleName_360_, v_pkg_x3f_361_);
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Lean_mkModuleInitializationFunctionName_0interp(lean_interpreter_value* stack)
{
lean_object* v_moduleName_360_ = stack[0].m_obj;
lean_object* v_pkg_x3f_361_ = stack[1].m_obj;
uint8_t v_phases_362_ = stack[2].m_num;
lean_object* v_res_368_;
v_res_368_ = l_Lean_mkModuleInitializationFunctionName(v_moduleName_360_, v_pkg_x3f_361_, v_phases_362_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object* v_moduleName_369_, lean_object* v_pkg_x3f_370_, lean_object* v_phases_371_){
_start:
{
uint8_t v_phases_boxed_372_; lean_object* v_res_373_; 
v_phases_boxed_372_ = lean_unbox(v_phases_371_);
v_res_373_ = l_Lean_mkModuleInitializationFunctionName(v_moduleName_369_, v_pkg_x3f_370_, v_phases_boxed_372_);
lean_dec(v_pkg_x3f_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object* v_pkg_x3f_376_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_376_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__0));
return v___x_377_;
}
else
{
lean_object* v_val_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_val_378_ = lean_ctor_get(v_pkg_x3f_376_, 0);
v___x_379_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__1));
v___x_380_ = l_String_Internal_mangle(v_val_378_);
v___x_381_ = lean_string_append(v___x_379_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_383_ = lean_string_append(v___x_381_, v___x_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object* v_pkg_x3f_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_mkPackageSymbolPrefix(v_pkg_x3f_384_);
lean_dec(v_pkg_x3f_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_zero_388_; uint8_t v_isZero_389_; 
v_zero_388_ = lean_unsigned_to_nat(0u);
v_isZero_389_ = lean_nat_dec_eq(v_x_386_, v_zero_388_);
if (v_isZero_389_ == 1)
{
lean_dec(v_x_386_);
return v_x_387_;
}
else
{
uint32_t v___x_390_; lean_object* v_one_391_; lean_object* v_n_392_; lean_object* v___x_393_; 
v___x_390_ = 95;
v_one_391_ = lean_unsigned_to_nat(1u);
v_n_392_ = lean_nat_sub(v_x_386_, v_one_391_);
lean_dec(v_x_386_);
v___x_393_ = lean_string_push(v_x_387_, v___x_390_);
v_x_386_ = v_n_392_;
v_x_387_ = v___x_393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object* v_s_395_, lean_object* v_p_u2080_396_, lean_object* v_res_397_, lean_object* v_acc_398_, lean_object* v_ucount_399_){
_start:
{
lean_object* v___x_400_; uint8_t v_decide_401_; 
v___x_400_ = lean_string_utf8_byte_size(v_s_395_);
v_decide_401_ = lean_nat_dec_eq(v_p_u2080_396_, v___x_400_);
if (v_decide_401_ == 0)
{
uint32_t v_ch_402_; lean_object* v_p_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v_ch_402_ = lean_string_utf8_get_fast(v_s_395_, v_p_u2080_396_);
v_p_403_ = lean_string_utf8_next_fast(v_s_395_, v_p_u2080_396_);
lean_dec(v_p_u2080_396_);
v___x_404_ = 95;
v___x_405_ = lean_uint32_dec_eq(v_ch_402_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_458_; 
v___x_406_ = lean_unsigned_to_nat(2u);
v___x_407_ = lean_nat_mod(v_ucount_399_, v___x_406_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_nat_dec_eq(v___x_407_, v___x_408_);
lean_dec(v___x_407_);
if (v___x_458_ == 0)
{
uint32_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = 48;
v___x_460_ = lean_uint32_dec_le(v___x_459_, v_ch_402_);
if (v___x_460_ == 0)
{
goto v___jp_445_;
}
else
{
uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 57;
v___x_462_ = lean_uint32_dec_le(v_ch_402_, v___x_461_);
if (v___x_462_ == 0)
{
goto v___jp_445_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_res_466_; uint8_t v___y_472_; uint8_t v___x_478_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_shiftr(v_ucount_399_, v___x_463_);
lean_dec(v_ucount_399_);
v___x_465_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_464_, v_acc_398_);
v_res_466_ = l_Lean_Name_str___override(v_res_397_, v___x_465_);
v___x_478_ = lean_uint32_dec_eq(v_ch_402_, v___x_459_);
if (v___x_478_ == 0)
{
goto v___jp_467_;
}
else
{
uint8_t v_decide_479_; 
v_decide_479_ = lean_nat_dec_eq(v_p_403_, v___x_400_);
if (v_decide_479_ == 0)
{
v___y_472_ = v___x_478_;
goto v___jp_471_;
}
else
{
v___y_472_ = v___x_458_;
goto v___jp_471_;
}
}
v___jp_467_:
{
uint32_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_uint32_sub(v_ch_402_, v___x_459_);
v___x_469_ = lean_uint32_to_nat(v___x_468_);
v___x_470_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_395_, v_p_403_, v_res_466_, v___x_469_);
return v___x_470_;
}
v___jp_471_:
{
if (v___y_472_ == 0)
{
goto v___jp_467_;
}
else
{
uint32_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_string_utf8_get_fast(v_s_395_, v_p_403_);
v___x_474_ = lean_uint32_dec_eq(v___x_473_, v___x_459_);
if (v___x_474_ == 0)
{
goto v___jp_467_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_string_utf8_next_fast(v_s_395_, v_p_403_);
v___x_476_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v_p_u2080_396_ = v___x_475_;
v_res_397_ = v_res_466_;
v_acc_398_ = v___x_476_;
v_ucount_399_ = v___x_408_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_shiftr(v_ucount_399_, v___x_480_);
lean_dec(v_ucount_399_);
v___x_482_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_481_, v_acc_398_);
v___x_483_ = lean_string_push(v___x_482_, v_ch_402_);
v_p_u2080_396_ = v_p_403_;
v_acc_398_ = v___x_483_;
v_ucount_399_ = v___x_408_;
goto _start;
}
v___jp_409_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = l_Lean_Name_str___override(v_res_397_, v_acc_398_);
v___x_411_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_shiftr(v_ucount_399_, v___x_412_);
lean_dec(v_ucount_399_);
v___x_414_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_413_, v___x_411_);
v___x_415_ = lean_string_push(v___x_414_, v_ch_402_);
v_p_u2080_396_ = v_p_403_;
v_res_397_ = v___x_410_;
v_acc_398_ = v___x_415_;
v_ucount_399_ = v___x_408_;
goto _start;
}
v___jp_417_:
{
uint32_t v___x_418_; uint8_t v___x_419_; 
v___x_418_ = 85;
v___x_419_ = lean_uint32_dec_eq(v_ch_402_, v___x_418_);
if (v___x_419_ == 0)
{
goto v___jp_409_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(8u);
v___x_421_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_420_, v_s_395_, v_p_403_, v___x_408_);
if (lean_obj_tag(v___x_421_) == 1)
{
lean_object* v_val_422_; lean_object* v_fst_423_; lean_object* v_snd_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_acc_427_; uint32_t v___x_428_; lean_object* v___x_429_; 
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
v_fst_423_ = lean_ctor_get(v_val_422_, 0);
lean_inc(v_fst_423_);
v_snd_424_ = lean_ctor_get(v_val_422_, 1);
lean_inc(v_snd_424_);
lean_dec(v_val_422_);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_shiftr(v_ucount_399_, v___x_425_);
lean_dec(v_ucount_399_);
v_acc_427_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_426_, v_acc_398_);
v___x_428_ = l_Char_ofNat(v_snd_424_);
lean_dec(v_snd_424_);
v___x_429_ = lean_string_push(v_acc_427_, v___x_428_);
v_p_u2080_396_ = v_fst_423_;
v_acc_398_ = v___x_429_;
v_ucount_399_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v___x_421_);
goto v___jp_409_;
}
}
}
v___jp_431_:
{
uint32_t v___x_432_; uint8_t v___x_433_; 
v___x_432_ = 117;
v___x_433_ = lean_uint32_dec_eq(v_ch_402_, v___x_432_);
if (v___x_433_ == 0)
{
goto v___jp_417_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_434_, v_s_395_, v_p_403_, v___x_408_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_acc_441_; uint32_t v___x_442_; lean_object* v___x_443_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v_fst_437_ = lean_ctor_get(v_val_436_, 0);
lean_inc(v_fst_437_);
v_snd_438_ = lean_ctor_get(v_val_436_, 1);
lean_inc(v_snd_438_);
lean_dec(v_val_436_);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_shiftr(v_ucount_399_, v___x_439_);
lean_dec(v_ucount_399_);
v_acc_441_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_440_, v_acc_398_);
v___x_442_ = l_Char_ofNat(v_snd_438_);
lean_dec(v_snd_438_);
v___x_443_ = lean_string_push(v_acc_441_, v___x_442_);
v_p_u2080_396_ = v_fst_437_;
v_acc_398_ = v___x_443_;
v_ucount_399_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v___x_435_);
goto v___jp_417_;
}
}
}
v___jp_445_:
{
uint32_t v___x_446_; uint8_t v___x_447_; 
v___x_446_ = 120;
v___x_447_ = lean_uint32_dec_eq(v_ch_402_, v___x_446_);
if (v___x_447_ == 0)
{
goto v___jp_431_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_406_, v_s_395_, v_p_403_, v___x_408_);
if (lean_obj_tag(v___x_448_) == 1)
{
lean_object* v_val_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_acc_454_; uint32_t v___x_455_; lean_object* v___x_456_; 
v_val_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_448_, 1);
v_fst_450_ = lean_ctor_get(v_val_449_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v_val_449_, 1);
lean_inc(v_snd_451_);
lean_dec(v_val_449_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_shiftr(v_ucount_399_, v___x_452_);
lean_dec(v_ucount_399_);
v_acc_454_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_453_, v_acc_398_);
v___x_455_ = l_Char_ofNat(v_snd_451_);
lean_dec(v_snd_451_);
v___x_456_ = lean_string_push(v_acc_454_, v___x_455_);
v_p_u2080_396_ = v_fst_450_;
v_acc_398_ = v___x_456_;
v_ucount_399_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v___x_448_);
goto v___jp_431_;
}
}
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_ucount_399_, v___x_485_);
lean_dec(v_ucount_399_);
v_p_u2080_396_ = v_p_403_;
v_ucount_399_ = v___x_486_;
goto _start;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_p_u2080_396_);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_shiftr(v_ucount_399_, v___x_488_);
lean_dec(v_ucount_399_);
v___x_490_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_489_, v_acc_398_);
v___x_491_ = l_Lean_Name_str___override(v_res_397_, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* v_s_492_, lean_object* v_p_493_, lean_object* v_res_494_){
_start:
{
lean_object* v___x_495_; uint8_t v_decide_496_; 
v___x_495_ = lean_string_utf8_byte_size(v_s_492_);
v_decide_496_ = lean_nat_dec_eq(v_p_493_, v___x_495_);
if (v_decide_496_ == 0)
{
uint32_t v_ch_497_; lean_object* v_p_498_; uint8_t v___y_505_; uint32_t v___x_523_; uint8_t v___x_524_; 
v_ch_497_ = lean_string_utf8_get_fast(v_s_492_, v_p_493_);
v_p_498_ = lean_string_utf8_next_fast(v_s_492_, v_p_493_);
v___x_523_ = 48;
v___x_524_ = lean_uint32_dec_le(v___x_523_, v_ch_497_);
if (v___x_524_ == 0)
{
goto v___jp_513_;
}
else
{
uint32_t v___x_525_; uint8_t v___x_526_; 
v___x_525_ = 57;
v___x_526_ = lean_uint32_dec_le(v_ch_497_, v___x_525_);
if (v___x_526_ == 0)
{
goto v___jp_513_;
}
else
{
uint8_t v___x_527_; 
v___x_527_ = lean_uint32_dec_eq(v_ch_497_, v___x_523_);
if (v___x_527_ == 0)
{
goto v___jp_499_;
}
else
{
uint8_t v_decide_528_; 
v_decide_528_ = lean_nat_dec_eq(v_p_498_, v___x_495_);
if (v_decide_528_ == 0)
{
v___y_505_ = v___x_527_;
goto v___jp_504_;
}
else
{
v___y_505_ = v_decide_496_;
goto v___jp_504_;
}
}
}
}
v___jp_499_:
{
uint32_t v___x_500_; uint32_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = 48;
v___x_501_ = lean_uint32_sub(v_ch_497_, v___x_500_);
v___x_502_ = lean_uint32_to_nat(v___x_501_);
v___x_503_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_492_, v_p_498_, v_res_494_, v___x_502_);
return v___x_503_;
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
goto v___jp_499_;
}
else
{
uint32_t v___x_506_; uint32_t v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_string_utf8_get_fast(v_s_492_, v_p_498_);
v___x_507_ = 48;
v___x_508_ = lean_uint32_dec_eq(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
goto v___jp_499_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_509_ = lean_string_utf8_next_fast(v_s_492_, v_p_498_);
v___x_510_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_492_, v___x_509_, v_res_494_, v___x_510_, v___x_511_);
return v___x_512_;
}
}
}
v___jp_513_:
{
uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_514_ = 95;
v___x_515_ = lean_uint32_dec_eq(v_ch_497_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_517_ = lean_string_push(v___x_516_, v_ch_497_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_492_, v_p_498_, v_res_494_, v___x_517_, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_492_, v_p_498_, v_res_494_, v___x_520_, v___x_521_);
return v___x_522_;
}
}
}
else
{
return v_res_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* v_s_529_, lean_object* v_p_530_, lean_object* v_res_531_, lean_object* v_n_532_){
_start:
{
lean_object* v___x_533_; uint8_t v_decide_534_; 
v___x_533_ = lean_string_utf8_byte_size(v_s_529_);
v_decide_534_ = lean_nat_dec_eq(v_p_530_, v___x_533_);
if (v_decide_534_ == 0)
{
uint32_t v_ch_535_; lean_object* v_p_536_; uint32_t v___x_542_; uint8_t v___x_543_; 
v_ch_535_ = lean_string_utf8_get_fast(v_s_529_, v_p_530_);
v_p_536_ = lean_string_utf8_next_fast(v_s_529_, v_p_530_);
lean_dec(v_p_530_);
v___x_542_ = 48;
v___x_543_ = lean_uint32_dec_le(v___x_542_, v_ch_535_);
if (v___x_543_ == 0)
{
goto v___jp_537_;
}
else
{
uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 57;
v___x_545_ = lean_uint32_dec_le(v_ch_535_, v___x_544_);
if (v___x_545_ == 0)
{
goto v___jp_537_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; uint32_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_546_ = lean_unsigned_to_nat(10u);
v___x_547_ = lean_nat_mul(v_n_532_, v___x_546_);
lean_dec(v_n_532_);
v___x_548_ = lean_uint32_sub(v_ch_535_, v___x_542_);
v___x_549_ = lean_uint32_to_nat(v___x_548_);
v___x_550_ = lean_nat_add(v___x_547_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_547_);
v_p_530_ = v_p_536_;
v_n_532_ = v___x_550_;
goto _start;
}
}
v___jp_537_:
{
lean_object* v_res_538_; uint8_t v_decide_539_; 
v_res_538_ = l_Lean_Name_num___override(v_res_531_, v_n_532_);
v_decide_539_ = lean_nat_dec_eq(v_p_536_, v___x_533_);
if (v_decide_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_string_utf8_next_fast(v_s_529_, v_p_536_);
v___x_541_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_529_, v___x_540_, v_res_538_);
return v___x_541_;
}
else
{
return v_res_538_;
}
}
}
else
{
lean_object* v___x_552_; 
lean_dec(v_p_530_);
v___x_552_ = l_Lean_Name_num___override(v_res_531_, v_n_532_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* v_s_553_, lean_object* v_p_554_, lean_object* v_res_555_, lean_object* v_n_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_553_, v_p_554_, v_res_555_, v_n_556_);
lean_dec_ref(v_s_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* v_s_558_, lean_object* v_p_559_, lean_object* v_res_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_558_, v_p_559_, v_res_560_);
lean_dec(v_p_559_);
lean_dec_ref(v_s_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* v_s_562_, lean_object* v_p_u2080_563_, lean_object* v_res_564_, lean_object* v_acc_565_, lean_object* v_ucount_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_562_, v_p_u2080_563_, v_res_564_, v_acc_565_, v_ucount_566_);
lean_dec_ref(v_s_562_);
return v_res_567_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_568_; lean_object* v___x_569_; 
v___x_568_ = 120;
v___x_569_ = lean_box_uint32(v___x_568_);
return v___x_569_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t v_ch_570_, lean_object* v_x_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
uint32_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = 120;
v___x_575_ = lean_uint32_dec_eq(v_ch_570_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_h__1_572_);
v___x_576_ = lean_box_uint32(v_ch_570_);
v___x_577_ = lean_apply_4(v_h__2_573_, v___x_576_, v_x_571_, lean_box(0), lean_box(0));
return v___x_577_;
}
else
{
if (lean_obj_tag(v_x_571_) == 1)
{
lean_object* v_val_578_; lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_581_; 
lean_dec(v_h__2_573_);
v_val_578_ = lean_ctor_get(v_x_571_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v_x_571_, 1);
v_fst_579_ = lean_ctor_get(v_val_578_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v_val_578_, 1);
lean_inc(v_snd_580_);
lean_dec(v_val_578_);
v___x_581_ = lean_apply_3(v_h__1_572_, v_fst_579_, v_snd_580_, lean_box(0));
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_h__1_572_);
v___x_582_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_583_ = lean_apply_4(v_h__2_573_, v___x_582_, v_x_571_, lean_box(0), lean_box(0));
return v___x_583_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_570_ = stack[0].m_num;
lean_object* v_x_571_ = stack[1].m_obj;
lean_object* v_h__1_572_ = stack[2].m_obj;
lean_object* v_h__2_573_ = stack[3].m_obj;
lean_object* v_res_584_;
v_res_584_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_570_, v_x_571_, v_h__1_572_, v_h__2_573_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* v_ch_585_, lean_object* v_x_586_, lean_object* v_h__1_587_, lean_object* v_h__2_588_){
_start:
{
uint32_t v_ch_87__boxed_589_; lean_object* v_res_590_; 
v_ch_87__boxed_589_ = lean_unbox_uint32(v_ch_585_);
lean_dec(v_ch_585_);
v_res_590_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_87__boxed_589_, v_x_586_, v_h__1_587_, v_h__2_588_);
return v_res_590_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* v_s_591_, lean_object* v_motive_592_, uint32_t v_ch_593_, lean_object* v_x_594_, lean_object* v_h__1_595_, lean_object* v_h__2_596_){
_start:
{
uint32_t v___x_597_; uint8_t v___x_598_; 
v___x_597_ = 120;
v___x_598_ = lean_uint32_dec_eq(v_ch_593_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_h__1_595_);
v___x_599_ = lean_box_uint32(v_ch_593_);
v___x_600_ = lean_apply_4(v_h__2_596_, v___x_599_, v_x_594_, lean_box(0), lean_box(0));
return v___x_600_;
}
else
{
if (lean_obj_tag(v_x_594_) == 1)
{
lean_object* v_val_601_; lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___x_604_; 
lean_dec(v_h__2_596_);
v_val_601_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v_x_594_, 1);
v_fst_602_ = lean_ctor_get(v_val_601_, 0);
lean_inc(v_fst_602_);
v_snd_603_ = lean_ctor_get(v_val_601_, 1);
lean_inc(v_snd_603_);
lean_dec(v_val_601_);
v___x_604_ = lean_apply_3(v_h__1_595_, v_fst_602_, v_snd_603_, lean_box(0));
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_h__1_595_);
v___x_605_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_606_ = lean_apply_4(v_h__2_596_, v___x_605_, v_x_594_, lean_box(0), lean_box(0));
return v___x_606_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_591_ = stack[0].m_obj;
uint32_t v_ch_593_ = stack[2].m_num;
lean_object* v_x_594_ = stack[3].m_obj;
lean_object* v_h__1_595_ = stack[4].m_obj;
lean_object* v_h__2_596_ = stack[5].m_obj;
lean_object* v_res_607_;
v_res_607_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_591_, lean_box(0), v_ch_593_, v_x_594_, v_h__1_595_, v_h__2_596_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* v_s_608_, lean_object* v_motive_609_, lean_object* v_ch_610_, lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
uint32_t v_ch_133__boxed_614_; lean_object* v_res_615_; 
v_ch_133__boxed_614_ = lean_unbox_uint32(v_ch_610_);
lean_dec(v_ch_610_);
v_res_615_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_608_, v_motive_609_, v_ch_133__boxed_614_, v_x_611_, v_h__1_612_, v_h__2_613_);
lean_dec_ref(v_s_608_);
return v_res_615_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_616_; lean_object* v___x_617_; 
v___x_616_ = 117;
v___x_617_ = lean_box_uint32(v___x_616_);
return v___x_617_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t v_ch_618_, lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_){
_start:
{
uint32_t v___x_622_; uint8_t v___x_623_; 
v___x_622_ = 117;
v___x_623_ = lean_uint32_dec_eq(v_ch_618_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_h__1_620_);
v___x_624_ = lean_box_uint32(v_ch_618_);
v___x_625_ = lean_apply_4(v_h__2_621_, v___x_624_, v_x_619_, lean_box(0), lean_box(0));
return v___x_625_;
}
else
{
if (lean_obj_tag(v_x_619_) == 1)
{
lean_object* v_val_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; lean_object* v___x_629_; 
lean_dec(v_h__2_621_);
v_val_626_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v_x_619_, 1);
v_fst_627_ = lean_ctor_get(v_val_626_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v_val_626_, 1);
lean_inc(v_snd_628_);
lean_dec(v_val_626_);
v___x_629_ = lean_apply_3(v_h__1_620_, v_fst_627_, v_snd_628_, lean_box(0));
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_h__1_620_);
v___x_630_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_631_ = lean_apply_4(v_h__2_621_, v___x_630_, v_x_619_, lean_box(0), lean_box(0));
return v___x_631_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_618_ = stack[0].m_num;
lean_object* v_x_619_ = stack[1].m_obj;
lean_object* v_h__1_620_ = stack[2].m_obj;
lean_object* v_h__2_621_ = stack[3].m_obj;
lean_object* v_res_632_;
v_res_632_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_618_, v_x_619_, v_h__1_620_, v_h__2_621_);
stack->m_obj
 = v_res_632_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* v_ch_633_, lean_object* v_x_634_, lean_object* v_h__1_635_, lean_object* v_h__2_636_){
_start:
{
uint32_t v_ch_87__boxed_637_; lean_object* v_res_638_; 
v_ch_87__boxed_637_ = lean_unbox_uint32(v_ch_633_);
lean_dec(v_ch_633_);
v_res_638_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_87__boxed_637_, v_x_634_, v_h__1_635_, v_h__2_636_);
return v_res_638_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* v_s_639_, lean_object* v_motive_640_, uint32_t v_ch_641_, lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
uint32_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 117;
v___x_646_ = lean_uint32_dec_eq(v_ch_641_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_643_);
v___x_647_ = lean_box_uint32(v_ch_641_);
v___x_648_ = lean_apply_4(v_h__2_644_, v___x_647_, v_x_642_, lean_box(0), lean_box(0));
return v___x_648_;
}
else
{
if (lean_obj_tag(v_x_642_) == 1)
{
lean_object* v_val_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; 
lean_dec(v_h__2_644_);
v_val_649_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_x_642_, 1);
v_fst_650_ = lean_ctor_get(v_val_649_, 0);
lean_inc(v_fst_650_);
v_snd_651_ = lean_ctor_get(v_val_649_, 1);
lean_inc(v_snd_651_);
lean_dec(v_val_649_);
v___x_652_ = lean_apply_3(v_h__1_643_, v_fst_650_, v_snd_651_, lean_box(0));
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v_h__1_643_);
v___x_653_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_654_ = lean_apply_4(v_h__2_644_, v___x_653_, v_x_642_, lean_box(0), lean_box(0));
return v___x_654_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_639_ = stack[0].m_obj;
uint32_t v_ch_641_ = stack[2].m_num;
lean_object* v_x_642_ = stack[3].m_obj;
lean_object* v_h__1_643_ = stack[4].m_obj;
lean_object* v_h__2_644_ = stack[5].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_639_, lean_box(0), v_ch_641_, v_x_642_, v_h__1_643_, v_h__2_644_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* v_s_656_, lean_object* v_motive_657_, lean_object* v_ch_658_, lean_object* v_x_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_){
_start:
{
uint32_t v_ch_133__boxed_662_; lean_object* v_res_663_; 
v_ch_133__boxed_662_ = lean_unbox_uint32(v_ch_658_);
lean_dec(v_ch_658_);
v_res_663_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_656_, v_motive_657_, v_ch_133__boxed_662_, v_x_659_, v_h__1_660_, v_h__2_661_);
lean_dec_ref(v_s_656_);
return v_res_663_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_664_; lean_object* v___x_665_; 
v___x_664_ = 85;
v___x_665_ = lean_box_uint32(v___x_664_);
return v___x_665_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t v_ch_666_, lean_object* v_x_667_, lean_object* v_h__1_668_, lean_object* v_h__2_669_){
_start:
{
uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 85;
v___x_671_ = lean_uint32_dec_eq(v_ch_666_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v_h__1_668_);
v___x_672_ = lean_box_uint32(v_ch_666_);
v___x_673_ = lean_apply_4(v_h__2_669_, v___x_672_, v_x_667_, lean_box(0), lean_box(0));
return v___x_673_;
}
else
{
if (lean_obj_tag(v_x_667_) == 1)
{
lean_object* v_val_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_677_; 
lean_dec(v_h__2_669_);
v_val_674_ = lean_ctor_get(v_x_667_, 0);
lean_inc(v_val_674_);
lean_dec_ref_known(v_x_667_, 1);
v_fst_675_ = lean_ctor_get(v_val_674_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v_val_674_, 1);
lean_inc(v_snd_676_);
lean_dec(v_val_674_);
v___x_677_ = lean_apply_3(v_h__1_668_, v_fst_675_, v_snd_676_, lean_box(0));
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_h__1_668_);
v___x_678_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_679_ = lean_apply_4(v_h__2_669_, v___x_678_, v_x_667_, lean_box(0), lean_box(0));
return v___x_679_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_666_ = stack[0].m_num;
lean_object* v_x_667_ = stack[1].m_obj;
lean_object* v_h__1_668_ = stack[2].m_obj;
lean_object* v_h__2_669_ = stack[3].m_obj;
lean_object* v_res_680_;
v_res_680_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_666_, v_x_667_, v_h__1_668_, v_h__2_669_);
stack->m_obj
 = v_res_680_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* v_ch_681_, lean_object* v_x_682_, lean_object* v_h__1_683_, lean_object* v_h__2_684_){
_start:
{
uint32_t v_ch_87__boxed_685_; lean_object* v_res_686_; 
v_ch_87__boxed_685_ = lean_unbox_uint32(v_ch_681_);
lean_dec(v_ch_681_);
v_res_686_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_87__boxed_685_, v_x_682_, v_h__1_683_, v_h__2_684_);
return v_res_686_;
}
}
lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* v_s_687_, lean_object* v_motive_688_, uint32_t v_ch_689_, lean_object* v_x_690_, lean_object* v_h__1_691_, lean_object* v_h__2_692_){
_start:
{
uint32_t v___x_693_; uint8_t v___x_694_; 
v___x_693_ = 85;
v___x_694_ = lean_uint32_dec_eq(v_ch_689_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_h__1_691_);
v___x_695_ = lean_box_uint32(v_ch_689_);
v___x_696_ = lean_apply_4(v_h__2_692_, v___x_695_, v_x_690_, lean_box(0), lean_box(0));
return v___x_696_;
}
else
{
if (lean_obj_tag(v_x_690_) == 1)
{
lean_object* v_val_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_700_; 
lean_dec(v_h__2_692_);
v_val_697_ = lean_ctor_get(v_x_690_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v_x_690_, 1);
v_fst_698_ = lean_ctor_get(v_val_697_, 0);
lean_inc(v_fst_698_);
v_snd_699_ = lean_ctor_get(v_val_697_, 1);
lean_inc(v_snd_699_);
lean_dec(v_val_697_);
v___x_700_ = lean_apply_3(v_h__1_691_, v_fst_698_, v_snd_699_, lean_box(0));
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v_h__1_691_);
v___x_701_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_702_ = lean_apply_4(v_h__2_692_, v___x_701_, v_x_690_, lean_box(0), lean_box(0));
return v___x_702_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_687_ = stack[0].m_obj;
uint32_t v_ch_689_ = stack[2].m_num;
lean_object* v_x_690_ = stack[3].m_obj;
lean_object* v_h__1_691_ = stack[4].m_obj;
lean_object* v_h__2_692_ = stack[5].m_obj;
lean_object* v_res_703_;
v_res_703_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_687_, lean_box(0), v_ch_689_, v_x_690_, v_h__1_691_, v_h__2_692_);
stack->m_obj
 = v_res_703_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* v_s_704_, lean_object* v_motive_705_, lean_object* v_ch_706_, lean_object* v_x_707_, lean_object* v_h__1_708_, lean_object* v_h__2_709_){
_start:
{
uint32_t v_ch_133__boxed_710_; lean_object* v_res_711_; 
v_ch_133__boxed_710_ = lean_unbox_uint32(v_ch_706_);
lean_dec(v_ch_706_);
v_res_711_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_704_, v_motive_705_, v_ch_133__boxed_710_, v_x_707_, v_h__1_708_, v_h__2_709_);
lean_dec_ref(v_s_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* v_s_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_box(0);
v___x_715_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_712_, v___x_713_, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* v_s_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Name_demangle(v_s_716_);
lean_dec_ref(v_s_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* v_s_718_){
_start:
{
lean_object* v_n_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_n_719_ = l_Lean_Name_demangle(v_s_718_);
lean_inc(v_n_719_);
v___x_720_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_719_);
v___x_721_ = lean_string_dec_eq(v___x_720_, v_s_718_);
lean_dec_ref(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec(v_n_719_);
v___x_722_ = lean_box(0);
return v___x_722_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v_n_719_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* v_s_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Name_demangle_x3f(v_s_724_);
lean_dec_ref(v_s_724_);
return v_res_725_;
}
}
lean_object* runtime_initialize_Lean_Setup(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Setup(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_NameMangling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_NameMangling(builtin);
}
#ifdef __cplusplus
}
#endif
