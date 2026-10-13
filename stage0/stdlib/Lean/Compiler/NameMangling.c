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
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(uint32_t v_n_1_){
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(lean_object* v_n_8_){
_start:
{
uint32_t v_n_boxed_9_; uint32_t v_res_10_; lean_object* v_r_11_; 
v_n_boxed_9_ = lean_unbox_uint32(v_n_8_);
lean_dec(v_n_8_);
v_res_10_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_boxed_9_);
v_r_11_ = lean_box_uint32(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint32_t l___private_Lean_Compiler_NameMangling_0__String_digitChar(uint32_t v_n_12_, lean_object* v_h_13_){
_start:
{
uint32_t v___x_14_; 
v___x_14_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(lean_object* v_n_15_, lean_object* v_h_16_){
_start:
{
uint32_t v_n_boxed_17_; uint32_t v_res_18_; lean_object* v_r_19_; 
v_n_boxed_17_ = lean_unbox_uint32(v_n_15_);
lean_dec(v_n_15_);
v_res_18_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar(v_n_boxed_17_, v_h_16_);
v_r_19_ = lean_box_uint32(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex(lean_object* v_n_20_, uint32_t v_val_21_, lean_object* v_s_22_){
_start:
{
lean_object* v_zero_23_; uint8_t v_isZero_24_; 
v_zero_23_ = lean_unsigned_to_nat(0u);
v_isZero_24_ = lean_nat_dec_eq(v_n_20_, v_zero_23_);
if (v_isZero_24_ == 1)
{
lean_dec(v_n_20_);
return v_s_22_;
}
else
{
lean_object* v_one_25_; lean_object* v_n_26_; uint32_t v___x_27_; uint32_t v___x_28_; uint32_t v___x_29_; uint32_t v___x_30_; uint32_t v___x_31_; uint32_t v_i_32_; uint32_t v___x_33_; lean_object* v___x_34_; 
v_one_25_ = lean_unsigned_to_nat(1u);
v_n_26_ = lean_nat_sub(v_n_20_, v_one_25_);
lean_dec(v_n_20_);
v___x_27_ = lean_uint32_of_nat(v_n_26_);
v___x_28_ = 2;
v___x_29_ = lean_uint32_shift_left(v___x_27_, v___x_28_);
v___x_30_ = lean_uint32_shift_right(v_val_21_, v___x_29_);
v___x_31_ = 15;
v_i_32_ = lean_uint32_land(v___x_30_, v___x_31_);
v___x_33_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_i_32_);
v___x_34_ = lean_string_push(v_s_22_, v___x_33_);
v_n_20_ = v_n_26_;
v_s_22_ = v___x_34_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(lean_object* v_n_36_, lean_object* v_val_37_, lean_object* v_s_38_){
_start:
{
uint32_t v_val_boxed_39_; lean_object* v_res_40_; 
v_val_boxed_39_ = lean_unbox_uint32(v_val_37_);
lean_dec(v_val_37_);
v_res_40_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v_n_36_, v_val_boxed_39_, v_s_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* v_s_45_, lean_object* v_pos_46_, lean_object* v_r_47_){
_start:
{
lean_object* v___x_48_; uint8_t v_decide_49_; 
v___x_48_ = lean_string_utf8_byte_size(v_s_45_);
v_decide_49_ = lean_nat_dec_eq(v_pos_46_, v___x_48_);
if (v_decide_49_ == 0)
{
uint32_t v_c_50_; lean_object* v_pos_51_; uint32_t v___x_91_; uint8_t v___x_92_; 
v_c_50_ = lean_string_utf8_get_fast(v_s_45_, v_pos_46_);
v_pos_51_ = lean_string_utf8_next_fast(v_s_45_, v_pos_46_);
lean_dec(v_pos_46_);
v___x_91_ = 65;
v___x_92_ = lean_uint32_dec_le(v___x_91_, v_c_50_);
if (v___x_92_ == 0)
{
goto v___jp_86_;
}
else
{
uint32_t v___x_93_; uint8_t v___x_94_; 
v___x_93_ = 90;
v___x_94_ = lean_uint32_dec_le(v_c_50_, v___x_93_);
if (v___x_94_ == 0)
{
goto v___jp_86_;
}
else
{
goto v___jp_78_;
}
}
v___jp_52_:
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 95;
v___x_54_ = lean_uint32_dec_eq(v_c_50_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = lean_uint32_to_nat(v_c_50_);
v___x_56_ = lean_unsigned_to_nat(256u);
v___x_57_ = lean_nat_dec_lt(v___x_55_, v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(65536u);
v___x_59_ = lean_nat_dec_lt(v___x_55_, v___x_58_);
lean_dec(v___x_55_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = lean_unsigned_to_nat(8u);
v___x_61_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0));
v___x_62_ = lean_string_append(v_r_47_, v___x_61_);
v___x_63_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_60_, v_c_50_, v___x_62_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_63_;
goto _start;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = lean_unsigned_to_nat(4u);
v___x_66_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1));
v___x_67_ = lean_string_append(v_r_47_, v___x_66_);
v___x_68_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_65_, v_c_50_, v___x_67_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_68_;
goto _start;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v___x_55_);
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2));
v___x_72_ = lean_string_append(v_r_47_, v___x_71_);
v___x_73_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_70_, v_c_50_, v___x_72_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_73_;
goto _start;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_76_ = lean_string_append(v_r_47_, v___x_75_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_76_;
goto _start;
}
}
v___jp_78_:
{
lean_object* v___x_79_; 
v___x_79_ = lean_string_push(v_r_47_, v_c_50_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_79_;
goto _start;
}
v___jp_81_:
{
uint32_t v___x_82_; uint8_t v___x_83_; 
v___x_82_ = 48;
v___x_83_ = lean_uint32_dec_le(v___x_82_, v_c_50_);
if (v___x_83_ == 0)
{
goto v___jp_52_;
}
else
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 57;
v___x_85_ = lean_uint32_dec_le(v_c_50_, v___x_84_);
if (v___x_85_ == 0)
{
goto v___jp_52_;
}
else
{
goto v___jp_78_;
}
}
}
v___jp_86_:
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 97;
v___x_88_ = lean_uint32_dec_le(v___x_87_, v_c_50_);
if (v___x_88_ == 0)
{
goto v___jp_81_;
}
else
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 122;
v___x_90_ = lean_uint32_dec_le(v_c_50_, v___x_89_);
if (v___x_90_ == 0)
{
goto v___jp_81_;
}
else
{
goto v___jp_78_;
}
}
}
}
else
{
lean_dec(v_pos_46_);
return v_r_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object* v_s_95_, lean_object* v_pos_96_, lean_object* v_r_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_95_, v_pos_96_, v_r_97_);
lean_dec_ref(v_s_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle(lean_object* v_s_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_103_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_100_, v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle___boxed(lean_object* v_s_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_String_Internal_mangle(v_s_104_);
lean_dec_ref(v_s_104_);
return v_res_105_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_zero_109_; uint8_t v_isZero_110_; 
v_zero_109_ = lean_unsigned_to_nat(0u);
v_isZero_110_ = lean_nat_dec_eq(v_x_106_, v_zero_109_);
if (v_isZero_110_ == 1)
{
lean_dec(v_x_108_);
lean_dec(v_x_106_);
return v_isZero_110_;
}
else
{
lean_object* v___x_111_; uint8_t v_decide_112_; 
v___x_111_ = lean_string_utf8_byte_size(v_x_107_);
v_decide_112_ = lean_nat_dec_eq(v_x_108_, v___x_111_);
if (v_decide_112_ == 0)
{
lean_object* v_one_113_; lean_object* v_n_114_; uint32_t v_ch_118_; uint32_t v___x_124_; uint8_t v___x_125_; 
v_one_113_ = lean_unsigned_to_nat(1u);
v_n_114_ = lean_nat_sub(v_x_106_, v_one_113_);
lean_dec(v_x_106_);
v_ch_118_ = lean_string_utf8_get_fast(v_x_107_, v_x_108_);
v___x_124_ = 48;
v___x_125_ = lean_uint32_dec_le(v___x_124_, v_ch_118_);
if (v___x_125_ == 0)
{
goto v___jp_119_;
}
else
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 57;
v___x_127_ = lean_uint32_dec_le(v_ch_118_, v___x_126_);
if (v___x_127_ == 0)
{
goto v___jp_119_;
}
else
{
goto v___jp_115_;
}
}
v___jp_115_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_string_utf8_next_fast(v_x_107_, v_x_108_);
lean_dec(v_x_108_);
v_x_106_ = v_n_114_;
v_x_108_ = v___x_116_;
goto _start;
}
v___jp_119_:
{
uint32_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = 97;
v___x_121_ = lean_uint32_dec_le(v___x_120_, v_ch_118_);
if (v___x_121_ == 0)
{
lean_dec(v_n_114_);
lean_dec(v_x_108_);
return v_decide_112_;
}
else
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 102;
v___x_123_ = lean_uint32_dec_le(v_ch_118_, v___x_122_);
if (v___x_123_ == 0)
{
lean_dec(v_n_114_);
lean_dec(v_x_108_);
return v_decide_112_;
}
else
{
goto v___jp_115_;
}
}
}
}
else
{
lean_dec(v_x_108_);
lean_dec(v_x_106_);
return v_isZero_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object* v_x_128_, lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_128_, v_x_129_, v_x_130_);
lean_dec_ref(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t v_c_133_){
_start:
{
uint32_t v___x_145_; uint8_t v___x_146_; 
v___x_145_ = 48;
v___x_146_ = lean_uint32_dec_le(v___x_145_, v_c_133_);
if (v___x_146_ == 0)
{
goto v___jp_134_;
}
else
{
uint32_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = 57;
v___x_148_ = lean_uint32_dec_le(v_c_133_, v___x_147_);
if (v___x_148_ == 0)
{
goto v___jp_134_;
}
else
{
uint32_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_uint32_sub(v_c_133_, v___x_145_);
v___x_150_ = lean_uint32_to_nat(v___x_149_);
v___x_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
v___jp_134_:
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 97;
v___x_136_ = lean_uint32_dec_le(v___x_135_, v_c_133_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 102;
v___x_139_ = lean_uint32_dec_le(v_c_133_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_box(0);
return v___x_140_;
}
else
{
uint32_t v___x_141_; uint32_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = 87;
v___x_142_ = lean_uint32_sub(v_c_133_, v___x_141_);
v___x_143_ = lean_uint32_to_nat(v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object* v_c_152_){
_start:
{
uint32_t v_c_boxed_153_; lean_object* v_res_154_; 
v_c_boxed_153_ = lean_unbox_uint32(v_c_152_);
lean_dec(v_c_152_);
v_res_154_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_boxed_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object* v_k_155_, lean_object* v_s_156_, lean_object* v_p_157_, lean_object* v_acc_158_){
_start:
{
lean_object* v_zero_159_; uint8_t v_isZero_160_; 
v_zero_159_ = lean_unsigned_to_nat(0u);
v_isZero_160_ = lean_nat_dec_eq(v_k_155_, v_zero_159_);
if (v_isZero_160_ == 1)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_k_155_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_p_157_);
lean_ctor_set(v___x_161_, 1, v_acc_158_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v_decide_164_; 
v___x_163_ = lean_string_utf8_byte_size(v_s_156_);
v_decide_164_ = lean_nat_dec_eq(v_p_157_, v___x_163_);
if (v_decide_164_ == 0)
{
uint32_t v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_string_utf8_get_fast(v_s_156_, v_p_157_);
v___x_166_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v___x_165_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_acc_158_);
lean_dec(v_p_157_);
lean_dec(v_k_155_);
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v_one_169_; lean_object* v_n_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_val_168_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v___x_166_, 1);
v_one_169_ = lean_unsigned_to_nat(1u);
v_n_170_ = lean_nat_sub(v_k_155_, v_one_169_);
lean_dec(v_k_155_);
v___x_171_ = lean_string_utf8_next_fast(v_s_156_, v_p_157_);
lean_dec(v_p_157_);
v___x_172_ = lean_unsigned_to_nat(4u);
v___x_173_ = lean_nat_shiftl(v_acc_158_, v___x_172_);
lean_dec(v_acc_158_);
v___x_174_ = lean_nat_lor(v___x_173_, v_val_168_);
lean_dec(v_val_168_);
lean_dec(v___x_173_);
v_k_155_ = v_n_170_;
v_p_157_ = v___x_171_;
v_acc_158_ = v___x_174_;
goto _start;
}
}
else
{
lean_object* v___x_176_; 
lean_dec(v_acc_158_);
lean_dec(v_p_157_);
lean_dec(v_k_155_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object* v_k_177_, lean_object* v_s_178_, lean_object* v_p_179_, lean_object* v_acc_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v_k_177_, v_s_178_, v_p_179_, v_acc_180_);
lean_dec_ref(v_s_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object* v_n_182_, lean_object* v_h__1_183_, lean_object* v_h__2_184_){
_start:
{
lean_object* v_zero_185_; uint8_t v_isZero_186_; 
v_zero_185_ = lean_unsigned_to_nat(0u);
v_isZero_186_ = lean_nat_dec_eq(v_n_182_, v_zero_185_);
if (v_isZero_186_ == 1)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v_h__2_184_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_apply_1(v_h__1_183_, v___x_187_);
return v___x_188_;
}
else
{
lean_object* v_one_189_; lean_object* v_n_190_; lean_object* v___x_191_; 
lean_dec(v_h__1_183_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_n_190_ = lean_nat_sub(v_n_182_, v_one_189_);
v___x_191_ = lean_apply_1(v_h__2_184_, v_n_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object* v_n_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(v_n_192_, v_h__1_193_, v_h__2_194_);
lean_dec(v_n_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object* v_motive_196_, lean_object* v_n_197_, lean_object* v_h__1_198_, lean_object* v_h__2_199_){
_start:
{
lean_object* v_zero_200_; uint8_t v_isZero_201_; 
v_zero_200_ = lean_unsigned_to_nat(0u);
v_isZero_201_ = lean_nat_dec_eq(v_n_197_, v_zero_200_);
if (v_isZero_201_ == 1)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_h__2_199_);
v___x_202_ = lean_box(0);
v___x_203_ = lean_apply_1(v_h__1_198_, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v_one_204_; lean_object* v_n_205_; lean_object* v___x_206_; 
lean_dec(v_h__1_198_);
v_one_204_ = lean_unsigned_to_nat(1u);
v_n_205_ = lean_nat_sub(v_n_197_, v_one_204_);
v___x_206_ = lean_apply_1(v_h__2_199_, v_n_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* v_motive_207_, lean_object* v_n_208_, lean_object* v_h__1_209_, lean_object* v_h__2_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(v_motive_207_, v_n_208_, v_h__1_209_, v_h__2_210_);
lean_dec(v_n_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* v_x_212_, lean_object* v_h__1_213_, lean_object* v_h__2_214_){
_start:
{
if (lean_obj_tag(v_x_212_) == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_h__1_213_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v_h__2_214_, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; 
lean_dec(v_h__2_214_);
v_val_217_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v_x_212_, 1);
v___x_218_ = lean_apply_1(v_h__1_213_, v_val_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* v_motive_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__1_221_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__2_222_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_dec(v_h__2_222_);
v_val_225_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_x_220_, 1);
v___x_226_ = lean_apply_1(v_h__1_221_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* v_s_227_, lean_object* v_p_228_){
_start:
{
lean_object* v___x_229_; uint8_t v_decide_230_; 
v___x_229_ = lean_string_utf8_byte_size(v_s_227_);
v_decide_230_ = lean_nat_dec_eq(v_p_228_, v___x_229_);
if (v_decide_230_ == 0)
{
uint32_t v_b_231_; uint32_t v___x_232_; uint8_t v___x_233_; 
v_b_231_ = lean_string_utf8_get_fast(v_s_227_, v_p_228_);
v___x_232_ = 95;
v___x_233_ = lean_uint32_dec_eq(v_b_231_, v___x_232_);
if (v___x_233_ == 0)
{
uint32_t v___x_234_; uint8_t v___x_235_; 
v___x_234_ = 120;
v___x_235_ = lean_uint32_dec_eq(v_b_231_, v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = 117;
v___x_237_ = lean_uint32_dec_eq(v_b_231_, v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 85;
v___x_239_ = lean_uint32_dec_eq(v_b_231_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
lean_dec(v_p_228_);
v___x_240_ = 48;
v___x_241_ = lean_uint32_dec_le(v___x_240_, v_b_231_);
if (v___x_241_ == 0)
{
return v___x_239_;
}
else
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 57;
v___x_243_ = lean_uint32_dec_le(v_b_231_, v___x_242_);
return v___x_243_;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = lean_unsigned_to_nat(8u);
v___x_245_ = lean_string_utf8_next_fast(v_s_227_, v_p_228_);
lean_dec(v_p_228_);
v___x_246_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_244_, v_s_227_, v___x_245_);
return v___x_246_;
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(4u);
v___x_248_ = lean_string_utf8_next_fast(v_s_227_, v_p_228_);
lean_dec(v_p_228_);
v___x_249_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_247_, v_s_227_, v___x_248_);
return v___x_249_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_unsigned_to_nat(2u);
v___x_251_ = lean_string_utf8_next_fast(v_s_227_, v_p_228_);
lean_dec(v_p_228_);
v___x_252_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_250_, v_s_227_, v___x_251_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_string_utf8_next_fast(v_s_227_, v_p_228_);
lean_dec(v_p_228_);
v_p_228_ = v___x_253_;
goto _start;
}
}
else
{
lean_dec(v_p_228_);
return v_decide_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* v_s_255_, lean_object* v_p_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_255_, v_p_256_);
lean_dec_ref(v_s_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* v_prev_259_, lean_object* v_next_260_){
_start:
{
if (lean_obj_tag(v_prev_259_) == 1)
{
lean_object* v_str_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v_decide_267_; 
v_str_264_ = lean_ctor_get(v_prev_259_, 1);
v___x_265_ = lean_string_utf8_byte_size(v_str_264_);
v___x_266_ = lean_unsigned_to_nat(0u);
v_decide_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
if (v_decide_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; uint32_t v___x_272_; uint32_t v___x_273_; uint8_t v___x_274_; 
lean_inc_ref(v_str_264_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v_str_264_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_sub(v___x_265_, v___x_269_);
v___x_271_ = l_String_Slice_posLE(v___x_268_, v___x_270_);
lean_dec_ref_known(v___x_268_, 3);
v___x_272_ = lean_string_utf8_get_fast(v_str_264_, v___x_271_);
lean_dec(v___x_271_);
v___x_273_ = 95;
v___x_274_ = lean_uint32_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
goto v___jp_261_;
}
else
{
return v___x_274_;
}
}
else
{
goto v___jp_261_;
}
}
else
{
goto v___jp_261_;
}
v___jp_261_:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_next_260_, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* v_prev_275_, lean_object* v_next_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_275_, v_next_276_);
lean_dec_ref(v_next_276_);
lean_dec(v_prev_275_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* v_x_282_){
_start:
{
switch(lean_obj_tag(v_x_282_))
{
case 0:
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_283_;
}
case 1:
{
lean_object* v_pre_284_; lean_object* v_str_285_; lean_object* v_m_286_; 
v_pre_284_ = lean_ctor_get(v_x_282_, 0);
lean_inc(v_pre_284_);
v_str_285_ = lean_ctor_get(v_x_282_, 1);
lean_inc_ref(v_str_285_);
lean_dec_ref_known(v_x_282_, 2);
v_m_286_ = l_String_Internal_mangle(v_str_285_);
lean_dec_ref(v_str_285_);
if (lean_obj_tag(v_pre_284_) == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_m_286_, v___x_287_);
if (v___x_288_ == 0)
{
return v_m_286_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0));
v___x_290_ = lean_string_append(v___x_289_, v_m_286_);
lean_dec_ref(v_m_286_);
return v___x_290_;
}
}
else
{
lean_object* v_m1_291_; lean_object* v___y_293_; uint8_t v___x_296_; 
lean_inc(v_pre_284_);
v_m1_291_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_284_);
v___x_296_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_pre_284_, v_m_286_);
lean_dec(v_pre_284_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___y_293_ = v___x_297_;
goto v___jp_292_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2));
v___y_293_ = v___x_298_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_string_append(v_m1_291_, v___y_293_);
v___x_295_ = lean_string_append(v___x_294_, v_m_286_);
lean_dec_ref(v_m_286_);
return v___x_295_;
}
}
}
default: 
{
lean_object* v_pre_299_; 
v_pre_299_ = lean_ctor_get(v_x_282_, 0);
if (lean_obj_tag(v_pre_299_) == 0)
{
lean_object* v_i_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_i_300_ = lean_ctor_get(v_x_282_, 1);
lean_inc(v_i_300_);
lean_dec_ref_known(v_x_282_, 2);
v___x_301_ = l_Nat_reprFast(v_i_300_);
v___x_302_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
return v___x_303_;
}
else
{
lean_object* v_i_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc(v_pre_299_);
v_i_304_ = lean_ctor_get(v_x_282_, 1);
lean_inc(v_i_304_);
lean_dec_ref_known(v_x_282_, 2);
v___x_305_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_299_);
v___x_306_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_307_ = lean_string_append(v___x_305_, v___x_306_);
v___x_308_ = l_Nat_reprFast(v_i_304_);
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
lean_dec_ref(v___x_308_);
v___x_310_ = lean_string_append(v___x_309_, v___x_306_);
return v___x_310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* v_n_311_, lean_object* v_pre_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_311_);
v___x_314_ = lean_string_append(v_pre_312_, v___x_313_);
lean_dec_ref(v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object* v_s_317_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_string_utf8_byte_size(v_s_317_);
v___x_322_ = lean_unsigned_to_nat(2u);
v___x_323_ = lean_nat_dec_le(v___x_322_, v___x_321_);
if (v___x_323_ == 0)
{
goto v___jp_318_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_nat_sub(v___x_321_, v___x_322_);
v___x_327_ = lean_string_memcmp(v_s_317_, v___x_324_, v___x_326_, v___x_325_, v___x_322_);
lean_dec(v___x_326_);
if (v___x_327_ == 0)
{
goto v___jp_318_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__1));
v___x_329_ = lean_string_append(v_s_317_, v___x_328_);
return v___x_329_;
}
}
v___jp_318_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__0));
v___x_320_ = lean_string_append(v_s_317_, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object* v_moduleName_330_, lean_object* v_pkg_x3f_331_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_333_ = l_Lean_Name_mangle(v_moduleName_330_, v___x_332_);
return v___x_333_;
}
else
{
lean_object* v_val_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_val_334_ = lean_ctor_get(v_pkg_x3f_331_, 0);
v___x_335_ = l_String_Internal_mangle(v_val_334_);
v___x_336_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_337_ = lean_string_append(v___x_335_, v___x_336_);
v___x_338_ = l_Lean_Name_mangle(v_moduleName_330_, v___x_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object* v_moduleName_339_, lean_object* v_pkg_x3f_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_mkModuleInitializationStem(v_moduleName_339_, v_pkg_x3f_340_);
lean_dec(v_pkg_x3f_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t v_phases_344_){
_start:
{
switch(v_phases_344_)
{
case 0:
{
lean_object* v___x_345_; 
v___x_345_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__0));
return v___x_345_;
}
case 1:
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__1));
return v___x_346_;
}
default: 
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix___boxed(lean_object* v_phases_348_){
_start:
{
uint8_t v_phases_boxed_349_; lean_object* v_res_350_; 
v_phases_boxed_349_ = lean_unbox(v_phases_348_);
v_res_350_ = l_Lean_mkModuleInitializationPrefix(v_phases_boxed_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object* v_moduleName_352_, lean_object* v_pkg_x3f_353_, uint8_t v_phases_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_355_ = l_Lean_mkModuleInitializationPrefix(v_phases_354_);
v___x_356_ = ((lean_object*)(l_Lean_mkModuleInitializationFunctionName___closed__0));
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
v___x_358_ = l_Lean_mkModuleInitializationStem(v_moduleName_352_, v_pkg_x3f_353_);
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
lean_dec_ref(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object* v_moduleName_360_, lean_object* v_pkg_x3f_361_, lean_object* v_phases_362_){
_start:
{
uint8_t v_phases_boxed_363_; lean_object* v_res_364_; 
v_phases_boxed_363_ = lean_unbox(v_phases_362_);
v_res_364_ = l_Lean_mkModuleInitializationFunctionName(v_moduleName_360_, v_pkg_x3f_361_, v_phases_boxed_363_);
lean_dec(v_pkg_x3f_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object* v_pkg_x3f_367_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_367_) == 0)
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__0));
return v___x_368_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_val_369_ = lean_ctor_get(v_pkg_x3f_367_, 0);
v___x_370_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__1));
v___x_371_ = l_String_Internal_mangle(v_val_369_);
v___x_372_ = lean_string_append(v___x_370_, v___x_371_);
lean_dec_ref(v___x_371_);
v___x_373_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object* v_pkg_x3f_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_mkPackageSymbolPrefix(v_pkg_x3f_375_);
lean_dec(v_pkg_x3f_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_zero_379_; uint8_t v_isZero_380_; 
v_zero_379_ = lean_unsigned_to_nat(0u);
v_isZero_380_ = lean_nat_dec_eq(v_x_377_, v_zero_379_);
if (v_isZero_380_ == 1)
{
lean_dec(v_x_377_);
return v_x_378_;
}
else
{
uint32_t v___x_381_; lean_object* v_one_382_; lean_object* v_n_383_; lean_object* v___x_384_; 
v___x_381_ = 95;
v_one_382_ = lean_unsigned_to_nat(1u);
v_n_383_ = lean_nat_sub(v_x_377_, v_one_382_);
lean_dec(v_x_377_);
v___x_384_ = lean_string_push(v_x_378_, v___x_381_);
v_x_377_ = v_n_383_;
v_x_378_ = v___x_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object* v_s_386_, lean_object* v_p_u2080_387_, lean_object* v_res_388_, lean_object* v_acc_389_, lean_object* v_ucount_390_){
_start:
{
lean_object* v___x_391_; uint8_t v_decide_392_; 
v___x_391_ = lean_string_utf8_byte_size(v_s_386_);
v_decide_392_ = lean_nat_dec_eq(v_p_u2080_387_, v___x_391_);
if (v_decide_392_ == 0)
{
uint32_t v_ch_393_; lean_object* v_p_394_; uint32_t v___x_395_; uint8_t v___x_396_; 
v_ch_393_ = lean_string_utf8_get_fast(v_s_386_, v_p_u2080_387_);
v_p_394_ = lean_string_utf8_next_fast(v_s_386_, v_p_u2080_387_);
lean_dec(v_p_u2080_387_);
v___x_395_ = 95;
v___x_396_ = lean_uint32_dec_eq(v_ch_393_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_449_; 
v___x_397_ = lean_unsigned_to_nat(2u);
v___x_398_ = lean_nat_mod(v_ucount_390_, v___x_397_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_nat_dec_eq(v___x_398_, v___x_399_);
lean_dec(v___x_398_);
if (v___x_449_ == 0)
{
uint32_t v___x_450_; uint8_t v___x_451_; 
v___x_450_ = 48;
v___x_451_ = lean_uint32_dec_le(v___x_450_, v_ch_393_);
if (v___x_451_ == 0)
{
goto v___jp_436_;
}
else
{
uint32_t v___x_452_; uint8_t v___x_453_; 
v___x_452_ = 57;
v___x_453_ = lean_uint32_dec_le(v_ch_393_, v___x_452_);
if (v___x_453_ == 0)
{
goto v___jp_436_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_res_457_; uint8_t v___y_463_; uint8_t v___x_469_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_shiftr(v_ucount_390_, v___x_454_);
lean_dec(v_ucount_390_);
v___x_456_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_455_, v_acc_389_);
v_res_457_ = l_Lean_Name_str___override(v_res_388_, v___x_456_);
v___x_469_ = lean_uint32_dec_eq(v_ch_393_, v___x_450_);
if (v___x_469_ == 0)
{
goto v___jp_458_;
}
else
{
uint8_t v_decide_470_; 
v_decide_470_ = lean_nat_dec_eq(v_p_394_, v___x_391_);
if (v_decide_470_ == 0)
{
v___y_463_ = v___x_469_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_449_;
goto v___jp_462_;
}
}
v___jp_458_:
{
uint32_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_uint32_sub(v_ch_393_, v___x_450_);
v___x_460_ = lean_uint32_to_nat(v___x_459_);
v___x_461_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_386_, v_p_394_, v_res_457_, v___x_460_);
return v___x_461_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
goto v___jp_458_;
}
else
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_string_utf8_get_fast(v_s_386_, v_p_394_);
v___x_465_ = lean_uint32_dec_eq(v___x_464_, v___x_450_);
if (v___x_465_ == 0)
{
goto v___jp_458_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_string_utf8_next_fast(v_s_386_, v_p_394_);
v___x_467_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v_p_u2080_387_ = v___x_466_;
v_res_388_ = v_res_457_;
v_acc_389_ = v___x_467_;
v_ucount_390_ = v___x_399_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_shiftr(v_ucount_390_, v___x_471_);
lean_dec(v_ucount_390_);
v___x_473_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_472_, v_acc_389_);
v___x_474_ = lean_string_push(v___x_473_, v_ch_393_);
v_p_u2080_387_ = v_p_394_;
v_acc_389_ = v___x_474_;
v_ucount_390_ = v___x_399_;
goto _start;
}
v___jp_400_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = l_Lean_Name_str___override(v_res_388_, v_acc_389_);
v___x_402_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_shiftr(v_ucount_390_, v___x_403_);
lean_dec(v_ucount_390_);
v___x_405_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_404_, v___x_402_);
v___x_406_ = lean_string_push(v___x_405_, v_ch_393_);
v_p_u2080_387_ = v_p_394_;
v_res_388_ = v___x_401_;
v_acc_389_ = v___x_406_;
v_ucount_390_ = v___x_399_;
goto _start;
}
v___jp_408_:
{
uint32_t v___x_409_; uint8_t v___x_410_; 
v___x_409_ = 85;
v___x_410_ = lean_uint32_dec_eq(v_ch_393_, v___x_409_);
if (v___x_410_ == 0)
{
goto v___jp_400_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(8u);
v___x_412_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_411_, v_s_386_, v_p_394_, v___x_399_);
if (lean_obj_tag(v___x_412_) == 1)
{
lean_object* v_val_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_acc_418_; uint32_t v___x_419_; lean_object* v___x_420_; 
v_val_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_412_, 1);
v_fst_414_ = lean_ctor_get(v_val_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v_val_413_, 1);
lean_inc(v_snd_415_);
lean_dec(v_val_413_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_shiftr(v_ucount_390_, v___x_416_);
lean_dec(v_ucount_390_);
v_acc_418_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_417_, v_acc_389_);
v___x_419_ = l_Char_ofNat(v_snd_415_);
lean_dec(v_snd_415_);
v___x_420_ = lean_string_push(v_acc_418_, v___x_419_);
v_p_u2080_387_ = v_fst_414_;
v_acc_389_ = v___x_420_;
v_ucount_390_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v___x_412_);
goto v___jp_400_;
}
}
}
v___jp_422_:
{
uint32_t v___x_423_; uint8_t v___x_424_; 
v___x_423_ = 117;
v___x_424_ = lean_uint32_dec_eq(v_ch_393_, v___x_423_);
if (v___x_424_ == 0)
{
goto v___jp_408_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(4u);
v___x_426_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_425_, v_s_386_, v_p_394_, v___x_399_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_acc_432_; uint32_t v___x_433_; lean_object* v___x_434_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
v_fst_428_ = lean_ctor_get(v_val_427_, 0);
lean_inc(v_fst_428_);
v_snd_429_ = lean_ctor_get(v_val_427_, 1);
lean_inc(v_snd_429_);
lean_dec(v_val_427_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_shiftr(v_ucount_390_, v___x_430_);
lean_dec(v_ucount_390_);
v_acc_432_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_431_, v_acc_389_);
v___x_433_ = l_Char_ofNat(v_snd_429_);
lean_dec(v_snd_429_);
v___x_434_ = lean_string_push(v_acc_432_, v___x_433_);
v_p_u2080_387_ = v_fst_428_;
v_acc_389_ = v___x_434_;
v_ucount_390_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v___x_426_);
goto v___jp_408_;
}
}
}
v___jp_436_:
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 120;
v___x_438_ = lean_uint32_dec_eq(v_ch_393_, v___x_437_);
if (v___x_438_ == 0)
{
goto v___jp_422_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_397_, v_s_386_, v_p_394_, v___x_399_);
if (lean_obj_tag(v___x_439_) == 1)
{
lean_object* v_val_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_acc_445_; uint32_t v___x_446_; lean_object* v___x_447_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
v_fst_441_ = lean_ctor_get(v_val_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v_val_440_, 1);
lean_inc(v_snd_442_);
lean_dec(v_val_440_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_shiftr(v_ucount_390_, v___x_443_);
lean_dec(v_ucount_390_);
v_acc_445_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_444_, v_acc_389_);
v___x_446_ = l_Char_ofNat(v_snd_442_);
lean_dec(v_snd_442_);
v___x_447_ = lean_string_push(v_acc_445_, v___x_446_);
v_p_u2080_387_ = v_fst_441_;
v_acc_389_ = v___x_447_;
v_ucount_390_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v___x_439_);
goto v___jp_422_;
}
}
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_ucount_390_, v___x_476_);
lean_dec(v_ucount_390_);
v_p_u2080_387_ = v_p_394_;
v_ucount_390_ = v___x_477_;
goto _start;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_p_u2080_387_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_shiftr(v_ucount_390_, v___x_479_);
lean_dec(v_ucount_390_);
v___x_481_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_480_, v_acc_389_);
v___x_482_ = l_Lean_Name_str___override(v_res_388_, v___x_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* v_s_483_, lean_object* v_p_484_, lean_object* v_res_485_){
_start:
{
lean_object* v___x_486_; uint8_t v_decide_487_; 
v___x_486_ = lean_string_utf8_byte_size(v_s_483_);
v_decide_487_ = lean_nat_dec_eq(v_p_484_, v___x_486_);
if (v_decide_487_ == 0)
{
uint32_t v_ch_488_; lean_object* v_p_489_; uint8_t v___y_496_; uint32_t v___x_514_; uint8_t v___x_515_; 
v_ch_488_ = lean_string_utf8_get_fast(v_s_483_, v_p_484_);
v_p_489_ = lean_string_utf8_next_fast(v_s_483_, v_p_484_);
v___x_514_ = 48;
v___x_515_ = lean_uint32_dec_le(v___x_514_, v_ch_488_);
if (v___x_515_ == 0)
{
goto v___jp_504_;
}
else
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 57;
v___x_517_ = lean_uint32_dec_le(v_ch_488_, v___x_516_);
if (v___x_517_ == 0)
{
goto v___jp_504_;
}
else
{
uint8_t v___x_518_; 
v___x_518_ = lean_uint32_dec_eq(v_ch_488_, v___x_514_);
if (v___x_518_ == 0)
{
goto v___jp_490_;
}
else
{
uint8_t v_decide_519_; 
v_decide_519_ = lean_nat_dec_eq(v_p_489_, v___x_486_);
if (v_decide_519_ == 0)
{
v___y_496_ = v___x_518_;
goto v___jp_495_;
}
else
{
v___y_496_ = v_decide_487_;
goto v___jp_495_;
}
}
}
}
v___jp_490_:
{
uint32_t v___x_491_; uint32_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = 48;
v___x_492_ = lean_uint32_sub(v_ch_488_, v___x_491_);
v___x_493_ = lean_uint32_to_nat(v___x_492_);
v___x_494_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_483_, v_p_489_, v_res_485_, v___x_493_);
return v___x_494_;
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
goto v___jp_490_;
}
else
{
uint32_t v___x_497_; uint32_t v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_string_utf8_get_fast(v_s_483_, v_p_489_);
v___x_498_ = 48;
v___x_499_ = lean_uint32_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
goto v___jp_490_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_string_utf8_next_fast(v_s_483_, v_p_489_);
v___x_501_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_483_, v___x_500_, v_res_485_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
}
v___jp_504_:
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 95;
v___x_506_ = lean_uint32_dec_eq(v_ch_488_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_508_ = lean_string_push(v___x_507_, v_ch_488_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_483_, v_p_489_, v_res_485_, v___x_508_, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_483_, v_p_489_, v_res_485_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
}
else
{
return v_res_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* v_s_520_, lean_object* v_p_521_, lean_object* v_res_522_, lean_object* v_n_523_){
_start:
{
lean_object* v___x_524_; uint8_t v_decide_525_; 
v___x_524_ = lean_string_utf8_byte_size(v_s_520_);
v_decide_525_ = lean_nat_dec_eq(v_p_521_, v___x_524_);
if (v_decide_525_ == 0)
{
uint32_t v_ch_526_; lean_object* v_p_527_; uint32_t v___x_533_; uint8_t v___x_534_; 
v_ch_526_ = lean_string_utf8_get_fast(v_s_520_, v_p_521_);
v_p_527_ = lean_string_utf8_next_fast(v_s_520_, v_p_521_);
lean_dec(v_p_521_);
v___x_533_ = 48;
v___x_534_ = lean_uint32_dec_le(v___x_533_, v_ch_526_);
if (v___x_534_ == 0)
{
goto v___jp_528_;
}
else
{
uint32_t v___x_535_; uint8_t v___x_536_; 
v___x_535_ = 57;
v___x_536_ = lean_uint32_dec_le(v_ch_526_, v___x_535_);
if (v___x_536_ == 0)
{
goto v___jp_528_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; uint32_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_537_ = lean_unsigned_to_nat(10u);
v___x_538_ = lean_nat_mul(v_n_523_, v___x_537_);
lean_dec(v_n_523_);
v___x_539_ = lean_uint32_sub(v_ch_526_, v___x_533_);
v___x_540_ = lean_uint32_to_nat(v___x_539_);
v___x_541_ = lean_nat_add(v___x_538_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v___x_538_);
v_p_521_ = v_p_527_;
v_n_523_ = v___x_541_;
goto _start;
}
}
v___jp_528_:
{
lean_object* v_res_529_; uint8_t v_decide_530_; 
v_res_529_ = l_Lean_Name_num___override(v_res_522_, v_n_523_);
v_decide_530_ = lean_nat_dec_eq(v_p_527_, v___x_524_);
if (v_decide_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_string_utf8_next_fast(v_s_520_, v_p_527_);
v___x_532_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_520_, v___x_531_, v_res_529_);
return v___x_532_;
}
else
{
return v_res_529_;
}
}
}
else
{
lean_object* v___x_543_; 
lean_dec(v_p_521_);
v___x_543_ = l_Lean_Name_num___override(v_res_522_, v_n_523_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* v_s_544_, lean_object* v_p_545_, lean_object* v_res_546_, lean_object* v_n_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_544_, v_p_545_, v_res_546_, v_n_547_);
lean_dec_ref(v_s_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* v_s_549_, lean_object* v_p_550_, lean_object* v_res_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_549_, v_p_550_, v_res_551_);
lean_dec(v_p_550_);
lean_dec_ref(v_s_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* v_s_553_, lean_object* v_p_u2080_554_, lean_object* v_res_555_, lean_object* v_acc_556_, lean_object* v_ucount_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_553_, v_p_u2080_554_, v_res_555_, v_acc_556_, v_ucount_557_);
lean_dec_ref(v_s_553_);
return v_res_558_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_559_; lean_object* v___x_560_; 
v___x_559_ = 120;
v___x_560_ = lean_box_uint32(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t v_ch_561_, lean_object* v_x_562_, lean_object* v_h__1_563_, lean_object* v_h__2_564_){
_start:
{
uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = 120;
v___x_566_ = lean_uint32_dec_eq(v_ch_561_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_h__1_563_);
v___x_567_ = lean_box_uint32(v_ch_561_);
v___x_568_ = lean_apply_4(v_h__2_564_, v___x_567_, v_x_562_, lean_box(0), lean_box(0));
return v___x_568_;
}
else
{
if (lean_obj_tag(v_x_562_) == 1)
{
lean_object* v_val_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; 
lean_dec(v_h__2_564_);
v_val_569_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_val_569_);
lean_dec_ref_known(v_x_562_, 1);
v_fst_570_ = lean_ctor_get(v_val_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v_val_569_, 1);
lean_inc(v_snd_571_);
lean_dec(v_val_569_);
v___x_572_ = lean_apply_3(v_h__1_563_, v_fst_570_, v_snd_571_, lean_box(0));
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_h__1_563_);
v___x_573_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_574_ = lean_apply_4(v_h__2_564_, v___x_573_, v_x_562_, lean_box(0), lean_box(0));
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* v_ch_575_, lean_object* v_x_576_, lean_object* v_h__1_577_, lean_object* v_h__2_578_){
_start:
{
uint32_t v_ch_87__boxed_579_; lean_object* v_res_580_; 
v_ch_87__boxed_579_ = lean_unbox_uint32(v_ch_575_);
lean_dec(v_ch_575_);
v_res_580_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_87__boxed_579_, v_x_576_, v_h__1_577_, v_h__2_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* v_s_581_, lean_object* v_motive_582_, uint32_t v_ch_583_, lean_object* v_x_584_, lean_object* v_h__1_585_, lean_object* v_h__2_586_){
_start:
{
uint32_t v___x_587_; uint8_t v___x_588_; 
v___x_587_ = 120;
v___x_588_ = lean_uint32_dec_eq(v_ch_583_, v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_h__1_585_);
v___x_589_ = lean_box_uint32(v_ch_583_);
v___x_590_ = lean_apply_4(v_h__2_586_, v___x_589_, v_x_584_, lean_box(0), lean_box(0));
return v___x_590_;
}
else
{
if (lean_obj_tag(v_x_584_) == 1)
{
lean_object* v_val_591_; lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_594_; 
lean_dec(v_h__2_586_);
v_val_591_ = lean_ctor_get(v_x_584_, 0);
lean_inc(v_val_591_);
lean_dec_ref_known(v_x_584_, 1);
v_fst_592_ = lean_ctor_get(v_val_591_, 0);
lean_inc(v_fst_592_);
v_snd_593_ = lean_ctor_get(v_val_591_, 1);
lean_inc(v_snd_593_);
lean_dec(v_val_591_);
v___x_594_ = lean_apply_3(v_h__1_585_, v_fst_592_, v_snd_593_, lean_box(0));
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_h__1_585_);
v___x_595_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_596_ = lean_apply_4(v_h__2_586_, v___x_595_, v_x_584_, lean_box(0), lean_box(0));
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* v_s_597_, lean_object* v_motive_598_, lean_object* v_ch_599_, lean_object* v_x_600_, lean_object* v_h__1_601_, lean_object* v_h__2_602_){
_start:
{
uint32_t v_ch_117__boxed_603_; lean_object* v_res_604_; 
v_ch_117__boxed_603_ = lean_unbox_uint32(v_ch_599_);
lean_dec(v_ch_599_);
v_res_604_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_597_, v_motive_598_, v_ch_117__boxed_603_, v_x_600_, v_h__1_601_, v_h__2_602_);
lean_dec_ref(v_s_597_);
return v_res_604_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_605_; lean_object* v___x_606_; 
v___x_605_ = 117;
v___x_606_ = lean_box_uint32(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t v_ch_607_, lean_object* v_x_608_, lean_object* v_h__1_609_, lean_object* v_h__2_610_){
_start:
{
uint32_t v___x_611_; uint8_t v___x_612_; 
v___x_611_ = 117;
v___x_612_ = lean_uint32_dec_eq(v_ch_607_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_h__1_609_);
v___x_613_ = lean_box_uint32(v_ch_607_);
v___x_614_ = lean_apply_4(v_h__2_610_, v___x_613_, v_x_608_, lean_box(0), lean_box(0));
return v___x_614_;
}
else
{
if (lean_obj_tag(v_x_608_) == 1)
{
lean_object* v_val_615_; lean_object* v_fst_616_; lean_object* v_snd_617_; lean_object* v___x_618_; 
lean_dec(v_h__2_610_);
v_val_615_ = lean_ctor_get(v_x_608_, 0);
lean_inc(v_val_615_);
lean_dec_ref_known(v_x_608_, 1);
v_fst_616_ = lean_ctor_get(v_val_615_, 0);
lean_inc(v_fst_616_);
v_snd_617_ = lean_ctor_get(v_val_615_, 1);
lean_inc(v_snd_617_);
lean_dec(v_val_615_);
v___x_618_ = lean_apply_3(v_h__1_609_, v_fst_616_, v_snd_617_, lean_box(0));
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_h__1_609_);
v___x_619_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_620_ = lean_apply_4(v_h__2_610_, v___x_619_, v_x_608_, lean_box(0), lean_box(0));
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* v_ch_621_, lean_object* v_x_622_, lean_object* v_h__1_623_, lean_object* v_h__2_624_){
_start:
{
uint32_t v_ch_87__boxed_625_; lean_object* v_res_626_; 
v_ch_87__boxed_625_ = lean_unbox_uint32(v_ch_621_);
lean_dec(v_ch_621_);
v_res_626_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_87__boxed_625_, v_x_622_, v_h__1_623_, v_h__2_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* v_s_627_, lean_object* v_motive_628_, uint32_t v_ch_629_, lean_object* v_x_630_, lean_object* v_h__1_631_, lean_object* v_h__2_632_){
_start:
{
uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_633_ = 117;
v___x_634_ = lean_uint32_dec_eq(v_ch_629_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_h__1_631_);
v___x_635_ = lean_box_uint32(v_ch_629_);
v___x_636_ = lean_apply_4(v_h__2_632_, v___x_635_, v_x_630_, lean_box(0), lean_box(0));
return v___x_636_;
}
else
{
if (lean_obj_tag(v_x_630_) == 1)
{
lean_object* v_val_637_; lean_object* v_fst_638_; lean_object* v_snd_639_; lean_object* v___x_640_; 
lean_dec(v_h__2_632_);
v_val_637_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_x_630_, 1);
v_fst_638_ = lean_ctor_get(v_val_637_, 0);
lean_inc(v_fst_638_);
v_snd_639_ = lean_ctor_get(v_val_637_, 1);
lean_inc(v_snd_639_);
lean_dec(v_val_637_);
v___x_640_ = lean_apply_3(v_h__1_631_, v_fst_638_, v_snd_639_, lean_box(0));
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_h__1_631_);
v___x_641_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_642_ = lean_apply_4(v_h__2_632_, v___x_641_, v_x_630_, lean_box(0), lean_box(0));
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* v_s_643_, lean_object* v_motive_644_, lean_object* v_ch_645_, lean_object* v_x_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_){
_start:
{
uint32_t v_ch_117__boxed_649_; lean_object* v_res_650_; 
v_ch_117__boxed_649_ = lean_unbox_uint32(v_ch_645_);
lean_dec(v_ch_645_);
v_res_650_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_643_, v_motive_644_, v_ch_117__boxed_649_, v_x_646_, v_h__1_647_, v_h__2_648_);
lean_dec_ref(v_s_643_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_651_; lean_object* v___x_652_; 
v___x_651_ = 85;
v___x_652_ = lean_box_uint32(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t v_ch_653_, lean_object* v_x_654_, lean_object* v_h__1_655_, lean_object* v_h__2_656_){
_start:
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 85;
v___x_658_ = lean_uint32_dec_eq(v_ch_653_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v_h__1_655_);
v___x_659_ = lean_box_uint32(v_ch_653_);
v___x_660_ = lean_apply_4(v_h__2_656_, v___x_659_, v_x_654_, lean_box(0), lean_box(0));
return v___x_660_;
}
else
{
if (lean_obj_tag(v_x_654_) == 1)
{
lean_object* v_val_661_; lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_664_; 
lean_dec(v_h__2_656_);
v_val_661_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_x_654_, 1);
v_fst_662_ = lean_ctor_get(v_val_661_, 0);
lean_inc(v_fst_662_);
v_snd_663_ = lean_ctor_get(v_val_661_, 1);
lean_inc(v_snd_663_);
lean_dec(v_val_661_);
v___x_664_ = lean_apply_3(v_h__1_655_, v_fst_662_, v_snd_663_, lean_box(0));
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_h__1_655_);
v___x_665_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_666_ = lean_apply_4(v_h__2_656_, v___x_665_, v_x_654_, lean_box(0), lean_box(0));
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* v_ch_667_, lean_object* v_x_668_, lean_object* v_h__1_669_, lean_object* v_h__2_670_){
_start:
{
uint32_t v_ch_87__boxed_671_; lean_object* v_res_672_; 
v_ch_87__boxed_671_ = lean_unbox_uint32(v_ch_667_);
lean_dec(v_ch_667_);
v_res_672_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_87__boxed_671_, v_x_668_, v_h__1_669_, v_h__2_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* v_s_673_, lean_object* v_motive_674_, uint32_t v_ch_675_, lean_object* v_x_676_, lean_object* v_h__1_677_, lean_object* v_h__2_678_){
_start:
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 85;
v___x_680_ = lean_uint32_dec_eq(v_ch_675_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_h__1_677_);
v___x_681_ = lean_box_uint32(v_ch_675_);
v___x_682_ = lean_apply_4(v_h__2_678_, v___x_681_, v_x_676_, lean_box(0), lean_box(0));
return v___x_682_;
}
else
{
if (lean_obj_tag(v_x_676_) == 1)
{
lean_object* v_val_683_; lean_object* v_fst_684_; lean_object* v_snd_685_; lean_object* v___x_686_; 
lean_dec(v_h__2_678_);
v_val_683_ = lean_ctor_get(v_x_676_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v_x_676_, 1);
v_fst_684_ = lean_ctor_get(v_val_683_, 0);
lean_inc(v_fst_684_);
v_snd_685_ = lean_ctor_get(v_val_683_, 1);
lean_inc(v_snd_685_);
lean_dec(v_val_683_);
v___x_686_ = lean_apply_3(v_h__1_677_, v_fst_684_, v_snd_685_, lean_box(0));
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_h__1_677_);
v___x_687_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_688_ = lean_apply_4(v_h__2_678_, v___x_687_, v_x_676_, lean_box(0), lean_box(0));
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* v_s_689_, lean_object* v_motive_690_, lean_object* v_ch_691_, lean_object* v_x_692_, lean_object* v_h__1_693_, lean_object* v_h__2_694_){
_start:
{
uint32_t v_ch_117__boxed_695_; lean_object* v_res_696_; 
v_ch_117__boxed_695_ = lean_unbox_uint32(v_ch_691_);
lean_dec(v_ch_691_);
v_res_696_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_689_, v_motive_690_, v_ch_117__boxed_695_, v_x_692_, v_h__1_693_, v_h__2_694_);
lean_dec_ref(v_s_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* v_s_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_box(0);
v___x_700_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_697_, v___x_698_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* v_s_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Name_demangle(v_s_701_);
lean_dec_ref(v_s_701_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* v_s_703_){
_start:
{
lean_object* v_n_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_n_704_ = l_Lean_Name_demangle(v_s_703_);
lean_inc(v_n_704_);
v___x_705_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_704_);
v___x_706_ = lean_string_dec_eq(v___x_705_, v_s_703_);
lean_dec_ref(v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec(v_n_704_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_n_704_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* v_s_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Name_demangle_x3f(v_s_709_);
lean_dec_ref(v_s_709_);
return v_res_710_;
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
