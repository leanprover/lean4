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
uint32_t v_c_50_; lean_object* v_pos_51_; uint8_t v___y_87_; uint32_t v___x_92_; uint8_t v___x_93_; 
v_c_50_ = lean_string_utf8_get_fast(v_s_45_, v_pos_46_);
v_pos_51_ = lean_string_utf8_next_fast(v_s_45_, v_pos_46_);
lean_dec(v_pos_46_);
v___x_92_ = 65;
v___x_93_ = lean_uint32_dec_le(v___x_92_, v_c_50_);
if (v___x_93_ == 0)
{
v___y_87_ = v___x_93_;
goto v___jp_86_;
}
else
{
uint32_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = 90;
v___x_95_ = lean_uint32_dec_le(v_c_50_, v___x_94_);
v___y_87_ = v___x_95_;
goto v___jp_86_;
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
if (v___y_87_ == 0)
{
uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_88_ = 97;
v___x_89_ = lean_uint32_dec_le(v___x_88_, v_c_50_);
if (v___x_89_ == 0)
{
goto v___jp_81_;
}
else
{
uint32_t v___x_90_; uint8_t v___x_91_; 
v___x_90_ = 122;
v___x_91_ = lean_uint32_dec_le(v_c_50_, v___x_90_);
if (v___x_91_ == 0)
{
goto v___jp_81_;
}
else
{
goto v___jp_78_;
}
}
}
else
{
goto v___jp_78_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object* v_s_96_, lean_object* v_pos_97_, lean_object* v_r_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_96_, v_pos_97_, v_r_98_);
lean_dec_ref(v_s_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle(lean_object* v_s_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_104_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_101_, v___x_102_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_mangle___boxed(lean_object* v_s_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_String_Internal_mangle(v_s_105_);
lean_dec_ref(v_s_105_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object* v_x_107_, lean_object* v_x_108_, lean_object* v_x_109_){
_start:
{
lean_object* v_zero_110_; uint8_t v_isZero_111_; 
v_zero_110_ = lean_unsigned_to_nat(0u);
v_isZero_111_ = lean_nat_dec_eq(v_x_107_, v_zero_110_);
if (v_isZero_111_ == 1)
{
lean_dec(v_x_109_);
lean_dec(v_x_107_);
return v_isZero_111_;
}
else
{
lean_object* v___x_112_; uint8_t v_decide_113_; 
v___x_112_ = lean_string_utf8_byte_size(v_x_108_);
v_decide_113_ = lean_nat_dec_eq(v_x_109_, v___x_112_);
if (v_decide_113_ == 0)
{
lean_object* v_one_114_; lean_object* v_n_115_; uint32_t v_ch_119_; uint32_t v___x_125_; uint8_t v___x_126_; 
v_one_114_ = lean_unsigned_to_nat(1u);
v_n_115_ = lean_nat_sub(v_x_107_, v_one_114_);
lean_dec(v_x_107_);
v_ch_119_ = lean_string_utf8_get_fast(v_x_108_, v_x_109_);
v___x_125_ = 48;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_ch_119_);
if (v___x_126_ == 0)
{
goto v___jp_120_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 57;
v___x_128_ = lean_uint32_dec_le(v_ch_119_, v___x_127_);
if (v___x_128_ == 0)
{
goto v___jp_120_;
}
else
{
goto v___jp_116_;
}
}
v___jp_116_:
{
lean_object* v___x_117_; 
v___x_117_ = lean_string_utf8_next_fast(v_x_108_, v_x_109_);
lean_dec(v_x_109_);
v_x_107_ = v_n_115_;
v_x_109_ = v___x_117_;
goto _start;
}
v___jp_120_:
{
uint32_t v___x_121_; uint8_t v___x_122_; 
v___x_121_ = 97;
v___x_122_ = lean_uint32_dec_le(v___x_121_, v_ch_119_);
if (v___x_122_ == 0)
{
lean_dec(v_n_115_);
lean_dec(v_x_109_);
return v_decide_113_;
}
else
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 102;
v___x_124_ = lean_uint32_dec_le(v_ch_119_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_n_115_);
lean_dec(v_x_109_);
return v_decide_113_;
}
else
{
goto v___jp_116_;
}
}
}
}
else
{
lean_dec(v_x_109_);
lean_dec(v_x_107_);
return v_isZero_111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_129_, v_x_130_, v_x_131_);
lean_dec_ref(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t v_c_134_){
_start:
{
uint32_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = 48;
v___x_147_ = lean_uint32_dec_le(v___x_146_, v_c_134_);
if (v___x_147_ == 0)
{
goto v___jp_135_;
}
else
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 57;
v___x_149_ = lean_uint32_dec_le(v_c_134_, v___x_148_);
if (v___x_149_ == 0)
{
goto v___jp_135_;
}
else
{
uint32_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_uint32_sub(v_c_134_, v___x_146_);
v___x_151_ = lean_uint32_to_nat(v___x_150_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
v___jp_135_:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 97;
v___x_137_ = lean_uint32_dec_le(v___x_136_, v_c_134_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
uint32_t v___x_139_; uint8_t v___x_140_; 
v___x_139_ = 102;
v___x_140_ = lean_uint32_dec_le(v_c_134_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
uint32_t v___x_142_; uint32_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = 87;
v___x_143_ = lean_uint32_sub(v_c_134_, v___x_142_);
v___x_144_ = lean_uint32_to_nat(v___x_143_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object* v_c_153_){
_start:
{
uint32_t v_c_boxed_154_; lean_object* v_res_155_; 
v_c_boxed_154_ = lean_unbox_uint32(v_c_153_);
lean_dec(v_c_153_);
v_res_155_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_boxed_154_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object* v_k_156_, lean_object* v_s_157_, lean_object* v_p_158_, lean_object* v_acc_159_){
_start:
{
lean_object* v_zero_160_; uint8_t v_isZero_161_; 
v_zero_160_ = lean_unsigned_to_nat(0u);
v_isZero_161_ = lean_nat_dec_eq(v_k_156_, v_zero_160_);
if (v_isZero_161_ == 1)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_k_156_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_p_158_);
lean_ctor_set(v___x_162_, 1, v_acc_159_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; uint8_t v_decide_165_; 
v___x_164_ = lean_string_utf8_byte_size(v_s_157_);
v_decide_165_ = lean_nat_dec_eq(v_p_158_, v___x_164_);
if (v_decide_165_ == 0)
{
uint32_t v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_string_utf8_get_fast(v_s_157_, v_p_158_);
v___x_167_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v___x_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; 
lean_dec(v_acc_159_);
lean_dec(v_p_158_);
lean_dec(v_k_156_);
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v_one_170_; lean_object* v_n_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_val_169_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_167_, 1);
v_one_170_ = lean_unsigned_to_nat(1u);
v_n_171_ = lean_nat_sub(v_k_156_, v_one_170_);
lean_dec(v_k_156_);
v___x_172_ = lean_string_utf8_next_fast(v_s_157_, v_p_158_);
lean_dec(v_p_158_);
v___x_173_ = lean_unsigned_to_nat(4u);
v___x_174_ = lean_nat_shiftl(v_acc_159_, v___x_173_);
lean_dec(v_acc_159_);
v___x_175_ = lean_nat_lor(v___x_174_, v_val_169_);
lean_dec(v_val_169_);
lean_dec(v___x_174_);
v_k_156_ = v_n_171_;
v_p_158_ = v___x_172_;
v_acc_159_ = v___x_175_;
goto _start;
}
}
else
{
lean_object* v___x_177_; 
lean_dec(v_acc_159_);
lean_dec(v_p_158_);
lean_dec(v_k_156_);
v___x_177_ = lean_box(0);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object* v_k_178_, lean_object* v_s_179_, lean_object* v_p_180_, lean_object* v_acc_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v_k_178_, v_s_179_, v_p_180_, v_acc_181_);
lean_dec_ref(v_s_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object* v_n_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_){
_start:
{
lean_object* v_zero_186_; uint8_t v_isZero_187_; 
v_zero_186_ = lean_unsigned_to_nat(0u);
v_isZero_187_ = lean_nat_dec_eq(v_n_183_, v_zero_186_);
if (v_isZero_187_ == 1)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec(v_h__2_185_);
v___x_188_ = lean_box(0);
v___x_189_ = lean_apply_1(v_h__1_184_, v___x_188_);
return v___x_189_;
}
else
{
lean_object* v_one_190_; lean_object* v_n_191_; lean_object* v___x_192_; 
lean_dec(v_h__1_184_);
v_one_190_ = lean_unsigned_to_nat(1u);
v_n_191_ = lean_nat_sub(v_n_183_, v_one_190_);
v___x_192_ = lean_apply_1(v_h__2_185_, v_n_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object* v_n_193_, lean_object* v_h__1_194_, lean_object* v_h__2_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(v_n_193_, v_h__1_194_, v_h__2_195_);
lean_dec(v_n_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object* v_motive_197_, lean_object* v_n_198_, lean_object* v_h__1_199_, lean_object* v_h__2_200_){
_start:
{
lean_object* v_zero_201_; uint8_t v_isZero_202_; 
v_zero_201_ = lean_unsigned_to_nat(0u);
v_isZero_202_ = lean_nat_dec_eq(v_n_198_, v_zero_201_);
if (v_isZero_202_ == 1)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_h__2_200_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_apply_1(v_h__1_199_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_one_205_; lean_object* v_n_206_; lean_object* v___x_207_; 
lean_dec(v_h__1_199_);
v_one_205_ = lean_unsigned_to_nat(1u);
v_n_206_ = lean_nat_sub(v_n_198_, v_one_205_);
v___x_207_ = lean_apply_1(v_h__2_200_, v_n_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* v_motive_208_, lean_object* v_n_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(v_motive_208_, v_n_209_, v_h__1_210_, v_h__2_211_);
lean_dec(v_n_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* v_x_213_, lean_object* v_h__1_214_, lean_object* v_h__2_215_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_h__1_214_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v_h__2_215_, v___x_216_);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
lean_dec(v_h__2_215_);
v_val_218_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v_x_213_, 1);
v___x_219_ = lean_apply_1(v_h__1_214_, v_val_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* v_motive_220_, lean_object* v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_h__1_222_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_apply_1(v_h__2_223_, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_227_; 
lean_dec(v_h__2_223_);
v_val_226_ = lean_ctor_get(v_x_221_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v_x_221_, 1);
v___x_227_ = lean_apply_1(v_h__1_222_, v_val_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* v_s_228_, lean_object* v_p_229_){
_start:
{
lean_object* v___x_230_; uint8_t v_decide_231_; 
v___x_230_ = lean_string_utf8_byte_size(v_s_228_);
v_decide_231_ = lean_nat_dec_eq(v_p_229_, v___x_230_);
if (v_decide_231_ == 0)
{
uint32_t v_b_232_; uint32_t v___x_233_; uint8_t v___x_234_; 
v_b_232_ = lean_string_utf8_get_fast(v_s_228_, v_p_229_);
v___x_233_ = 95;
v___x_234_ = lean_uint32_dec_eq(v_b_232_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 120;
v___x_236_ = lean_uint32_dec_eq(v_b_232_, v___x_235_);
if (v___x_236_ == 0)
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 117;
v___x_238_ = lean_uint32_dec_eq(v_b_232_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 85;
v___x_240_ = lean_uint32_dec_eq(v_b_232_, v___x_239_);
if (v___x_240_ == 0)
{
uint32_t v___x_241_; uint8_t v___x_242_; 
lean_dec(v_p_229_);
v___x_241_ = 48;
v___x_242_ = lean_uint32_dec_le(v___x_241_, v_b_232_);
if (v___x_242_ == 0)
{
return v___x_240_;
}
else
{
uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_243_ = 57;
v___x_244_ = lean_uint32_dec_le(v_b_232_, v___x_243_);
return v___x_244_;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_unsigned_to_nat(8u);
v___x_246_ = lean_string_utf8_next_fast(v_s_228_, v_p_229_);
lean_dec(v_p_229_);
v___x_247_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_245_, v_s_228_, v___x_246_);
return v___x_247_;
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_248_ = lean_unsigned_to_nat(4u);
v___x_249_ = lean_string_utf8_next_fast(v_s_228_, v_p_229_);
lean_dec(v_p_229_);
v___x_250_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_248_, v_s_228_, v___x_249_);
return v___x_250_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(2u);
v___x_252_ = lean_string_utf8_next_fast(v_s_228_, v_p_229_);
lean_dec(v_p_229_);
v___x_253_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_251_, v_s_228_, v___x_252_);
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; 
v___x_254_ = lean_string_utf8_next_fast(v_s_228_, v_p_229_);
lean_dec(v_p_229_);
v_p_229_ = v___x_254_;
goto _start;
}
}
else
{
lean_dec(v_p_229_);
return v_decide_231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* v_s_256_, lean_object* v_p_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_256_, v_p_257_);
lean_dec_ref(v_s_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* v_prev_260_, lean_object* v_next_261_){
_start:
{
if (lean_obj_tag(v_prev_260_) == 1)
{
lean_object* v_str_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v_decide_268_; 
v_str_265_ = lean_ctor_get(v_prev_260_, 1);
v___x_266_ = lean_string_utf8_byte_size(v_str_265_);
v___x_267_ = lean_unsigned_to_nat(0u);
v_decide_268_ = lean_nat_dec_eq(v___x_266_, v___x_267_);
if (v_decide_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint32_t v___x_273_; uint32_t v___x_274_; uint8_t v___x_275_; 
lean_inc_ref(v_str_265_);
v___x_269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_269_, 0, v_str_265_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_sub(v___x_266_, v___x_270_);
v___x_272_ = l_String_Slice_posLE(v___x_269_, v___x_271_);
lean_dec_ref_known(v___x_269_, 3);
v___x_273_ = lean_string_utf8_get_fast(v_str_265_, v___x_272_);
lean_dec(v___x_272_);
v___x_274_ = 95;
v___x_275_ = lean_uint32_dec_eq(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
goto v___jp_262_;
}
else
{
return v___x_275_;
}
}
else
{
goto v___jp_262_;
}
}
else
{
goto v___jp_262_;
}
v___jp_262_:
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_next_261_, v___x_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* v_prev_276_, lean_object* v_next_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_276_, v_next_277_);
lean_dec_ref(v_next_277_);
lean_dec(v_prev_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* v_x_283_){
_start:
{
switch(lean_obj_tag(v_x_283_))
{
case 0:
{
lean_object* v___x_284_; 
v___x_284_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_284_;
}
case 1:
{
lean_object* v_pre_285_; lean_object* v_str_286_; lean_object* v_m_287_; 
v_pre_285_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_pre_285_);
v_str_286_ = lean_ctor_get(v_x_283_, 1);
lean_inc_ref(v_str_286_);
lean_dec_ref_known(v_x_283_, 2);
v_m_287_ = l_String_Internal_mangle(v_str_286_);
lean_dec_ref(v_str_286_);
if (lean_obj_tag(v_pre_285_) == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_m_287_, v___x_288_);
if (v___x_289_ == 0)
{
return v_m_287_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0));
v___x_291_ = lean_string_append(v___x_290_, v_m_287_);
lean_dec_ref(v_m_287_);
return v___x_291_;
}
}
else
{
lean_object* v_m1_292_; lean_object* v___y_294_; uint8_t v___x_297_; 
lean_inc(v_pre_285_);
v_m1_292_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_285_);
v___x_297_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_pre_285_, v_m_287_);
lean_dec(v_pre_285_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___y_294_ = v___x_298_;
goto v___jp_293_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2));
v___y_294_ = v___x_299_;
goto v___jp_293_;
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_string_append(v_m1_292_, v___y_294_);
v___x_296_ = lean_string_append(v___x_295_, v_m_287_);
lean_dec_ref(v_m_287_);
return v___x_296_;
}
}
}
default: 
{
lean_object* v_pre_300_; 
v_pre_300_ = lean_ctor_get(v_x_283_, 0);
if (lean_obj_tag(v_pre_300_) == 0)
{
lean_object* v_i_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_i_301_ = lean_ctor_get(v_x_283_, 1);
lean_inc(v_i_301_);
lean_dec_ref_known(v_x_283_, 2);
v___x_302_ = l_Nat_reprFast(v_i_301_);
v___x_303_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_i_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_inc(v_pre_300_);
v_i_305_ = lean_ctor_get(v_x_283_, 1);
lean_inc(v_i_305_);
lean_dec_ref_known(v_x_283_, 2);
v___x_306_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_300_);
v___x_307_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v___x_309_ = l_Nat_reprFast(v_i_305_);
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
lean_dec_ref(v___x_309_);
v___x_311_ = lean_string_append(v___x_310_, v___x_307_);
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* v_n_312_, lean_object* v_pre_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_312_);
v___x_315_ = lean_string_append(v_pre_313_, v___x_314_);
lean_dec_ref(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object* v_s_318_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = lean_string_utf8_byte_size(v_s_318_);
v___x_323_ = lean_unsigned_to_nat(2u);
v___x_324_ = lean_nat_dec_le(v___x_323_, v___x_322_);
if (v___x_324_ == 0)
{
goto v___jp_319_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_325_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_nat_sub(v___x_322_, v___x_323_);
v___x_328_ = lean_string_memcmp(v_s_318_, v___x_325_, v___x_327_, v___x_326_, v___x_323_);
lean_dec(v___x_327_);
if (v___x_328_ == 0)
{
goto v___jp_319_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__1));
v___x_330_ = lean_string_append(v_s_318_, v___x_329_);
return v___x_330_;
}
}
v___jp_319_:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__0));
v___x_321_ = lean_string_append(v_s_318_, v___x_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object* v_moduleName_331_, lean_object* v_pkg_x3f_332_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_332_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_334_ = l_Lean_Name_mangle(v_moduleName_331_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_335_ = lean_ctor_get(v_pkg_x3f_332_, 0);
v___x_336_ = l_String_Internal_mangle(v_val_335_);
v___x_337_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
v___x_339_ = l_Lean_Name_mangle(v_moduleName_331_, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object* v_moduleName_340_, lean_object* v_pkg_x3f_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_mkModuleInitializationStem(v_moduleName_340_, v_pkg_x3f_341_);
lean_dec(v_pkg_x3f_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t v_phases_345_){
_start:
{
switch(v_phases_345_)
{
case 0:
{
lean_object* v___x_346_; 
v___x_346_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__0));
return v___x_346_;
}
case 1:
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__1));
return v___x_347_;
}
default: 
{
lean_object* v___x_348_; 
v___x_348_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix___boxed(lean_object* v_phases_349_){
_start:
{
uint8_t v_phases_boxed_350_; lean_object* v_res_351_; 
v_phases_boxed_350_ = lean_unbox(v_phases_349_);
v_res_351_ = l_Lean_mkModuleInitializationPrefix(v_phases_boxed_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object* v_moduleName_353_, lean_object* v_pkg_x3f_354_, uint8_t v_phases_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_356_ = l_Lean_mkModuleInitializationPrefix(v_phases_355_);
v___x_357_ = ((lean_object*)(l_Lean_mkModuleInitializationFunctionName___closed__0));
v___x_358_ = lean_string_append(v___x_356_, v___x_357_);
v___x_359_ = l_Lean_mkModuleInitializationStem(v_moduleName_353_, v_pkg_x3f_354_);
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
lean_dec_ref(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object* v_moduleName_361_, lean_object* v_pkg_x3f_362_, lean_object* v_phases_363_){
_start:
{
uint8_t v_phases_boxed_364_; lean_object* v_res_365_; 
v_phases_boxed_364_ = lean_unbox(v_phases_363_);
v_res_365_ = l_Lean_mkModuleInitializationFunctionName(v_moduleName_361_, v_pkg_x3f_362_, v_phases_boxed_364_);
lean_dec(v_pkg_x3f_362_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object* v_pkg_x3f_368_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_368_) == 0)
{
lean_object* v___x_369_; 
v___x_369_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__0));
return v___x_369_;
}
else
{
lean_object* v_val_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_val_370_ = lean_ctor_get(v_pkg_x3f_368_, 0);
v___x_371_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__1));
v___x_372_ = l_String_Internal_mangle(v_val_370_);
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
lean_dec_ref(v___x_372_);
v___x_374_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object* v_pkg_x3f_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_mkPackageSymbolPrefix(v_pkg_x3f_376_);
lean_dec(v_pkg_x3f_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v_zero_380_; uint8_t v_isZero_381_; 
v_zero_380_ = lean_unsigned_to_nat(0u);
v_isZero_381_ = lean_nat_dec_eq(v_x_378_, v_zero_380_);
if (v_isZero_381_ == 1)
{
lean_dec(v_x_378_);
return v_x_379_;
}
else
{
uint32_t v___x_382_; lean_object* v_one_383_; lean_object* v_n_384_; lean_object* v___x_385_; 
v___x_382_ = 95;
v_one_383_ = lean_unsigned_to_nat(1u);
v_n_384_ = lean_nat_sub(v_x_378_, v_one_383_);
lean_dec(v_x_378_);
v___x_385_ = lean_string_push(v_x_379_, v___x_382_);
v_x_378_ = v_n_384_;
v_x_379_ = v___x_385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object* v_s_387_, lean_object* v_p_u2080_388_, lean_object* v_res_389_, lean_object* v_acc_390_, lean_object* v_ucount_391_){
_start:
{
lean_object* v___x_392_; uint8_t v_decide_393_; 
v___x_392_ = lean_string_utf8_byte_size(v_s_387_);
v_decide_393_ = lean_nat_dec_eq(v_p_u2080_388_, v___x_392_);
if (v_decide_393_ == 0)
{
uint32_t v_ch_394_; lean_object* v_p_395_; uint32_t v___x_396_; uint8_t v___x_397_; 
v_ch_394_ = lean_string_utf8_get_fast(v_s_387_, v_p_u2080_388_);
v_p_395_ = lean_string_utf8_next_fast(v_s_387_, v_p_u2080_388_);
lean_dec(v_p_u2080_388_);
v___x_396_ = 95;
v___x_397_ = lean_uint32_dec_eq(v_ch_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_450_; 
v___x_398_ = lean_unsigned_to_nat(2u);
v___x_399_ = lean_nat_mod(v_ucount_391_, v___x_398_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_nat_dec_eq(v___x_399_, v___x_400_);
lean_dec(v___x_399_);
if (v___x_450_ == 0)
{
uint32_t v___x_451_; uint8_t v___x_452_; 
v___x_451_ = 48;
v___x_452_ = lean_uint32_dec_le(v___x_451_, v_ch_394_);
if (v___x_452_ == 0)
{
goto v___jp_437_;
}
else
{
uint32_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = 57;
v___x_454_ = lean_uint32_dec_le(v_ch_394_, v___x_453_);
if (v___x_454_ == 0)
{
goto v___jp_437_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v_res_458_; uint8_t v___y_460_; uint8_t v___x_467_; uint8_t v___y_469_; uint8_t v___y_471_; uint8_t v_decide_474_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_shiftr(v_ucount_391_, v___x_455_);
lean_dec(v_ucount_391_);
v___x_457_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_456_, v_acc_390_);
v_res_458_ = l_Lean_Name_str___override(v_res_389_, v___x_457_);
v___x_467_ = lean_uint32_dec_eq(v_ch_394_, v___x_451_);
v_decide_474_ = lean_nat_dec_eq(v_p_395_, v___x_392_);
if (v_decide_474_ == 0)
{
v___y_471_ = v___x_454_;
goto v___jp_470_;
}
else
{
v___y_471_ = v___x_450_;
goto v___jp_470_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
uint32_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_uint32_sub(v_ch_394_, v___x_451_);
v___x_462_ = lean_uint32_to_nat(v___x_461_);
v___x_463_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_387_, v_p_395_, v_res_458_, v___x_462_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_string_utf8_next_fast(v_s_387_, v_p_395_);
v___x_465_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v_p_u2080_388_ = v___x_464_;
v_res_389_ = v_res_458_;
v_acc_390_ = v___x_465_;
v_ucount_391_ = v___x_400_;
goto _start;
}
}
v___jp_468_:
{
if (v___x_467_ == 0)
{
v___y_460_ = v___x_467_;
goto v___jp_459_;
}
else
{
v___y_460_ = v___y_469_;
goto v___jp_459_;
}
}
v___jp_470_:
{
if (v___y_471_ == 0)
{
v___y_469_ = v___y_471_;
goto v___jp_468_;
}
else
{
uint32_t v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_string_utf8_get_fast(v_s_387_, v_p_395_);
v___x_473_ = lean_uint32_dec_eq(v___x_472_, v___x_451_);
v___y_469_ = v___x_473_;
goto v___jp_468_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_shiftr(v_ucount_391_, v___x_475_);
lean_dec(v_ucount_391_);
v___x_477_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_476_, v_acc_390_);
v___x_478_ = lean_string_push(v___x_477_, v_ch_394_);
v_p_u2080_388_ = v_p_395_;
v_acc_390_ = v___x_478_;
v_ucount_391_ = v___x_400_;
goto _start;
}
v___jp_401_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_402_ = l_Lean_Name_str___override(v_res_389_, v_acc_390_);
v___x_403_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_shiftr(v_ucount_391_, v___x_404_);
lean_dec(v_ucount_391_);
v___x_406_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_405_, v___x_403_);
v___x_407_ = lean_string_push(v___x_406_, v_ch_394_);
v_p_u2080_388_ = v_p_395_;
v_res_389_ = v___x_402_;
v_acc_390_ = v___x_407_;
v_ucount_391_ = v___x_400_;
goto _start;
}
v___jp_409_:
{
uint32_t v___x_410_; uint8_t v___x_411_; 
v___x_410_ = 85;
v___x_411_ = lean_uint32_dec_eq(v_ch_394_, v___x_410_);
if (v___x_411_ == 0)
{
goto v___jp_401_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(8u);
v___x_413_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_412_, v_s_387_, v_p_395_, v___x_400_);
if (lean_obj_tag(v___x_413_) == 1)
{
lean_object* v_val_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_acc_419_; uint32_t v___x_420_; lean_object* v___x_421_; 
v_val_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v___x_413_, 1);
v_fst_415_ = lean_ctor_get(v_val_414_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v_val_414_, 1);
lean_inc(v_snd_416_);
lean_dec(v_val_414_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_shiftr(v_ucount_391_, v___x_417_);
lean_dec(v_ucount_391_);
v_acc_419_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_418_, v_acc_390_);
v___x_420_ = l_Char_ofNat(v_snd_416_);
lean_dec(v_snd_416_);
v___x_421_ = lean_string_push(v_acc_419_, v___x_420_);
v_p_u2080_388_ = v_fst_415_;
v_acc_390_ = v___x_421_;
v_ucount_391_ = v___x_400_;
goto _start;
}
else
{
lean_dec(v___x_413_);
goto v___jp_401_;
}
}
}
v___jp_423_:
{
uint32_t v___x_424_; uint8_t v___x_425_; 
v___x_424_ = 117;
v___x_425_ = lean_uint32_dec_eq(v_ch_394_, v___x_424_);
if (v___x_425_ == 0)
{
goto v___jp_409_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(4u);
v___x_427_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_426_, v_s_387_, v_p_395_, v___x_400_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_acc_433_; uint32_t v___x_434_; lean_object* v___x_435_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_427_, 1);
v_fst_429_ = lean_ctor_get(v_val_428_, 0);
lean_inc(v_fst_429_);
v_snd_430_ = lean_ctor_get(v_val_428_, 1);
lean_inc(v_snd_430_);
lean_dec(v_val_428_);
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_shiftr(v_ucount_391_, v___x_431_);
lean_dec(v_ucount_391_);
v_acc_433_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_432_, v_acc_390_);
v___x_434_ = l_Char_ofNat(v_snd_430_);
lean_dec(v_snd_430_);
v___x_435_ = lean_string_push(v_acc_433_, v___x_434_);
v_p_u2080_388_ = v_fst_429_;
v_acc_390_ = v___x_435_;
v_ucount_391_ = v___x_400_;
goto _start;
}
else
{
lean_dec(v___x_427_);
goto v___jp_409_;
}
}
}
v___jp_437_:
{
uint32_t v___x_438_; uint8_t v___x_439_; 
v___x_438_ = 120;
v___x_439_ = lean_uint32_dec_eq(v_ch_394_, v___x_438_);
if (v___x_439_ == 0)
{
goto v___jp_423_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_398_, v_s_387_, v_p_395_, v___x_400_);
if (lean_obj_tag(v___x_440_) == 1)
{
lean_object* v_val_441_; lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_acc_446_; uint32_t v___x_447_; lean_object* v___x_448_; 
v_val_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_val_441_);
lean_dec_ref_known(v___x_440_, 1);
v_fst_442_ = lean_ctor_get(v_val_441_, 0);
lean_inc(v_fst_442_);
v_snd_443_ = lean_ctor_get(v_val_441_, 1);
lean_inc(v_snd_443_);
lean_dec(v_val_441_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_shiftr(v_ucount_391_, v___x_444_);
lean_dec(v_ucount_391_);
v_acc_446_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_445_, v_acc_390_);
v___x_447_ = l_Char_ofNat(v_snd_443_);
lean_dec(v_snd_443_);
v___x_448_ = lean_string_push(v_acc_446_, v___x_447_);
v_p_u2080_388_ = v_fst_442_;
v_acc_390_ = v___x_448_;
v_ucount_391_ = v___x_400_;
goto _start;
}
else
{
lean_dec(v___x_440_);
goto v___jp_423_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_ucount_391_, v___x_480_);
lean_dec(v_ucount_391_);
v_p_u2080_388_ = v_p_395_;
v_ucount_391_ = v___x_481_;
goto _start;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v_p_u2080_388_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_shiftr(v_ucount_391_, v___x_483_);
lean_dec(v_ucount_391_);
v___x_485_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_484_, v_acc_390_);
v___x_486_ = l_Lean_Name_str___override(v_res_389_, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* v_s_487_, lean_object* v_p_488_, lean_object* v_res_489_){
_start:
{
lean_object* v___x_490_; uint8_t v_decide_491_; 
v___x_490_ = lean_string_utf8_byte_size(v_s_487_);
v_decide_491_ = lean_nat_dec_eq(v_p_488_, v___x_490_);
if (v_decide_491_ == 0)
{
uint32_t v_ch_492_; lean_object* v_p_493_; uint8_t v___y_495_; uint32_t v___x_514_; uint8_t v___x_515_; 
v_ch_492_ = lean_string_utf8_get_fast(v_s_487_, v_p_488_);
v_p_493_ = lean_string_utf8_next_fast(v_s_487_, v_p_488_);
v___x_514_ = 48;
v___x_515_ = lean_uint32_dec_le(v___x_514_, v_ch_492_);
if (v___x_515_ == 0)
{
goto v___jp_504_;
}
else
{
uint32_t v___x_516_; uint8_t v___x_517_; 
v___x_516_ = 57;
v___x_517_ = lean_uint32_dec_le(v_ch_492_, v___x_516_);
if (v___x_517_ == 0)
{
goto v___jp_504_;
}
else
{
uint8_t v___x_518_; uint8_t v___y_520_; uint8_t v___y_522_; uint8_t v_decide_525_; 
v___x_518_ = lean_uint32_dec_eq(v_ch_492_, v___x_514_);
v_decide_525_ = lean_nat_dec_eq(v_p_493_, v___x_490_);
if (v_decide_525_ == 0)
{
v___y_522_ = v___x_517_;
goto v___jp_521_;
}
else
{
v___y_522_ = v_decide_491_;
goto v___jp_521_;
}
v___jp_519_:
{
if (v___x_518_ == 0)
{
v___y_495_ = v___x_518_;
goto v___jp_494_;
}
else
{
v___y_495_ = v___y_520_;
goto v___jp_494_;
}
}
v___jp_521_:
{
if (v___y_522_ == 0)
{
v___y_520_ = v___y_522_;
goto v___jp_519_;
}
else
{
uint32_t v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_string_utf8_get_fast(v_s_487_, v_p_493_);
v___x_524_ = lean_uint32_dec_eq(v___x_523_, v___x_514_);
v___y_520_ = v___x_524_;
goto v___jp_519_;
}
}
}
}
v___jp_494_:
{
if (v___y_495_ == 0)
{
uint32_t v___x_496_; uint32_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_496_ = 48;
v___x_497_ = lean_uint32_sub(v_ch_492_, v___x_496_);
v___x_498_ = lean_uint32_to_nat(v___x_497_);
v___x_499_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_487_, v_p_493_, v_res_489_, v___x_498_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_string_utf8_next_fast(v_s_487_, v_p_493_);
v___x_501_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_487_, v___x_500_, v_res_489_, v___x_501_, v___x_502_);
return v___x_503_;
}
}
v___jp_504_:
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 95;
v___x_506_ = lean_uint32_dec_eq(v_ch_492_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_508_ = lean_string_push(v___x_507_, v_ch_492_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_487_, v_p_493_, v_res_489_, v___x_508_, v___x_509_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l_String_Internal_mangle___closed__0));
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_487_, v_p_493_, v_res_489_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
}
else
{
return v_res_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* v_s_526_, lean_object* v_p_527_, lean_object* v_res_528_, lean_object* v_n_529_){
_start:
{
lean_object* v___x_530_; uint8_t v_decide_531_; 
v___x_530_ = lean_string_utf8_byte_size(v_s_526_);
v_decide_531_ = lean_nat_dec_eq(v_p_527_, v___x_530_);
if (v_decide_531_ == 0)
{
uint32_t v_ch_532_; lean_object* v_p_533_; uint32_t v___x_539_; uint8_t v___x_540_; 
v_ch_532_ = lean_string_utf8_get_fast(v_s_526_, v_p_527_);
v_p_533_ = lean_string_utf8_next_fast(v_s_526_, v_p_527_);
lean_dec(v_p_527_);
v___x_539_ = 48;
v___x_540_ = lean_uint32_dec_le(v___x_539_, v_ch_532_);
if (v___x_540_ == 0)
{
goto v___jp_534_;
}
else
{
uint32_t v___x_541_; uint8_t v___x_542_; 
v___x_541_ = 57;
v___x_542_ = lean_uint32_dec_le(v_ch_532_, v___x_541_);
if (v___x_542_ == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; uint32_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_543_ = lean_unsigned_to_nat(10u);
v___x_544_ = lean_nat_mul(v_n_529_, v___x_543_);
lean_dec(v_n_529_);
v___x_545_ = lean_uint32_sub(v_ch_532_, v___x_539_);
v___x_546_ = lean_uint32_to_nat(v___x_545_);
v___x_547_ = lean_nat_add(v___x_544_, v___x_546_);
lean_dec(v___x_546_);
lean_dec(v___x_544_);
v_p_527_ = v_p_533_;
v_n_529_ = v___x_547_;
goto _start;
}
}
v___jp_534_:
{
lean_object* v_res_535_; uint8_t v_decide_536_; 
v_res_535_ = l_Lean_Name_num___override(v_res_528_, v_n_529_);
v_decide_536_ = lean_nat_dec_eq(v_p_533_, v___x_530_);
if (v_decide_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_string_utf8_next_fast(v_s_526_, v_p_533_);
v___x_538_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_526_, v___x_537_, v_res_535_);
return v___x_538_;
}
else
{
return v_res_535_;
}
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v_p_527_);
v___x_549_ = l_Lean_Name_num___override(v_res_528_, v_n_529_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* v_s_550_, lean_object* v_p_551_, lean_object* v_res_552_, lean_object* v_n_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_550_, v_p_551_, v_res_552_, v_n_553_);
lean_dec_ref(v_s_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* v_s_555_, lean_object* v_p_556_, lean_object* v_res_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_555_, v_p_556_, v_res_557_);
lean_dec(v_p_556_);
lean_dec_ref(v_s_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* v_s_559_, lean_object* v_p_u2080_560_, lean_object* v_res_561_, lean_object* v_acc_562_, lean_object* v_ucount_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_559_, v_p_u2080_560_, v_res_561_, v_acc_562_, v_ucount_563_);
lean_dec_ref(v_s_559_);
return v_res_564_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_565_; lean_object* v___x_566_; 
v___x_565_ = 120;
v___x_566_ = lean_box_uint32(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t v_ch_567_, lean_object* v_x_568_, lean_object* v_h__1_569_, lean_object* v_h__2_570_){
_start:
{
uint32_t v___x_571_; uint8_t v___x_572_; 
v___x_571_ = 120;
v___x_572_ = lean_uint32_dec_eq(v_ch_567_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v_h__1_569_);
v___x_573_ = lean_box_uint32(v_ch_567_);
v___x_574_ = lean_apply_4(v_h__2_570_, v___x_573_, v_x_568_, lean_box(0), lean_box(0));
return v___x_574_;
}
else
{
if (lean_obj_tag(v_x_568_) == 1)
{
lean_object* v_val_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_578_; 
lean_dec(v_h__2_570_);
v_val_575_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_val_575_);
lean_dec_ref_known(v_x_568_, 1);
v_fst_576_ = lean_ctor_get(v_val_575_, 0);
lean_inc(v_fst_576_);
v_snd_577_ = lean_ctor_get(v_val_575_, 1);
lean_inc(v_snd_577_);
lean_dec(v_val_575_);
v___x_578_ = lean_apply_3(v_h__1_569_, v_fst_576_, v_snd_577_, lean_box(0));
return v___x_578_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_h__1_569_);
v___x_579_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_580_ = lean_apply_4(v_h__2_570_, v___x_579_, v_x_568_, lean_box(0), lean_box(0));
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* v_ch_581_, lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_){
_start:
{
uint32_t v_ch_87__boxed_585_; lean_object* v_res_586_; 
v_ch_87__boxed_585_ = lean_unbox_uint32(v_ch_581_);
lean_dec(v_ch_581_);
v_res_586_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_87__boxed_585_, v_x_582_, v_h__1_583_, v_h__2_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* v_s_587_, lean_object* v_motive_588_, uint32_t v_ch_589_, lean_object* v_x_590_, lean_object* v_h__1_591_, lean_object* v_h__2_592_){
_start:
{
uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 120;
v___x_594_ = lean_uint32_dec_eq(v_ch_589_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_h__1_591_);
v___x_595_ = lean_box_uint32(v_ch_589_);
v___x_596_ = lean_apply_4(v_h__2_592_, v___x_595_, v_x_590_, lean_box(0), lean_box(0));
return v___x_596_;
}
else
{
if (lean_obj_tag(v_x_590_) == 1)
{
lean_object* v_val_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_600_; 
lean_dec(v_h__2_592_);
v_val_597_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_x_590_, 1);
v_fst_598_ = lean_ctor_get(v_val_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v_val_597_, 1);
lean_inc(v_snd_599_);
lean_dec(v_val_597_);
v___x_600_ = lean_apply_3(v_h__1_591_, v_fst_598_, v_snd_599_, lean_box(0));
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_h__1_591_);
v___x_601_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_602_ = lean_apply_4(v_h__2_592_, v___x_601_, v_x_590_, lean_box(0), lean_box(0));
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* v_s_603_, lean_object* v_motive_604_, lean_object* v_ch_605_, lean_object* v_x_606_, lean_object* v_h__1_607_, lean_object* v_h__2_608_){
_start:
{
uint32_t v_ch_117__boxed_609_; lean_object* v_res_610_; 
v_ch_117__boxed_609_ = lean_unbox_uint32(v_ch_605_);
lean_dec(v_ch_605_);
v_res_610_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_603_, v_motive_604_, v_ch_117__boxed_609_, v_x_606_, v_h__1_607_, v_h__2_608_);
lean_dec_ref(v_s_603_);
return v_res_610_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_611_; lean_object* v___x_612_; 
v___x_611_ = 117;
v___x_612_ = lean_box_uint32(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t v_ch_613_, lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 117;
v___x_618_ = lean_uint32_dec_eq(v_ch_613_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_h__1_615_);
v___x_619_ = lean_box_uint32(v_ch_613_);
v___x_620_ = lean_apply_4(v_h__2_616_, v___x_619_, v_x_614_, lean_box(0), lean_box(0));
return v___x_620_;
}
else
{
if (lean_obj_tag(v_x_614_) == 1)
{
lean_object* v_val_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; lean_object* v___x_624_; 
lean_dec(v_h__2_616_);
v_val_621_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v_x_614_, 1);
v_fst_622_ = lean_ctor_get(v_val_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v_val_621_, 1);
lean_inc(v_snd_623_);
lean_dec(v_val_621_);
v___x_624_ = lean_apply_3(v_h__1_615_, v_fst_622_, v_snd_623_, lean_box(0));
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_h__1_615_);
v___x_625_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_626_ = lean_apply_4(v_h__2_616_, v___x_625_, v_x_614_, lean_box(0), lean_box(0));
return v___x_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* v_ch_627_, lean_object* v_x_628_, lean_object* v_h__1_629_, lean_object* v_h__2_630_){
_start:
{
uint32_t v_ch_87__boxed_631_; lean_object* v_res_632_; 
v_ch_87__boxed_631_ = lean_unbox_uint32(v_ch_627_);
lean_dec(v_ch_627_);
v_res_632_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_87__boxed_631_, v_x_628_, v_h__1_629_, v_h__2_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* v_s_633_, lean_object* v_motive_634_, uint32_t v_ch_635_, lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_){
_start:
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 117;
v___x_640_ = lean_uint32_dec_eq(v_ch_635_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_h__1_637_);
v___x_641_ = lean_box_uint32(v_ch_635_);
v___x_642_ = lean_apply_4(v_h__2_638_, v___x_641_, v_x_636_, lean_box(0), lean_box(0));
return v___x_642_;
}
else
{
if (lean_obj_tag(v_x_636_) == 1)
{
lean_object* v_val_643_; lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_646_; 
lean_dec(v_h__2_638_);
v_val_643_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_val_643_);
lean_dec_ref_known(v_x_636_, 1);
v_fst_644_ = lean_ctor_get(v_val_643_, 0);
lean_inc(v_fst_644_);
v_snd_645_ = lean_ctor_get(v_val_643_, 1);
lean_inc(v_snd_645_);
lean_dec(v_val_643_);
v___x_646_ = lean_apply_3(v_h__1_637_, v_fst_644_, v_snd_645_, lean_box(0));
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_637_);
v___x_647_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_648_ = lean_apply_4(v_h__2_638_, v___x_647_, v_x_636_, lean_box(0), lean_box(0));
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* v_s_649_, lean_object* v_motive_650_, lean_object* v_ch_651_, lean_object* v_x_652_, lean_object* v_h__1_653_, lean_object* v_h__2_654_){
_start:
{
uint32_t v_ch_117__boxed_655_; lean_object* v_res_656_; 
v_ch_117__boxed_655_ = lean_unbox_uint32(v_ch_651_);
lean_dec(v_ch_651_);
v_res_656_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_649_, v_motive_650_, v_ch_117__boxed_655_, v_x_652_, v_h__1_653_, v_h__2_654_);
lean_dec_ref(v_s_649_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_657_; lean_object* v___x_658_; 
v___x_657_ = 85;
v___x_658_ = lean_box_uint32(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t v_ch_659_, lean_object* v_x_660_, lean_object* v_h__1_661_, lean_object* v_h__2_662_){
_start:
{
uint32_t v___x_663_; uint8_t v___x_664_; 
v___x_663_ = 85;
v___x_664_ = lean_uint32_dec_eq(v_ch_659_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_h__1_661_);
v___x_665_ = lean_box_uint32(v_ch_659_);
v___x_666_ = lean_apply_4(v_h__2_662_, v___x_665_, v_x_660_, lean_box(0), lean_box(0));
return v___x_666_;
}
else
{
if (lean_obj_tag(v_x_660_) == 1)
{
lean_object* v_val_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_670_; 
lean_dec(v_h__2_662_);
v_val_667_ = lean_ctor_get(v_x_660_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_x_660_, 1);
v_fst_668_ = lean_ctor_get(v_val_667_, 0);
lean_inc(v_fst_668_);
v_snd_669_ = lean_ctor_get(v_val_667_, 1);
lean_inc(v_snd_669_);
lean_dec(v_val_667_);
v___x_670_ = lean_apply_3(v_h__1_661_, v_fst_668_, v_snd_669_, lean_box(0));
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_h__1_661_);
v___x_671_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_672_ = lean_apply_4(v_h__2_662_, v___x_671_, v_x_660_, lean_box(0), lean_box(0));
return v___x_672_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* v_ch_673_, lean_object* v_x_674_, lean_object* v_h__1_675_, lean_object* v_h__2_676_){
_start:
{
uint32_t v_ch_87__boxed_677_; lean_object* v_res_678_; 
v_ch_87__boxed_677_ = lean_unbox_uint32(v_ch_673_);
lean_dec(v_ch_673_);
v_res_678_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_87__boxed_677_, v_x_674_, v_h__1_675_, v_h__2_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* v_s_679_, lean_object* v_motive_680_, uint32_t v_ch_681_, lean_object* v_x_682_, lean_object* v_h__1_683_, lean_object* v_h__2_684_){
_start:
{
uint32_t v___x_685_; uint8_t v___x_686_; 
v___x_685_ = 85;
v___x_686_ = lean_uint32_dec_eq(v_ch_681_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_h__1_683_);
v___x_687_ = lean_box_uint32(v_ch_681_);
v___x_688_ = lean_apply_4(v_h__2_684_, v___x_687_, v_x_682_, lean_box(0), lean_box(0));
return v___x_688_;
}
else
{
if (lean_obj_tag(v_x_682_) == 1)
{
lean_object* v_val_689_; lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_692_; 
lean_dec(v_h__2_684_);
v_val_689_ = lean_ctor_get(v_x_682_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v_x_682_, 1);
v_fst_690_ = lean_ctor_get(v_val_689_, 0);
lean_inc(v_fst_690_);
v_snd_691_ = lean_ctor_get(v_val_689_, 1);
lean_inc(v_snd_691_);
lean_dec(v_val_689_);
v___x_692_ = lean_apply_3(v_h__1_683_, v_fst_690_, v_snd_691_, lean_box(0));
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v_h__1_683_);
v___x_693_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_694_ = lean_apply_4(v_h__2_684_, v___x_693_, v_x_682_, lean_box(0), lean_box(0));
return v___x_694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* v_s_695_, lean_object* v_motive_696_, lean_object* v_ch_697_, lean_object* v_x_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
_start:
{
uint32_t v_ch_117__boxed_701_; lean_object* v_res_702_; 
v_ch_117__boxed_701_ = lean_unbox_uint32(v_ch_697_);
lean_dec(v_ch_697_);
v_res_702_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_695_, v_motive_696_, v_ch_117__boxed_701_, v_x_698_, v_h__1_699_, v_h__2_700_);
lean_dec_ref(v_s_695_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* v_s_703_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_box(0);
v___x_706_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_703_, v___x_704_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* v_s_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Name_demangle(v_s_707_);
lean_dec_ref(v_s_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* v_s_709_){
_start:
{
lean_object* v_n_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_n_710_ = l_Lean_Name_demangle(v_s_709_);
lean_inc(v_n_710_);
v___x_711_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_710_);
v___x_712_ = lean_string_dec_eq(v___x_711_, v_s_709_);
lean_dec_ref(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec(v_n_710_);
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_n_710_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* v_s_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Name_demangle_x3f(v_s_715_);
lean_dec_ref(v_s_715_);
return v_res_716_;
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
