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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
static const lean_string_object l_String_mangle___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_mangle___closed__0 = (const lean_object*)&l_String_mangle___closed__0_value;
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
LEAN_EXPORT lean_object* l_String_mangle___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_mkMangledBoxedName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkMangledBoxedName___closed__1;
static const lean_string_object l_Lean_mkMangledBoxedName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_00__boxed"};
static const lean_object* l_Lean_mkMangledBoxedName___closed__2 = (const lean_object*)&l_Lean_mkMangledBoxedName___closed__2_value;
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
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_string_utf8_byte_size(v_s_45_);
v___x_49_ = lean_nat_dec_eq(v_pos_46_, v___x_48_);
if (v___x_49_ == 0)
{
uint32_t v_c_50_; lean_object* v_pos_51_; uint8_t v___y_56_; uint8_t v___y_83_; uint32_t v___x_93_; uint8_t v___x_94_; 
v_c_50_ = lean_string_utf8_get_fast(v_s_45_, v_pos_46_);
v_pos_51_ = lean_string_utf8_next_fast(v_s_45_, v_pos_46_);
lean_dec(v_pos_46_);
v___x_93_ = 65;
v___x_94_ = lean_uint32_dec_le(v___x_93_, v_c_50_);
if (v___x_94_ == 0)
{
goto v___jp_88_;
}
else
{
uint32_t v___x_95_; uint8_t v___x_96_; 
v___x_95_ = 90;
v___x_96_ = lean_uint32_dec_le(v_c_50_, v___x_95_);
if (v___x_96_ == 0)
{
goto v___jp_88_;
}
else
{
goto v___jp_52_;
}
}
v___jp_52_:
{
lean_object* v___x_53_; 
v___x_53_ = lean_string_push(v_r_47_, v_c_50_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_53_;
goto _start;
}
v___jp_55_:
{
if (v___y_56_ == 0)
{
uint32_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = 95;
v___x_58_ = lean_uint32_dec_eq(v_c_50_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = lean_uint32_to_nat(v_c_50_);
v___x_60_ = lean_unsigned_to_nat(256u);
v___x_61_ = lean_nat_dec_lt(v___x_59_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(65536u);
v___x_63_ = lean_nat_dec_lt(v___x_59_, v___x_62_);
lean_dec(v___x_59_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_unsigned_to_nat(8u);
v___x_65_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0));
v___x_66_ = lean_string_append(v_r_47_, v___x_65_);
v___x_67_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_64_, v_c_50_, v___x_66_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_67_;
goto _start;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_unsigned_to_nat(4u);
v___x_70_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1));
v___x_71_ = lean_string_append(v_r_47_, v___x_70_);
v___x_72_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_69_, v_c_50_, v___x_71_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_72_;
goto _start;
}
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v___x_59_);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2));
v___x_76_ = lean_string_append(v_r_47_, v___x_75_);
v___x_77_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(v___x_74_, v_c_50_, v___x_76_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_77_;
goto _start;
}
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_80_ = lean_string_append(v_r_47_, v___x_79_);
v_pos_46_ = v_pos_51_;
v_r_47_ = v___x_80_;
goto _start;
}
}
else
{
goto v___jp_52_;
}
}
v___jp_82_:
{
if (v___y_83_ == 0)
{
uint32_t v___x_84_; uint8_t v___x_85_; 
v___x_84_ = 48;
v___x_85_ = lean_uint32_dec_le(v___x_84_, v_c_50_);
if (v___x_85_ == 0)
{
v___y_56_ = v___x_85_;
goto v___jp_55_;
}
else
{
uint32_t v___x_86_; uint8_t v___x_87_; 
v___x_86_ = 57;
v___x_87_ = lean_uint32_dec_le(v_c_50_, v___x_86_);
v___y_56_ = v___x_87_;
goto v___jp_55_;
}
}
else
{
goto v___jp_52_;
}
}
v___jp_88_:
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 97;
v___x_90_ = lean_uint32_dec_le(v___x_89_, v_c_50_);
if (v___x_90_ == 0)
{
v___y_83_ = v___x_90_;
goto v___jp_82_;
}
else
{
uint32_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = 122;
v___x_92_ = lean_uint32_dec_le(v_c_50_, v___x_91_);
v___y_83_ = v___x_92_;
goto v___jp_82_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(lean_object* v_s_97_, lean_object* v_pos_98_, lean_object* v_r_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_97_, v_pos_98_, v_r_99_);
lean_dec_ref(v_s_97_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_String_mangle(lean_object* v_s_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_105_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_102_, v___x_103_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_String_mangle___boxed(lean_object* v_s_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_String_mangle(v_s_106_);
lean_dec_ref(v_s_106_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(lean_object* v_x_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_zero_111_; uint8_t v_isZero_112_; 
v_zero_111_ = lean_unsigned_to_nat(0u);
v_isZero_112_ = lean_nat_dec_eq(v_x_108_, v_zero_111_);
if (v_isZero_112_ == 1)
{
lean_dec(v_x_110_);
lean_dec(v_x_108_);
return v_isZero_112_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_string_utf8_byte_size(v_x_109_);
v___x_114_ = lean_nat_dec_eq(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v_one_115_; lean_object* v_n_116_; uint8_t v___y_121_; uint32_t v_ch_122_; uint8_t v___y_124_; uint32_t v___x_129_; uint8_t v___x_130_; 
v_one_115_ = lean_unsigned_to_nat(1u);
v_n_116_ = lean_nat_sub(v_x_108_, v_one_115_);
lean_dec(v_x_108_);
v_ch_122_ = lean_string_utf8_get_fast(v_x_109_, v_x_110_);
v___x_129_ = 48;
v___x_130_ = lean_uint32_dec_le(v___x_129_, v_ch_122_);
if (v___x_130_ == 0)
{
v___y_124_ = v___x_130_;
goto v___jp_123_;
}
else
{
uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_131_ = 57;
v___x_132_ = lean_uint32_dec_le(v_ch_122_, v___x_131_);
v___y_124_ = v___x_132_;
goto v___jp_123_;
}
v___jp_117_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_string_utf8_next_fast(v_x_109_, v_x_110_);
lean_dec(v_x_110_);
v_x_108_ = v_n_116_;
v_x_110_ = v___x_118_;
goto _start;
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
lean_dec(v_n_116_);
lean_dec(v_x_110_);
return v___y_121_;
}
else
{
goto v___jp_117_;
}
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 97;
v___x_126_ = lean_uint32_dec_le(v___x_125_, v_ch_122_);
if (v___x_126_ == 0)
{
v___y_121_ = v___x_126_;
goto v___jp_120_;
}
else
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 102;
v___x_128_ = lean_uint32_dec_le(v_ch_122_, v___x_127_);
v___y_121_ = v___x_128_;
goto v___jp_120_;
}
}
else
{
goto v___jp_117_;
}
}
}
else
{
lean_dec(v_x_110_);
lean_dec(v_x_108_);
return v_isZero_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_133_, v_x_134_, v_x_135_);
lean_dec_ref(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(uint32_t v_c_138_){
_start:
{
uint8_t v___y_140_; uint8_t v___y_147_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 48;
v___x_157_ = lean_uint32_dec_le(v___x_156_, v_c_138_);
if (v___x_157_ == 0)
{
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 57;
v___x_159_ = lean_uint32_dec_le(v_c_138_, v___x_158_);
v___y_147_ = v___x_159_;
goto v___jp_146_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_box(0);
return v___x_141_;
}
else
{
uint32_t v___x_142_; uint32_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = 87;
v___x_143_ = lean_uint32_sub(v_c_138_, v___x_142_);
v___x_144_ = lean_uint32_to_nat(v___x_143_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
v___jp_146_:
{
if (v___y_147_ == 0)
{
uint32_t v___x_148_; uint8_t v___x_149_; 
v___x_148_ = 97;
v___x_149_ = lean_uint32_dec_le(v___x_148_, v_c_138_);
if (v___x_149_ == 0)
{
v___y_140_ = v___x_149_;
goto v___jp_139_;
}
else
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 102;
v___x_151_ = lean_uint32_dec_le(v_c_138_, v___x_150_);
v___y_140_ = v___x_151_;
goto v___jp_139_;
}
}
else
{
uint32_t v___x_152_; uint32_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = 48;
v___x_153_ = lean_uint32_sub(v_c_138_, v___x_152_);
v___x_154_ = lean_uint32_to_nat(v___x_153_);
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(lean_object* v_c_160_){
_start:
{
uint32_t v_c_boxed_161_; lean_object* v_res_162_; 
v_c_boxed_161_ = lean_unbox_uint32(v_c_160_);
lean_dec(v_c_160_);
v_res_162_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(lean_object* v_k_163_, lean_object* v_s_164_, lean_object* v_p_165_, lean_object* v_acc_166_){
_start:
{
lean_object* v_zero_167_; uint8_t v_isZero_168_; 
v_zero_167_ = lean_unsigned_to_nat(0u);
v_isZero_168_ = lean_nat_dec_eq(v_k_163_, v_zero_167_);
if (v_isZero_168_ == 1)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_k_163_);
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v_p_165_);
lean_ctor_set(v___x_169_, 1, v_acc_166_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_string_utf8_byte_size(v_s_164_);
v___x_172_ = lean_nat_dec_eq(v_p_165_, v___x_171_);
if (v___x_172_ == 0)
{
uint32_t v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_string_utf8_get_fast(v_s_164_, v_p_165_);
v___x_174_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; 
lean_dec(v_acc_166_);
lean_dec(v_p_165_);
lean_dec(v_k_163_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_val_176_; lean_object* v_one_177_; lean_object* v_n_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_val_176_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_176_);
lean_dec_ref(v___x_174_);
v_one_177_ = lean_unsigned_to_nat(1u);
v_n_178_ = lean_nat_sub(v_k_163_, v_one_177_);
lean_dec(v_k_163_);
v___x_179_ = lean_string_utf8_next_fast(v_s_164_, v_p_165_);
lean_dec(v_p_165_);
v___x_180_ = lean_unsigned_to_nat(4u);
v___x_181_ = lean_nat_shiftl(v_acc_166_, v___x_180_);
lean_dec(v_acc_166_);
v___x_182_ = lean_nat_lor(v___x_181_, v_val_176_);
lean_dec(v_val_176_);
lean_dec(v___x_181_);
v_k_163_ = v_n_178_;
v_p_165_ = v___x_179_;
v_acc_166_ = v___x_182_;
goto _start;
}
}
else
{
lean_object* v___x_184_; 
lean_dec(v_acc_166_);
lean_dec(v_p_165_);
lean_dec(v_k_163_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(lean_object* v_k_185_, lean_object* v_s_186_, lean_object* v_p_187_, lean_object* v_acc_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v_k_185_, v_s_186_, v_p_187_, v_acc_188_);
lean_dec_ref(v_s_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(lean_object* v_n_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
lean_object* v_zero_193_; uint8_t v_isZero_194_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_n_190_, v_zero_193_);
if (v_isZero_194_ == 1)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_h__2_192_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_1(v_h__1_191_, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_one_197_; lean_object* v_n_198_; lean_object* v___x_199_; 
lean_dec(v_h__1_191_);
v_one_197_ = lean_unsigned_to_nat(1u);
v_n_198_ = lean_nat_sub(v_n_190_, v_one_197_);
v___x_199_ = lean_apply_1(v_h__2_192_, v_n_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(lean_object* v_n_200_, lean_object* v_h__1_201_, lean_object* v_h__2_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(v_n_200_, v_h__1_201_, v_h__2_202_);
lean_dec(v_n_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(lean_object* v_motive_204_, lean_object* v_n_205_, lean_object* v_h__1_206_, lean_object* v_h__2_207_){
_start:
{
lean_object* v_zero_208_; uint8_t v_isZero_209_; 
v_zero_208_ = lean_unsigned_to_nat(0u);
v_isZero_209_ = lean_nat_dec_eq(v_n_205_, v_zero_208_);
if (v_isZero_209_ == 1)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_h__2_207_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_1(v_h__1_206_, v___x_210_);
return v___x_211_;
}
else
{
lean_object* v_one_212_; lean_object* v_n_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_206_);
v_one_212_ = lean_unsigned_to_nat(1u);
v_n_213_ = lean_nat_sub(v_n_205_, v_one_212_);
v___x_214_ = lean_apply_1(v_h__2_207_, v_n_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* v_motive_215_, lean_object* v_n_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(v_motive_215_, v_n_216_, v_h__1_217_, v_h__2_218_);
lean_dec(v_n_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
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
lean_dec_ref(v_x_220_);
v___x_226_ = lean_apply_1(v_h__1_221_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* v_motive_227_, lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__1_229_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__2_230_, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
lean_dec(v_h__2_230_);
v_val_233_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v_x_228_);
v___x_234_ = lean_apply_1(v_h__1_229_, v_val_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* v_s_235_, lean_object* v_p_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_string_utf8_byte_size(v_s_235_);
v___x_238_ = lean_nat_dec_eq(v_p_236_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v_b_239_; uint32_t v___x_240_; uint8_t v___x_241_; 
v_b_239_ = lean_string_utf8_get_fast(v_s_235_, v_p_236_);
v___x_240_ = 95;
v___x_241_ = lean_uint32_dec_eq(v_b_239_, v___x_240_);
if (v___x_241_ == 0)
{
uint32_t v___x_242_; uint8_t v___x_243_; 
v___x_242_ = 120;
v___x_243_ = lean_uint32_dec_eq(v_b_239_, v___x_242_);
if (v___x_243_ == 0)
{
uint32_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 117;
v___x_245_ = lean_uint32_dec_eq(v_b_239_, v___x_244_);
if (v___x_245_ == 0)
{
uint32_t v___x_246_; uint8_t v___x_247_; 
v___x_246_ = 85;
v___x_247_ = lean_uint32_dec_eq(v_b_239_, v___x_246_);
if (v___x_247_ == 0)
{
uint32_t v___x_248_; uint8_t v___x_249_; 
lean_dec(v_p_236_);
v___x_248_ = 48;
v___x_249_ = lean_uint32_dec_le(v___x_248_, v_b_239_);
if (v___x_249_ == 0)
{
return v___x_249_;
}
else
{
uint32_t v___x_250_; uint8_t v___x_251_; 
v___x_250_ = 57;
v___x_251_ = lean_uint32_dec_le(v_b_239_, v___x_250_);
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_252_ = lean_unsigned_to_nat(8u);
v___x_253_ = lean_string_utf8_next_fast(v_s_235_, v_p_236_);
lean_dec(v_p_236_);
v___x_254_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_252_, v_s_235_, v___x_253_);
return v___x_254_;
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(4u);
v___x_256_ = lean_string_utf8_next_fast(v_s_235_, v_p_236_);
lean_dec(v_p_236_);
v___x_257_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_255_, v_s_235_, v___x_256_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(2u);
v___x_259_ = lean_string_utf8_next_fast(v_s_235_, v_p_236_);
lean_dec(v_p_236_);
v___x_260_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_258_, v_s_235_, v___x_259_);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; 
v___x_261_ = lean_string_utf8_next_fast(v_s_235_, v_p_236_);
lean_dec(v_p_236_);
v_p_236_ = v___x_261_;
goto _start;
}
}
else
{
lean_dec(v_p_236_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* v_s_263_, lean_object* v_p_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_263_, v_p_264_);
lean_dec_ref(v_s_263_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* v_prev_267_, lean_object* v_next_268_){
_start:
{
if (lean_obj_tag(v_prev_267_) == 1)
{
lean_object* v_str_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_str_272_ = lean_ctor_get(v_prev_267_, 1);
v___x_273_ = lean_string_utf8_byte_size(v_str_272_);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint32_t v___x_280_; uint32_t v___x_281_; uint8_t v___x_282_; 
lean_inc_ref(v_str_272_);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_str_272_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_sub(v___x_273_, v___x_277_);
v___x_279_ = l_String_Slice_posLE(v___x_276_, v___x_278_);
lean_dec_ref(v___x_276_);
v___x_280_ = lean_string_utf8_get_fast(v_str_272_, v___x_279_);
lean_dec(v___x_279_);
v___x_281_ = 95;
v___x_282_ = lean_uint32_dec_eq(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
goto v___jp_269_;
}
else
{
return v___x_282_;
}
}
else
{
goto v___jp_269_;
}
}
else
{
goto v___jp_269_;
}
v___jp_269_:
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_next_268_, v___x_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* v_prev_283_, lean_object* v_next_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_283_, v_next_284_);
lean_dec_ref(v_next_284_);
lean_dec(v_prev_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* v_x_290_){
_start:
{
switch(lean_obj_tag(v_x_290_))
{
case 0:
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_String_mangle___closed__0));
return v___x_291_;
}
case 1:
{
lean_object* v_pre_292_; lean_object* v_str_293_; lean_object* v_m_294_; 
v_pre_292_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_pre_292_);
v_str_293_ = lean_ctor_get(v_x_290_, 1);
lean_inc_ref(v_str_293_);
lean_dec_ref(v_x_290_);
v_m_294_ = l_String_mangle(v_str_293_);
lean_dec_ref(v_str_293_);
if (lean_obj_tag(v_pre_292_) == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_m_294_, v___x_295_);
if (v___x_296_ == 0)
{
return v_m_294_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0));
v___x_298_ = lean_string_append(v___x_297_, v_m_294_);
lean_dec_ref(v_m_294_);
return v___x_298_;
}
}
else
{
lean_object* v_m1_299_; lean_object* v___y_301_; uint8_t v___x_304_; 
lean_inc(v_pre_292_);
v_m1_299_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_292_);
v___x_304_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_pre_292_, v_m_294_);
lean_dec(v_pre_292_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___y_301_ = v___x_305_;
goto v___jp_300_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2));
v___y_301_ = v___x_306_;
goto v___jp_300_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_string_append(v_m1_299_, v___y_301_);
lean_dec_ref(v___y_301_);
v___x_303_ = lean_string_append(v___x_302_, v_m_294_);
lean_dec_ref(v_m_294_);
return v___x_303_;
}
}
}
default: 
{
lean_object* v_pre_307_; 
v_pre_307_ = lean_ctor_get(v_x_290_, 0);
if (lean_obj_tag(v_pre_307_) == 0)
{
lean_object* v_i_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_i_308_ = lean_ctor_get(v_x_290_, 1);
lean_inc(v_i_308_);
lean_dec_ref(v_x_290_);
v___x_309_ = l_Nat_reprFast(v_i_308_);
v___x_310_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_i_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc(v_pre_307_);
v_i_312_ = lean_ctor_get(v_x_290_, 1);
lean_inc(v_i_312_);
lean_dec_ref(v_x_290_);
v___x_313_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_307_);
v___x_314_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = l_Nat_reprFast(v_i_312_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_string_append(v___x_317_, v___x_314_);
return v___x_318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* v_n_319_, lean_object* v_pre_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_319_);
v___x_322_ = lean_string_append(v_pre_320_, v___x_321_);
lean_dec_ref(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_mkMangledBoxedName___closed__1(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_325_ = lean_string_utf8_byte_size(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object* v_s_327_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_332_ = lean_string_utf8_byte_size(v_s_327_);
v___x_333_ = lean_obj_once(&l_Lean_mkMangledBoxedName___closed__1, &l_Lean_mkMangledBoxedName___closed__1_once, _init_l_Lean_mkMangledBoxedName___closed__1);
v___x_334_ = lean_nat_dec_le(v___x_333_, v___x_332_);
if (v___x_334_ == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_nat_sub(v___x_332_, v___x_333_);
v___x_337_ = lean_string_memcmp(v_s_327_, v___x_331_, v___x_336_, v___x_335_, v___x_333_);
lean_dec(v___x_336_);
if (v___x_337_ == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__2));
v___x_339_ = lean_string_append(v_s_327_, v___x_338_);
return v___x_339_;
}
}
v___jp_328_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__0));
v___x_330_ = lean_string_append(v_s_327_, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem(lean_object* v_moduleName_340_, lean_object* v_pkg_x3f_341_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_341_) == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_343_ = l_Lean_Name_mangle(v_moduleName_340_, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_val_344_ = lean_ctor_get(v_pkg_x3f_341_, 0);
v___x_345_ = l_String_mangle(v_val_344_);
v___x_346_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
v___x_348_ = l_Lean_Name_mangle(v_moduleName_340_, v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationStem___boxed(lean_object* v_moduleName_349_, lean_object* v_pkg_x3f_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_mkModuleInitializationStem(v_moduleName_349_, v_pkg_x3f_350_);
lean_dec(v_pkg_x3f_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix(uint8_t v_phases_354_){
_start:
{
switch(v_phases_354_)
{
case 0:
{
lean_object* v___x_355_; 
v___x_355_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__0));
return v___x_355_;
}
case 1:
{
lean_object* v___x_356_; 
v___x_356_ = ((lean_object*)(l_Lean_mkModuleInitializationPrefix___closed__1));
return v___x_356_;
}
default: 
{
lean_object* v___x_357_; 
v___x_357_ = ((lean_object*)(l_String_mangle___closed__0));
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationPrefix___boxed(lean_object* v_phases_358_){
_start:
{
uint8_t v_phases_boxed_359_; lean_object* v_res_360_; 
v_phases_boxed_359_ = lean_unbox(v_phases_358_);
v_res_360_ = l_Lean_mkModuleInitializationPrefix(v_phases_boxed_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName(lean_object* v_moduleName_362_, lean_object* v_pkg_x3f_363_, uint8_t v_phases_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = l_Lean_mkModuleInitializationPrefix(v_phases_364_);
v___x_366_ = ((lean_object*)(l_Lean_mkModuleInitializationFunctionName___closed__0));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
v___x_368_ = l_Lean_mkModuleInitializationStem(v_moduleName_362_, v_pkg_x3f_363_);
v___x_369_ = lean_string_append(v___x_367_, v___x_368_);
lean_dec_ref(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkModuleInitializationFunctionName___boxed(lean_object* v_moduleName_370_, lean_object* v_pkg_x3f_371_, lean_object* v_phases_372_){
_start:
{
uint8_t v_phases_boxed_373_; lean_object* v_res_374_; 
v_phases_boxed_373_ = lean_unbox(v_phases_372_);
v_res_374_ = l_Lean_mkModuleInitializationFunctionName(v_moduleName_370_, v_pkg_x3f_371_, v_phases_boxed_373_);
lean_dec(v_pkg_x3f_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix(lean_object* v_pkg_x3f_377_){
_start:
{
if (lean_obj_tag(v_pkg_x3f_377_) == 0)
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__0));
return v___x_378_;
}
else
{
lean_object* v_val_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_val_379_ = lean_ctor_get(v_pkg_x3f_377_, 0);
v___x_380_ = ((lean_object*)(l_Lean_mkPackageSymbolPrefix___closed__1));
v___x_381_ = l_String_mangle(v_val_379_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_384_ = lean_string_append(v___x_382_, v___x_383_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPackageSymbolPrefix___boxed(lean_object* v_pkg_x3f_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_mkPackageSymbolPrefix(v_pkg_x3f_385_);
lean_dec(v_pkg_x3f_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_zero_389_; uint8_t v_isZero_390_; 
v_zero_389_ = lean_unsigned_to_nat(0u);
v_isZero_390_ = lean_nat_dec_eq(v_x_387_, v_zero_389_);
if (v_isZero_390_ == 1)
{
lean_dec(v_x_387_);
return v_x_388_;
}
else
{
uint32_t v___x_391_; lean_object* v_one_392_; lean_object* v_n_393_; lean_object* v___x_394_; 
v___x_391_ = 95;
v_one_392_ = lean_unsigned_to_nat(1u);
v_n_393_ = lean_nat_sub(v_x_387_, v_one_392_);
lean_dec(v_x_387_);
v___x_394_ = lean_string_push(v_x_388_, v___x_391_);
v_x_387_ = v_n_393_;
v_x_388_ = v___x_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(lean_object* v_s_396_, lean_object* v_p_u2080_397_, lean_object* v_res_398_, lean_object* v_acc_399_, lean_object* v_ucount_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_string_utf8_byte_size(v_s_396_);
v___x_402_ = lean_nat_dec_eq(v_p_u2080_397_, v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v_ch_403_; lean_object* v_p_404_; lean_object* v___y_406_; uint32_t v___x_411_; uint8_t v___x_412_; 
v_ch_403_ = lean_string_utf8_get_fast(v_s_396_, v_p_u2080_397_);
v_p_404_ = lean_string_utf8_next_fast(v_s_396_, v_p_u2080_397_);
lean_dec(v_p_u2080_397_);
v___x_411_ = 95;
v___x_412_ = lean_uint32_dec_eq(v_ch_403_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___y_453_; uint8_t v___y_454_; uint8_t v___y_462_; uint8_t v___x_482_; 
v___x_413_ = lean_unsigned_to_nat(2u);
v___x_414_ = lean_nat_mod(v_ucount_400_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_nat_dec_eq(v___x_414_, v___x_415_);
lean_dec(v___x_414_);
if (v___x_482_ == 0)
{
uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_483_ = 48;
v___x_484_ = lean_uint32_dec_le(v___x_483_, v_ch_403_);
if (v___x_484_ == 0)
{
v___y_462_ = v___x_484_;
goto v___jp_461_;
}
else
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 57;
v___x_486_ = lean_uint32_dec_le(v_ch_403_, v___x_485_);
v___y_462_ = v___x_486_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_shiftr(v_ucount_400_, v___x_487_);
lean_dec(v_ucount_400_);
v___x_489_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_488_, v_acc_399_);
v___x_490_ = lean_string_push(v___x_489_, v_ch_403_);
v_p_u2080_397_ = v_p_404_;
v_acc_399_ = v___x_490_;
v_ucount_400_ = v___x_415_;
goto _start;
}
v___jp_416_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = l_Lean_Name_str___override(v_res_398_, v_acc_399_);
v___x_418_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = lean_nat_shiftr(v_ucount_400_, v___x_419_);
lean_dec(v_ucount_400_);
v___x_421_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_420_, v___x_418_);
v___x_422_ = lean_string_push(v___x_421_, v_ch_403_);
v_p_u2080_397_ = v_p_404_;
v_res_398_ = v___x_417_;
v_acc_399_ = v___x_422_;
v_ucount_400_ = v___x_415_;
goto _start;
}
v___jp_424_:
{
uint32_t v___x_425_; uint8_t v___x_426_; 
v___x_425_ = 85;
v___x_426_ = lean_uint32_dec_eq(v_ch_403_, v___x_425_);
if (v___x_426_ == 0)
{
goto v___jp_416_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(8u);
v___x_428_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_427_, v_s_396_, v_p_404_, v___x_415_);
if (lean_obj_tag(v___x_428_) == 1)
{
lean_object* v_val_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v_acc_434_; uint32_t v___x_435_; lean_object* v___x_436_; 
v_val_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_429_);
lean_dec_ref(v___x_428_);
v_fst_430_ = lean_ctor_get(v_val_429_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v_val_429_, 1);
lean_inc(v_snd_431_);
lean_dec(v_val_429_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_shiftr(v_ucount_400_, v___x_432_);
lean_dec(v_ucount_400_);
v_acc_434_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_433_, v_acc_399_);
v___x_435_ = l_Char_ofNat(v_snd_431_);
lean_dec(v_snd_431_);
v___x_436_ = lean_string_push(v_acc_434_, v___x_435_);
v_p_u2080_397_ = v_fst_430_;
v_acc_399_ = v___x_436_;
v_ucount_400_ = v___x_415_;
goto _start;
}
else
{
lean_dec(v___x_428_);
goto v___jp_416_;
}
}
}
v___jp_438_:
{
uint32_t v___x_439_; uint8_t v___x_440_; 
v___x_439_ = 117;
v___x_440_ = lean_uint32_dec_eq(v_ch_403_, v___x_439_);
if (v___x_440_ == 0)
{
goto v___jp_424_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_unsigned_to_nat(4u);
v___x_442_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_441_, v_s_396_, v_p_404_, v___x_415_);
if (lean_obj_tag(v___x_442_) == 1)
{
lean_object* v_val_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_acc_448_; uint32_t v___x_449_; lean_object* v___x_450_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref(v___x_442_);
v_fst_444_ = lean_ctor_get(v_val_443_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v_val_443_, 1);
lean_inc(v_snd_445_);
lean_dec(v_val_443_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_shiftr(v_ucount_400_, v___x_446_);
lean_dec(v_ucount_400_);
v_acc_448_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_447_, v_acc_399_);
v___x_449_ = l_Char_ofNat(v_snd_445_);
lean_dec(v_snd_445_);
v___x_450_ = lean_string_push(v_acc_448_, v___x_449_);
v_p_u2080_397_ = v_fst_444_;
v_acc_399_ = v___x_450_;
v_ucount_400_ = v___x_415_;
goto _start;
}
else
{
lean_dec(v___x_442_);
goto v___jp_424_;
}
}
}
v___jp_452_:
{
if (v___y_454_ == 0)
{
v___y_406_ = v___y_453_;
goto v___jp_405_;
}
else
{
uint32_t v___x_455_; uint32_t v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_string_utf8_get_fast(v_s_396_, v_p_404_);
v___x_456_ = 48;
v___x_457_ = lean_uint32_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_406_ = v___y_453_;
goto v___jp_405_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_string_utf8_next_fast(v_s_396_, v_p_404_);
v___x_459_ = ((lean_object*)(l_String_mangle___closed__0));
v_p_u2080_397_ = v___x_458_;
v_res_398_ = v___y_453_;
v_acc_399_ = v___x_459_;
v_ucount_400_ = v___x_415_;
goto _start;
}
}
}
v___jp_461_:
{
if (v___y_462_ == 0)
{
uint32_t v___x_463_; uint8_t v___x_464_; 
v___x_463_ = 120;
v___x_464_ = lean_uint32_dec_eq(v_ch_403_, v___x_463_);
if (v___x_464_ == 0)
{
goto v___jp_438_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_413_, v_s_396_, v_p_404_, v___x_415_);
if (lean_obj_tag(v___x_465_) == 1)
{
lean_object* v_val_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_acc_471_; uint32_t v___x_472_; lean_object* v___x_473_; 
v_val_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_466_);
lean_dec_ref(v___x_465_);
v_fst_467_ = lean_ctor_get(v_val_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v_val_466_, 1);
lean_inc(v_snd_468_);
lean_dec(v_val_466_);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_shiftr(v_ucount_400_, v___x_469_);
lean_dec(v_ucount_400_);
v_acc_471_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_470_, v_acc_399_);
v___x_472_ = l_Char_ofNat(v_snd_468_);
lean_dec(v_snd_468_);
v___x_473_ = lean_string_push(v_acc_471_, v___x_472_);
v_p_u2080_397_ = v_fst_467_;
v_acc_399_ = v___x_473_;
v_ucount_400_ = v___x_415_;
goto _start;
}
else
{
lean_dec(v___x_465_);
goto v___jp_438_;
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_res_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_nat_shiftr(v_ucount_400_, v___x_475_);
lean_dec(v_ucount_400_);
v___x_477_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_476_, v_acc_399_);
v_res_478_ = l_Lean_Name_str___override(v_res_398_, v___x_477_);
v___x_479_ = 48;
v___x_480_ = lean_uint32_dec_eq(v_ch_403_, v___x_479_);
if (v___x_480_ == 0)
{
v___y_406_ = v_res_478_;
goto v___jp_405_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = lean_nat_dec_eq(v_p_404_, v___x_401_);
if (v___x_481_ == 0)
{
v___y_453_ = v_res_478_;
v___y_454_ = v___x_480_;
goto v___jp_452_;
}
else
{
v___y_453_ = v_res_478_;
v___y_454_ = v___x_412_;
goto v___jp_452_;
}
}
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_ucount_400_, v___x_492_);
lean_dec(v_ucount_400_);
v_p_u2080_397_ = v_p_404_;
v_ucount_400_ = v___x_493_;
goto _start;
}
v___jp_405_:
{
uint32_t v___x_407_; uint32_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = 48;
v___x_408_ = lean_uint32_sub(v_ch_403_, v___x_407_);
v___x_409_ = lean_uint32_to_nat(v___x_408_);
v___x_410_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_396_, v_p_404_, v___y_406_, v___x_409_);
return v___x_410_;
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_p_u2080_397_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_shiftr(v_ucount_400_, v___x_495_);
lean_dec(v_ucount_400_);
v___x_497_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_496_, v_acc_399_);
v___x_498_ = l_Lean_Name_str___override(v_res_398_, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* v_s_499_, lean_object* v_p_500_, lean_object* v_res_501_){
_start:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_string_utf8_byte_size(v_s_499_);
v___x_503_ = lean_nat_dec_eq(v_p_500_, v___x_502_);
if (v___x_503_ == 0)
{
uint32_t v_ch_504_; lean_object* v_p_505_; uint8_t v___y_512_; uint8_t v___y_521_; uint32_t v___x_534_; uint8_t v___x_535_; 
v_ch_504_ = lean_string_utf8_get_fast(v_s_499_, v_p_500_);
v_p_505_ = lean_string_utf8_next_fast(v_s_499_, v_p_500_);
v___x_534_ = 48;
v___x_535_ = lean_uint32_dec_le(v___x_534_, v_ch_504_);
if (v___x_535_ == 0)
{
v___y_521_ = v___x_535_;
goto v___jp_520_;
}
else
{
uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_536_ = 57;
v___x_537_ = lean_uint32_dec_le(v_ch_504_, v___x_536_);
v___y_521_ = v___x_537_;
goto v___jp_520_;
}
v___jp_506_:
{
uint32_t v___x_507_; uint32_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = 48;
v___x_508_ = lean_uint32_sub(v_ch_504_, v___x_507_);
v___x_509_ = lean_uint32_to_nat(v___x_508_);
v___x_510_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_499_, v_p_505_, v_res_501_, v___x_509_);
return v___x_510_;
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
goto v___jp_506_;
}
else
{
uint32_t v___x_513_; uint32_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_string_utf8_get_fast(v_s_499_, v_p_505_);
v___x_514_ = 48;
v___x_515_ = lean_uint32_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
goto v___jp_506_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = lean_string_utf8_next_fast(v_s_499_, v_p_505_);
v___x_517_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_499_, v___x_516_, v_res_501_, v___x_517_, v___x_518_);
return v___x_519_;
}
}
}
v___jp_520_:
{
if (v___y_521_ == 0)
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 95;
v___x_523_ = lean_uint32_dec_eq(v_ch_504_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_525_ = lean_string_push(v___x_524_, v_ch_504_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_499_, v_p_505_, v_res_501_, v___x_525_, v___x_526_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_499_, v_p_505_, v_res_501_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
else
{
uint32_t v___x_531_; uint8_t v___x_532_; 
v___x_531_ = 48;
v___x_532_ = lean_uint32_dec_eq(v_ch_504_, v___x_531_);
if (v___x_532_ == 0)
{
goto v___jp_506_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_eq(v_p_505_, v___x_502_);
if (v___x_533_ == 0)
{
v___y_512_ = v___x_532_;
goto v___jp_511_;
}
else
{
v___y_512_ = v___x_503_;
goto v___jp_511_;
}
}
}
}
}
else
{
return v_res_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* v_s_538_, lean_object* v_p_539_, lean_object* v_res_540_, lean_object* v_n_541_){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_string_utf8_byte_size(v_s_538_);
v___x_543_ = lean_nat_dec_eq(v_p_539_, v___x_542_);
if (v___x_543_ == 0)
{
uint32_t v_ch_544_; lean_object* v_p_545_; uint8_t v___y_547_; uint32_t v___x_559_; uint8_t v___x_560_; 
v_ch_544_ = lean_string_utf8_get_fast(v_s_538_, v_p_539_);
v_p_545_ = lean_string_utf8_next_fast(v_s_538_, v_p_539_);
lean_dec(v_p_539_);
v___x_559_ = 48;
v___x_560_ = lean_uint32_dec_le(v___x_559_, v_ch_544_);
if (v___x_560_ == 0)
{
v___y_547_ = v___x_560_;
goto v___jp_546_;
}
else
{
uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 57;
v___x_562_ = lean_uint32_dec_le(v_ch_544_, v___x_561_);
v___y_547_ = v___x_562_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v_res_548_; uint8_t v___x_549_; 
v_res_548_ = l_Lean_Name_num___override(v_res_540_, v_n_541_);
v___x_549_ = lean_nat_dec_eq(v_p_545_, v___x_542_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = lean_string_utf8_next_fast(v_s_538_, v_p_545_);
v___x_551_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_538_, v___x_550_, v_res_548_);
return v___x_551_;
}
else
{
return v_res_548_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint32_t v___x_554_; uint32_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_552_ = lean_unsigned_to_nat(10u);
v___x_553_ = lean_nat_mul(v_n_541_, v___x_552_);
lean_dec(v_n_541_);
v___x_554_ = 48;
v___x_555_ = lean_uint32_sub(v_ch_544_, v___x_554_);
v___x_556_ = lean_uint32_to_nat(v___x_555_);
v___x_557_ = lean_nat_add(v___x_553_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_553_);
v_p_539_ = v_p_545_;
v_n_541_ = v___x_557_;
goto _start;
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_p_539_);
v___x_563_ = l_Lean_Name_num___override(v_res_540_, v_n_541_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* v_s_564_, lean_object* v_p_565_, lean_object* v_res_566_, lean_object* v_n_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_564_, v_p_565_, v_res_566_, v_n_567_);
lean_dec_ref(v_s_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* v_s_569_, lean_object* v_p_570_, lean_object* v_res_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_569_, v_p_570_, v_res_571_);
lean_dec(v_p_570_);
lean_dec_ref(v_s_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* v_s_573_, lean_object* v_p_u2080_574_, lean_object* v_res_575_, lean_object* v_acc_576_, lean_object* v_ucount_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_573_, v_p_u2080_574_, v_res_575_, v_acc_576_, v_ucount_577_);
lean_dec_ref(v_s_573_);
return v_res_578_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_579_; lean_object* v___x_580_; 
v___x_579_ = 120;
v___x_580_ = lean_box_uint32(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t v_ch_581_, lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_){
_start:
{
uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 120;
v___x_586_ = lean_uint32_dec_eq(v_ch_581_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_h__1_583_);
v___x_587_ = lean_box_uint32(v_ch_581_);
v___x_588_ = lean_apply_4(v_h__2_584_, v___x_587_, v_x_582_, lean_box(0), lean_box(0));
return v___x_588_;
}
else
{
if (lean_obj_tag(v_x_582_) == 1)
{
lean_object* v_val_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; 
lean_dec(v_h__2_584_);
v_val_589_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_val_589_);
lean_dec_ref(v_x_582_);
v_fst_590_ = lean_ctor_get(v_val_589_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v_val_589_, 1);
lean_inc(v_snd_591_);
lean_dec(v_val_589_);
v___x_592_ = lean_apply_3(v_h__1_583_, v_fst_590_, v_snd_591_, lean_box(0));
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_h__1_583_);
v___x_593_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_594_ = lean_apply_4(v_h__2_584_, v___x_593_, v_x_582_, lean_box(0), lean_box(0));
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* v_ch_595_, lean_object* v_x_596_, lean_object* v_h__1_597_, lean_object* v_h__2_598_){
_start:
{
uint32_t v_ch_81__boxed_599_; lean_object* v_res_600_; 
v_ch_81__boxed_599_ = lean_unbox_uint32(v_ch_595_);
lean_dec(v_ch_595_);
v_res_600_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_81__boxed_599_, v_x_596_, v_h__1_597_, v_h__2_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* v_s_601_, lean_object* v_motive_602_, uint32_t v_ch_603_, lean_object* v_x_604_, lean_object* v_h__1_605_, lean_object* v_h__2_606_){
_start:
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 120;
v___x_608_ = lean_uint32_dec_eq(v_ch_603_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_h__1_605_);
v___x_609_ = lean_box_uint32(v_ch_603_);
v___x_610_ = lean_apply_4(v_h__2_606_, v___x_609_, v_x_604_, lean_box(0), lean_box(0));
return v___x_610_;
}
else
{
if (lean_obj_tag(v_x_604_) == 1)
{
lean_object* v_val_611_; lean_object* v_fst_612_; lean_object* v_snd_613_; lean_object* v___x_614_; 
lean_dec(v_h__2_606_);
v_val_611_ = lean_ctor_get(v_x_604_, 0);
lean_inc(v_val_611_);
lean_dec_ref(v_x_604_);
v_fst_612_ = lean_ctor_get(v_val_611_, 0);
lean_inc(v_fst_612_);
v_snd_613_ = lean_ctor_get(v_val_611_, 1);
lean_inc(v_snd_613_);
lean_dec(v_val_611_);
v___x_614_ = lean_apply_3(v_h__1_605_, v_fst_612_, v_snd_613_, lean_box(0));
return v___x_614_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_h__1_605_);
v___x_615_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_616_ = lean_apply_4(v_h__2_606_, v___x_615_, v_x_604_, lean_box(0), lean_box(0));
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* v_s_617_, lean_object* v_motive_618_, lean_object* v_ch_619_, lean_object* v_x_620_, lean_object* v_h__1_621_, lean_object* v_h__2_622_){
_start:
{
uint32_t v_ch_111__boxed_623_; lean_object* v_res_624_; 
v_ch_111__boxed_623_ = lean_unbox_uint32(v_ch_619_);
lean_dec(v_ch_619_);
v_res_624_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_617_, v_motive_618_, v_ch_111__boxed_623_, v_x_620_, v_h__1_621_, v_h__2_622_);
lean_dec_ref(v_s_617_);
return v_res_624_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_625_; lean_object* v___x_626_; 
v___x_625_ = 117;
v___x_626_ = lean_box_uint32(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t v_ch_627_, lean_object* v_x_628_, lean_object* v_h__1_629_, lean_object* v_h__2_630_){
_start:
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 117;
v___x_632_ = lean_uint32_dec_eq(v_ch_627_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v_h__1_629_);
v___x_633_ = lean_box_uint32(v_ch_627_);
v___x_634_ = lean_apply_4(v_h__2_630_, v___x_633_, v_x_628_, lean_box(0), lean_box(0));
return v___x_634_;
}
else
{
if (lean_obj_tag(v_x_628_) == 1)
{
lean_object* v_val_635_; lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___x_638_; 
lean_dec(v_h__2_630_);
v_val_635_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_val_635_);
lean_dec_ref(v_x_628_);
v_fst_636_ = lean_ctor_get(v_val_635_, 0);
lean_inc(v_fst_636_);
v_snd_637_ = lean_ctor_get(v_val_635_, 1);
lean_inc(v_snd_637_);
lean_dec(v_val_635_);
v___x_638_ = lean_apply_3(v_h__1_629_, v_fst_636_, v_snd_637_, lean_box(0));
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_h__1_629_);
v___x_639_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_640_ = lean_apply_4(v_h__2_630_, v___x_639_, v_x_628_, lean_box(0), lean_box(0));
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* v_ch_641_, lean_object* v_x_642_, lean_object* v_h__1_643_, lean_object* v_h__2_644_){
_start:
{
uint32_t v_ch_81__boxed_645_; lean_object* v_res_646_; 
v_ch_81__boxed_645_ = lean_unbox_uint32(v_ch_641_);
lean_dec(v_ch_641_);
v_res_646_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_81__boxed_645_, v_x_642_, v_h__1_643_, v_h__2_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* v_s_647_, lean_object* v_motive_648_, uint32_t v_ch_649_, lean_object* v_x_650_, lean_object* v_h__1_651_, lean_object* v_h__2_652_){
_start:
{
uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_653_ = 117;
v___x_654_ = lean_uint32_dec_eq(v_ch_649_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v_h__1_651_);
v___x_655_ = lean_box_uint32(v_ch_649_);
v___x_656_ = lean_apply_4(v_h__2_652_, v___x_655_, v_x_650_, lean_box(0), lean_box(0));
return v___x_656_;
}
else
{
if (lean_obj_tag(v_x_650_) == 1)
{
lean_object* v_val_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_660_; 
lean_dec(v_h__2_652_);
v_val_657_ = lean_ctor_get(v_x_650_, 0);
lean_inc(v_val_657_);
lean_dec_ref(v_x_650_);
v_fst_658_ = lean_ctor_get(v_val_657_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v_val_657_, 1);
lean_inc(v_snd_659_);
lean_dec(v_val_657_);
v___x_660_ = lean_apply_3(v_h__1_651_, v_fst_658_, v_snd_659_, lean_box(0));
return v___x_660_;
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_h__1_651_);
v___x_661_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_662_ = lean_apply_4(v_h__2_652_, v___x_661_, v_x_650_, lean_box(0), lean_box(0));
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* v_s_663_, lean_object* v_motive_664_, lean_object* v_ch_665_, lean_object* v_x_666_, lean_object* v_h__1_667_, lean_object* v_h__2_668_){
_start:
{
uint32_t v_ch_111__boxed_669_; lean_object* v_res_670_; 
v_ch_111__boxed_669_ = lean_unbox_uint32(v_ch_665_);
lean_dec(v_ch_665_);
v_res_670_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_663_, v_motive_664_, v_ch_111__boxed_669_, v_x_666_, v_h__1_667_, v_h__2_668_);
lean_dec_ref(v_s_663_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_671_; lean_object* v___x_672_; 
v___x_671_ = 85;
v___x_672_ = lean_box_uint32(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t v_ch_673_, lean_object* v_x_674_, lean_object* v_h__1_675_, lean_object* v_h__2_676_){
_start:
{
uint32_t v___x_677_; uint8_t v___x_678_; 
v___x_677_ = 85;
v___x_678_ = lean_uint32_dec_eq(v_ch_673_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_h__1_675_);
v___x_679_ = lean_box_uint32(v_ch_673_);
v___x_680_ = lean_apply_4(v_h__2_676_, v___x_679_, v_x_674_, lean_box(0), lean_box(0));
return v___x_680_;
}
else
{
if (lean_obj_tag(v_x_674_) == 1)
{
lean_object* v_val_681_; lean_object* v_fst_682_; lean_object* v_snd_683_; lean_object* v___x_684_; 
lean_dec(v_h__2_676_);
v_val_681_ = lean_ctor_get(v_x_674_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v_x_674_);
v_fst_682_ = lean_ctor_get(v_val_681_, 0);
lean_inc(v_fst_682_);
v_snd_683_ = lean_ctor_get(v_val_681_, 1);
lean_inc(v_snd_683_);
lean_dec(v_val_681_);
v___x_684_ = lean_apply_3(v_h__1_675_, v_fst_682_, v_snd_683_, lean_box(0));
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_h__1_675_);
v___x_685_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_686_ = lean_apply_4(v_h__2_676_, v___x_685_, v_x_674_, lean_box(0), lean_box(0));
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* v_ch_687_, lean_object* v_x_688_, lean_object* v_h__1_689_, lean_object* v_h__2_690_){
_start:
{
uint32_t v_ch_81__boxed_691_; lean_object* v_res_692_; 
v_ch_81__boxed_691_ = lean_unbox_uint32(v_ch_687_);
lean_dec(v_ch_687_);
v_res_692_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_81__boxed_691_, v_x_688_, v_h__1_689_, v_h__2_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* v_s_693_, lean_object* v_motive_694_, uint32_t v_ch_695_, lean_object* v_x_696_, lean_object* v_h__1_697_, lean_object* v_h__2_698_){
_start:
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 85;
v___x_700_ = lean_uint32_dec_eq(v_ch_695_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v_h__1_697_);
v___x_701_ = lean_box_uint32(v_ch_695_);
v___x_702_ = lean_apply_4(v_h__2_698_, v___x_701_, v_x_696_, lean_box(0), lean_box(0));
return v___x_702_;
}
else
{
if (lean_obj_tag(v_x_696_) == 1)
{
lean_object* v_val_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_706_; 
lean_dec(v_h__2_698_);
v_val_703_ = lean_ctor_get(v_x_696_, 0);
lean_inc(v_val_703_);
lean_dec_ref(v_x_696_);
v_fst_704_ = lean_ctor_get(v_val_703_, 0);
lean_inc(v_fst_704_);
v_snd_705_ = lean_ctor_get(v_val_703_, 1);
lean_inc(v_snd_705_);
lean_dec(v_val_703_);
v___x_706_ = lean_apply_3(v_h__1_697_, v_fst_704_, v_snd_705_, lean_box(0));
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_h__1_697_);
v___x_707_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_708_ = lean_apply_4(v_h__2_698_, v___x_707_, v_x_696_, lean_box(0), lean_box(0));
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* v_s_709_, lean_object* v_motive_710_, lean_object* v_ch_711_, lean_object* v_x_712_, lean_object* v_h__1_713_, lean_object* v_h__2_714_){
_start:
{
uint32_t v_ch_111__boxed_715_; lean_object* v_res_716_; 
v_ch_111__boxed_715_ = lean_unbox_uint32(v_ch_711_);
lean_dec(v_ch_711_);
v_res_716_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_709_, v_motive_710_, v_ch_111__boxed_715_, v_x_712_, v_h__1_713_, v_h__2_714_);
lean_dec_ref(v_s_709_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* v_s_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_box(0);
v___x_720_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_717_, v___x_718_, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* v_s_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Name_demangle(v_s_721_);
lean_dec_ref(v_s_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* v_s_723_){
_start:
{
lean_object* v_n_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_n_724_ = l_Lean_Name_demangle(v_s_723_);
lean_inc(v_n_724_);
v___x_725_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_724_);
v___x_726_ = lean_string_dec_eq(v___x_725_, v_s_723_);
lean_dec_ref(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
lean_dec(v_n_724_);
v___x_727_ = lean_box(0);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_n_724_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* v_s_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Name_demangle_x3f(v_s_729_);
lean_dec_ref(v_s_729_);
return v_res_730_;
}
}
lean_object* runtime_initialize_Lean_Setup(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NameMangling(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
