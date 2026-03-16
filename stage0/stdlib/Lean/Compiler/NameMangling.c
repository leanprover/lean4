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
lean_object* v___x_208_; 
v___x_208_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(v_n_205_, v_h__1_206_, v_h__2_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(lean_object* v_motive_209_, lean_object* v_n_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(v_motive_209_, v_n_210_, v_h__1_211_, v_h__2_212_);
lean_dec(v_n_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_dec(v_h__1_215_);
v___x_217_ = lean_box(0);
v___x_218_ = lean_apply_1(v_h__2_216_, v___x_217_);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_216_);
v_val_219_ = lean_ctor_get(v_x_214_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v_x_214_);
v___x_220_ = lean_apply_1(v_h__1_215_, v_val_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(lean_object* v_motive_221_, lean_object* v_x_222_, lean_object* v_h__1_223_, lean_object* v_h__2_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(v_x_222_, v_h__1_223_, v_h__2_224_);
return v___x_225_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(lean_object* v_s_226_, lean_object* v_p_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_string_utf8_byte_size(v_s_226_);
v___x_229_ = lean_nat_dec_eq(v_p_227_, v___x_228_);
if (v___x_229_ == 0)
{
uint32_t v_b_230_; uint32_t v___x_231_; uint8_t v___x_232_; 
v_b_230_ = lean_string_utf8_get_fast(v_s_226_, v_p_227_);
v___x_231_ = 95;
v___x_232_ = lean_uint32_dec_eq(v_b_230_, v___x_231_);
if (v___x_232_ == 0)
{
uint32_t v___x_233_; uint8_t v___x_234_; 
v___x_233_ = 120;
v___x_234_ = lean_uint32_dec_eq(v_b_230_, v___x_233_);
if (v___x_234_ == 0)
{
uint32_t v___x_235_; uint8_t v___x_236_; 
v___x_235_ = 117;
v___x_236_ = lean_uint32_dec_eq(v_b_230_, v___x_235_);
if (v___x_236_ == 0)
{
uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_237_ = 85;
v___x_238_ = lean_uint32_dec_eq(v_b_230_, v___x_237_);
if (v___x_238_ == 0)
{
uint32_t v___x_239_; uint8_t v___x_240_; 
lean_dec(v_p_227_);
v___x_239_ = 48;
v___x_240_ = lean_uint32_dec_le(v___x_239_, v_b_230_);
if (v___x_240_ == 0)
{
return v___x_240_;
}
else
{
uint32_t v___x_241_; uint8_t v___x_242_; 
v___x_241_ = 57;
v___x_242_ = lean_uint32_dec_le(v_b_230_, v___x_241_);
return v___x_242_;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_unsigned_to_nat(8u);
v___x_244_ = lean_string_utf8_next_fast(v_s_226_, v_p_227_);
lean_dec(v_p_227_);
v___x_245_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_243_, v_s_226_, v___x_244_);
return v___x_245_;
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_string_utf8_next_fast(v_s_226_, v_p_227_);
lean_dec(v_p_227_);
v___x_248_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_246_, v_s_226_, v___x_247_);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_unsigned_to_nat(2u);
v___x_250_ = lean_string_utf8_next_fast(v_s_226_, v_p_227_);
lean_dec(v_p_227_);
v___x_251_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_249_, v_s_226_, v___x_250_);
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_string_utf8_next_fast(v_s_226_, v_p_227_);
lean_dec(v_p_227_);
v_p_227_ = v___x_252_;
goto _start;
}
}
else
{
lean_dec(v_p_227_);
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(lean_object* v_s_254_, lean_object* v_p_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_254_, v_p_255_);
lean_dec_ref(v_s_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(lean_object* v_prev_258_, lean_object* v_next_259_){
_start:
{
if (lean_obj_tag(v_prev_258_) == 1)
{
lean_object* v_str_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_str_263_ = lean_ctor_get(v_prev_258_, 1);
v___x_264_ = lean_string_utf8_byte_size(v_str_263_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_nat_dec_eq(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint32_t v___x_271_; uint32_t v___x_272_; uint8_t v___x_273_; 
lean_inc_ref(v_str_263_);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v_str_263_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_sub(v___x_264_, v___x_268_);
v___x_270_ = l_String_Slice_posLE(v___x_267_, v___x_269_);
lean_dec_ref(v___x_267_);
v___x_271_ = lean_string_utf8_get_fast(v_str_263_, v___x_270_);
lean_dec(v___x_270_);
v___x_272_ = 95;
v___x_273_ = lean_uint32_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
goto v___jp_260_;
}
else
{
return v___x_273_;
}
}
else
{
goto v___jp_260_;
}
}
else
{
goto v___jp_260_;
}
v___jp_260_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_next_259_, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(lean_object* v_prev_274_, lean_object* v_next_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_prev_274_, v_next_275_);
lean_dec_ref(v_next_275_);
lean_dec(v_prev_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* v_x_281_){
_start:
{
switch(lean_obj_tag(v_x_281_))
{
case 0:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l_String_mangle___closed__0));
return v___x_282_;
}
case 1:
{
lean_object* v_pre_283_; lean_object* v_str_284_; lean_object* v_m_285_; 
v_pre_283_ = lean_ctor_get(v_x_281_, 0);
lean_inc(v_pre_283_);
v_str_284_ = lean_ctor_get(v_x_281_, 1);
lean_inc_ref(v_str_284_);
lean_dec_ref(v_x_281_);
v_m_285_ = l_String_mangle(v_str_284_);
lean_dec_ref(v_str_284_);
if (lean_obj_tag(v_pre_283_) == 0)
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_m_285_, v___x_286_);
if (v___x_287_ == 0)
{
return v_m_285_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0));
v___x_289_ = lean_string_append(v___x_288_, v_m_285_);
lean_dec_ref(v_m_285_);
return v___x_289_;
}
}
else
{
lean_object* v_m1_290_; lean_object* v___y_292_; uint8_t v___x_295_; 
lean_inc(v_pre_283_);
v_m1_290_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_283_);
v___x_295_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(v_pre_283_, v_m_285_);
lean_dec(v_pre_283_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___y_292_ = v___x_296_;
goto v___jp_291_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2));
v___y_292_ = v___x_297_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_string_append(v_m1_290_, v___y_292_);
lean_dec_ref(v___y_292_);
v___x_294_ = lean_string_append(v___x_293_, v_m_285_);
lean_dec_ref(v_m_285_);
return v___x_294_;
}
}
}
default: 
{
lean_object* v_pre_298_; 
v_pre_298_ = lean_ctor_get(v_x_281_, 0);
if (lean_obj_tag(v_pre_298_) == 0)
{
lean_object* v_i_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_i_299_ = lean_ctor_get(v_x_281_, 1);
lean_inc(v_i_299_);
lean_dec_ref(v_x_281_);
v___x_300_ = l_Nat_reprFast(v_i_299_);
v___x_301_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v_i_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_inc(v_pre_298_);
v_i_303_ = lean_ctor_get(v_x_281_, 1);
lean_inc(v_i_303_);
lean_dec_ref(v_x_281_);
v___x_304_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_pre_298_);
v___x_305_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1));
v___x_306_ = lean_string_append(v___x_304_, v___x_305_);
v___x_307_ = l_Nat_reprFast(v_i_303_);
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
lean_dec_ref(v___x_307_);
v___x_309_ = lean_string_append(v___x_308_, v___x_305_);
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_mangle(lean_object* v_n_310_, lean_object* v_pre_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_310_);
v___x_313_ = lean_string_append(v_pre_311_, v___x_312_);
lean_dec_ref(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_mkMangledBoxedName___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_316_ = lean_string_utf8_byte_size(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* lean_mk_mangled_boxed_name(lean_object* v_s_318_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_322_ = ((lean_object*)(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3));
v___x_323_ = lean_string_utf8_byte_size(v_s_318_);
v___x_324_ = lean_obj_once(&l_Lean_mkMangledBoxedName___closed__1, &l_Lean_mkMangledBoxedName___closed__1_once, _init_l_Lean_mkMangledBoxedName___closed__1);
v___x_325_ = lean_nat_dec_le(v___x_324_, v___x_323_);
if (v___x_325_ == 0)
{
goto v___jp_319_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_nat_sub(v___x_323_, v___x_324_);
v___x_328_ = lean_string_memcmp(v_s_318_, v___x_322_, v___x_327_, v___x_326_, v___x_324_);
lean_dec(v___x_327_);
if (v___x_328_ == 0)
{
goto v___jp_319_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_mkMangledBoxedName___closed__2));
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
v___x_333_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_334_ = l_Lean_Name_mangle(v_moduleName_331_, v___x_333_);
return v___x_334_;
}
else
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_335_ = lean_ctor_get(v_pkg_x3f_332_, 0);
v___x_336_ = l_String_mangle(v_val_335_);
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
v___x_348_ = ((lean_object*)(l_String_mangle___closed__0));
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
v___x_372_ = l_String_mangle(v_val_370_);
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
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_string_utf8_byte_size(v_s_387_);
v___x_393_ = lean_nat_dec_eq(v_p_u2080_388_, v___x_392_);
if (v___x_393_ == 0)
{
uint32_t v_ch_394_; lean_object* v_p_395_; lean_object* v___y_397_; uint32_t v___x_402_; uint8_t v___x_403_; 
v_ch_394_ = lean_string_utf8_get_fast(v_s_387_, v_p_u2080_388_);
v_p_395_ = lean_string_utf8_next_fast(v_s_387_, v_p_u2080_388_);
lean_dec(v_p_u2080_388_);
v___x_402_ = 95;
v___x_403_ = lean_uint32_dec_eq(v_ch_394_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___y_444_; uint8_t v___y_445_; uint8_t v___y_453_; uint8_t v___x_473_; 
v___x_404_ = lean_unsigned_to_nat(2u);
v___x_405_ = lean_nat_mod(v_ucount_391_, v___x_404_);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_nat_dec_eq(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
if (v___x_473_ == 0)
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 48;
v___x_475_ = lean_uint32_dec_le(v___x_474_, v_ch_394_);
if (v___x_475_ == 0)
{
v___y_453_ = v___x_475_;
goto v___jp_452_;
}
else
{
uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 57;
v___x_477_ = lean_uint32_dec_le(v_ch_394_, v___x_476_);
v___y_453_ = v___x_477_;
goto v___jp_452_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_shiftr(v_ucount_391_, v___x_478_);
lean_dec(v_ucount_391_);
v___x_480_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_479_, v_acc_390_);
v___x_481_ = lean_string_push(v___x_480_, v_ch_394_);
v_p_u2080_388_ = v_p_395_;
v_acc_390_ = v___x_481_;
v_ucount_391_ = v___x_406_;
goto _start;
}
v___jp_407_:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_408_ = l_Lean_Name_str___override(v_res_389_, v_acc_390_);
v___x_409_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_shiftr(v_ucount_391_, v___x_410_);
lean_dec(v_ucount_391_);
v___x_412_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_411_, v___x_409_);
v___x_413_ = lean_string_push(v___x_412_, v_ch_394_);
v_p_u2080_388_ = v_p_395_;
v_res_389_ = v___x_408_;
v_acc_390_ = v___x_413_;
v_ucount_391_ = v___x_406_;
goto _start;
}
v___jp_415_:
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 85;
v___x_417_ = lean_uint32_dec_eq(v_ch_394_, v___x_416_);
if (v___x_417_ == 0)
{
goto v___jp_407_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(8u);
v___x_419_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_418_, v_s_387_, v_p_395_, v___x_406_);
if (lean_obj_tag(v___x_419_) == 1)
{
lean_object* v_val_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_acc_425_; uint32_t v___x_426_; lean_object* v___x_427_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref(v___x_419_);
v_fst_421_ = lean_ctor_get(v_val_420_, 0);
lean_inc(v_fst_421_);
v_snd_422_ = lean_ctor_get(v_val_420_, 1);
lean_inc(v_snd_422_);
lean_dec(v_val_420_);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_shiftr(v_ucount_391_, v___x_423_);
lean_dec(v_ucount_391_);
v_acc_425_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_424_, v_acc_390_);
v___x_426_ = l_Char_ofNat(v_snd_422_);
lean_dec(v_snd_422_);
v___x_427_ = lean_string_push(v_acc_425_, v___x_426_);
v_p_u2080_388_ = v_fst_421_;
v_acc_390_ = v___x_427_;
v_ucount_391_ = v___x_406_;
goto _start;
}
else
{
lean_dec(v___x_419_);
goto v___jp_407_;
}
}
}
v___jp_429_:
{
uint32_t v___x_430_; uint8_t v___x_431_; 
v___x_430_ = 117;
v___x_431_ = lean_uint32_dec_eq(v_ch_394_, v___x_430_);
if (v___x_431_ == 0)
{
goto v___jp_415_;
}
else
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_unsigned_to_nat(4u);
v___x_433_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_432_, v_s_387_, v_p_395_, v___x_406_);
if (lean_obj_tag(v___x_433_) == 1)
{
lean_object* v_val_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_acc_439_; uint32_t v___x_440_; lean_object* v___x_441_; 
v_val_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref(v___x_433_);
v_fst_435_ = lean_ctor_get(v_val_434_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v_val_434_, 1);
lean_inc(v_snd_436_);
lean_dec(v_val_434_);
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = lean_nat_shiftr(v_ucount_391_, v___x_437_);
lean_dec(v_ucount_391_);
v_acc_439_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_438_, v_acc_390_);
v___x_440_ = l_Char_ofNat(v_snd_436_);
lean_dec(v_snd_436_);
v___x_441_ = lean_string_push(v_acc_439_, v___x_440_);
v_p_u2080_388_ = v_fst_435_;
v_acc_390_ = v___x_441_;
v_ucount_391_ = v___x_406_;
goto _start;
}
else
{
lean_dec(v___x_433_);
goto v___jp_415_;
}
}
}
v___jp_443_:
{
if (v___y_445_ == 0)
{
v___y_397_ = v___y_444_;
goto v___jp_396_;
}
else
{
uint32_t v___x_446_; uint32_t v___x_447_; uint8_t v___x_448_; 
v___x_446_ = lean_string_utf8_get_fast(v_s_387_, v_p_395_);
v___x_447_ = 48;
v___x_448_ = lean_uint32_dec_eq(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
v___y_397_ = v___y_444_;
goto v___jp_396_;
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_string_utf8_next_fast(v_s_387_, v_p_395_);
v___x_450_ = ((lean_object*)(l_String_mangle___closed__0));
v_p_u2080_388_ = v___x_449_;
v_res_389_ = v___y_444_;
v_acc_390_ = v___x_450_;
v_ucount_391_ = v___x_406_;
goto _start;
}
}
}
v___jp_452_:
{
if (v___y_453_ == 0)
{
uint32_t v___x_454_; uint8_t v___x_455_; 
v___x_454_ = 120;
v___x_455_ = lean_uint32_dec_eq(v_ch_394_, v___x_454_);
if (v___x_455_ == 0)
{
goto v___jp_429_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(v___x_404_, v_s_387_, v_p_395_, v___x_406_);
if (lean_obj_tag(v___x_456_) == 1)
{
lean_object* v_val_457_; lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_acc_462_; uint32_t v___x_463_; lean_object* v___x_464_; 
v_val_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_457_);
lean_dec_ref(v___x_456_);
v_fst_458_ = lean_ctor_get(v_val_457_, 0);
lean_inc(v_fst_458_);
v_snd_459_ = lean_ctor_get(v_val_457_, 1);
lean_inc(v_snd_459_);
lean_dec(v_val_457_);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_shiftr(v_ucount_391_, v___x_460_);
lean_dec(v_ucount_391_);
v_acc_462_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_461_, v_acc_390_);
v___x_463_ = l_Char_ofNat(v_snd_459_);
lean_dec(v_snd_459_);
v___x_464_ = lean_string_push(v_acc_462_, v___x_463_);
v_p_u2080_388_ = v_fst_458_;
v_acc_390_ = v___x_464_;
v_ucount_391_ = v___x_406_;
goto _start;
}
else
{
lean_dec(v___x_456_);
goto v___jp_429_;
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_res_469_; uint32_t v___x_470_; uint8_t v___x_471_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_shiftr(v_ucount_391_, v___x_466_);
lean_dec(v_ucount_391_);
v___x_468_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_467_, v_acc_390_);
v_res_469_ = l_Lean_Name_str___override(v_res_389_, v___x_468_);
v___x_470_ = 48;
v___x_471_ = lean_uint32_dec_eq(v_ch_394_, v___x_470_);
if (v___x_471_ == 0)
{
v___y_397_ = v_res_469_;
goto v___jp_396_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_eq(v_p_395_, v___x_392_);
if (v___x_472_ == 0)
{
v___y_444_ = v_res_469_;
v___y_445_ = v___x_471_;
goto v___jp_443_;
}
else
{
v___y_444_ = v_res_469_;
v___y_445_ = v___x_403_;
goto v___jp_443_;
}
}
}
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_ucount_391_, v___x_483_);
lean_dec(v_ucount_391_);
v_p_u2080_388_ = v_p_395_;
v_ucount_391_ = v___x_484_;
goto _start;
}
v___jp_396_:
{
uint32_t v___x_398_; uint32_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_398_ = 48;
v___x_399_ = lean_uint32_sub(v_ch_394_, v___x_398_);
v___x_400_ = lean_uint32_to_nat(v___x_399_);
v___x_401_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_387_, v_p_395_, v___y_397_, v___x_400_);
return v___x_401_;
}
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec(v_p_u2080_388_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_shiftr(v_ucount_391_, v___x_486_);
lean_dec(v_ucount_391_);
v___x_488_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_487_, v_acc_390_);
v___x_489_ = l_Lean_Name_str___override(v_res_389_, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(lean_object* v_s_490_, lean_object* v_p_491_, lean_object* v_res_492_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_string_utf8_byte_size(v_s_490_);
v___x_494_ = lean_nat_dec_eq(v_p_491_, v___x_493_);
if (v___x_494_ == 0)
{
uint32_t v_ch_495_; lean_object* v_p_496_; uint8_t v___y_503_; uint8_t v___y_512_; uint32_t v___x_525_; uint8_t v___x_526_; 
v_ch_495_ = lean_string_utf8_get_fast(v_s_490_, v_p_491_);
v_p_496_ = lean_string_utf8_next_fast(v_s_490_, v_p_491_);
v___x_525_ = 48;
v___x_526_ = lean_uint32_dec_le(v___x_525_, v_ch_495_);
if (v___x_526_ == 0)
{
v___y_512_ = v___x_526_;
goto v___jp_511_;
}
else
{
uint32_t v___x_527_; uint8_t v___x_528_; 
v___x_527_ = 57;
v___x_528_ = lean_uint32_dec_le(v_ch_495_, v___x_527_);
v___y_512_ = v___x_528_;
goto v___jp_511_;
}
v___jp_497_:
{
uint32_t v___x_498_; uint32_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_498_ = 48;
v___x_499_ = lean_uint32_sub(v_ch_495_, v___x_498_);
v___x_500_ = lean_uint32_to_nat(v___x_499_);
v___x_501_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_490_, v_p_496_, v_res_492_, v___x_500_);
return v___x_501_;
}
v___jp_502_:
{
if (v___y_503_ == 0)
{
goto v___jp_497_;
}
else
{
uint32_t v___x_504_; uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_504_ = lean_string_utf8_get_fast(v_s_490_, v_p_496_);
v___x_505_ = 48;
v___x_506_ = lean_uint32_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
goto v___jp_497_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_string_utf8_next_fast(v_s_490_, v_p_496_);
v___x_508_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_490_, v___x_507_, v_res_492_, v___x_508_, v___x_509_);
return v___x_510_;
}
}
}
v___jp_511_:
{
if (v___y_512_ == 0)
{
uint32_t v___x_513_; uint8_t v___x_514_; 
v___x_513_ = 95;
v___x_514_ = lean_uint32_dec_eq(v_ch_495_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_515_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_516_ = lean_string_push(v___x_515_, v_ch_495_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_490_, v_p_496_, v_res_492_, v___x_516_, v___x_517_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l_String_mangle___closed__0));
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_490_, v_p_496_, v_res_492_, v___x_519_, v___x_520_);
return v___x_521_;
}
}
else
{
uint32_t v___x_522_; uint8_t v___x_523_; 
v___x_522_ = 48;
v___x_523_ = lean_uint32_dec_eq(v_ch_495_, v___x_522_);
if (v___x_523_ == 0)
{
goto v___jp_497_;
}
else
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_eq(v_p_496_, v___x_493_);
if (v___x_524_ == 0)
{
v___y_503_ = v___x_523_;
goto v___jp_502_;
}
else
{
v___y_503_ = v___x_494_;
goto v___jp_502_;
}
}
}
}
}
else
{
return v_res_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(lean_object* v_s_529_, lean_object* v_p_530_, lean_object* v_res_531_, lean_object* v_n_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_string_utf8_byte_size(v_s_529_);
v___x_534_ = lean_nat_dec_eq(v_p_530_, v___x_533_);
if (v___x_534_ == 0)
{
uint32_t v_ch_535_; lean_object* v_p_536_; uint8_t v___y_538_; uint32_t v___x_550_; uint8_t v___x_551_; 
v_ch_535_ = lean_string_utf8_get_fast(v_s_529_, v_p_530_);
v_p_536_ = lean_string_utf8_next_fast(v_s_529_, v_p_530_);
lean_dec(v_p_530_);
v___x_550_ = 48;
v___x_551_ = lean_uint32_dec_le(v___x_550_, v_ch_535_);
if (v___x_551_ == 0)
{
v___y_538_ = v___x_551_;
goto v___jp_537_;
}
else
{
uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_552_ = 57;
v___x_553_ = lean_uint32_dec_le(v_ch_535_, v___x_552_);
v___y_538_ = v___x_553_;
goto v___jp_537_;
}
v___jp_537_:
{
if (v___y_538_ == 0)
{
lean_object* v_res_539_; uint8_t v___x_540_; 
v_res_539_ = l_Lean_Name_num___override(v_res_531_, v_n_532_);
v___x_540_ = lean_nat_dec_eq(v_p_536_, v___x_533_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_string_utf8_next_fast(v_s_529_, v_p_536_);
v___x_542_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_529_, v___x_541_, v_res_539_);
return v___x_542_;
}
else
{
return v_res_539_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; uint32_t v___x_545_; uint32_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_543_ = lean_unsigned_to_nat(10u);
v___x_544_ = lean_nat_mul(v_n_532_, v___x_543_);
lean_dec(v_n_532_);
v___x_545_ = 48;
v___x_546_ = lean_uint32_sub(v_ch_535_, v___x_545_);
v___x_547_ = lean_uint32_to_nat(v___x_546_);
v___x_548_ = lean_nat_add(v___x_544_, v___x_547_);
lean_dec(v___x_547_);
lean_dec(v___x_544_);
v_p_530_ = v_p_536_;
v_n_532_ = v___x_548_;
goto _start;
}
}
}
else
{
lean_object* v___x_554_; 
lean_dec(v_p_530_);
v___x_554_ = l_Lean_Name_num___override(v_res_531_, v_n_532_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(lean_object* v_s_555_, lean_object* v_p_556_, lean_object* v_res_557_, lean_object* v_n_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(v_s_555_, v_p_556_, v_res_557_, v_n_558_);
lean_dec_ref(v_s_555_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(lean_object* v_s_560_, lean_object* v_p_561_, lean_object* v_res_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_560_, v_p_561_, v_res_562_);
lean_dec(v_p_561_);
lean_dec_ref(v_s_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(lean_object* v_s_564_, lean_object* v_p_u2080_565_, lean_object* v_res_566_, lean_object* v_acc_567_, lean_object* v_ucount_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(v_s_564_, v_p_u2080_565_, v_res_566_, v_acc_567_, v_ucount_568_);
lean_dec_ref(v_s_564_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; 
v___x_570_ = 120;
v___x_571_ = lean_box_uint32(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(uint32_t v_ch_572_, lean_object* v_x_573_, lean_object* v_h__1_574_, lean_object* v_h__2_575_){
_start:
{
uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_576_ = 120;
v___x_577_ = lean_uint32_dec_eq(v_ch_572_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_h__1_574_);
v___x_578_ = lean_box_uint32(v_ch_572_);
v___x_579_ = lean_apply_4(v_h__2_575_, v___x_578_, v_x_573_, lean_box(0), lean_box(0));
return v___x_579_;
}
else
{
if (lean_obj_tag(v_x_573_) == 1)
{
lean_object* v_val_580_; lean_object* v_fst_581_; lean_object* v_snd_582_; lean_object* v___x_583_; 
lean_dec(v_h__2_575_);
v_val_580_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_val_580_);
lean_dec_ref(v_x_573_);
v_fst_581_ = lean_ctor_get(v_val_580_, 0);
lean_inc(v_fst_581_);
v_snd_582_ = lean_ctor_get(v_val_580_, 1);
lean_inc(v_snd_582_);
lean_dec(v_val_580_);
v___x_583_ = lean_apply_3(v_h__1_574_, v_fst_581_, v_snd_582_, lean_box(0));
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_h__1_574_);
v___x_584_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_585_ = lean_apply_4(v_h__2_575_, v___x_584_, v_x_573_, lean_box(0), lean_box(0));
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(lean_object* v_ch_586_, lean_object* v_x_587_, lean_object* v_h__1_588_, lean_object* v_h__2_589_){
_start:
{
uint32_t v_ch_81__boxed_590_; lean_object* v_res_591_; 
v_ch_81__boxed_590_ = lean_unbox_uint32(v_ch_586_);
lean_dec(v_ch_586_);
v_res_591_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(v_ch_81__boxed_590_, v_x_587_, v_h__1_588_, v_h__2_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(lean_object* v_s_592_, lean_object* v_motive_593_, uint32_t v_ch_594_, lean_object* v_x_595_, lean_object* v_h__1_596_, lean_object* v_h__2_597_){
_start:
{
uint32_t v___x_598_; uint8_t v___x_599_; 
v___x_598_ = 120;
v___x_599_ = lean_uint32_dec_eq(v_ch_594_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_h__1_596_);
v___x_600_ = lean_box_uint32(v_ch_594_);
v___x_601_ = lean_apply_4(v_h__2_597_, v___x_600_, v_x_595_, lean_box(0), lean_box(0));
return v___x_601_;
}
else
{
if (lean_obj_tag(v_x_595_) == 1)
{
lean_object* v_val_602_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_605_; 
lean_dec(v_h__2_597_);
v_val_602_ = lean_ctor_get(v_x_595_, 0);
lean_inc(v_val_602_);
lean_dec_ref(v_x_595_);
v_fst_603_ = lean_ctor_get(v_val_602_, 0);
lean_inc(v_fst_603_);
v_snd_604_ = lean_ctor_get(v_val_602_, 1);
lean_inc(v_snd_604_);
lean_dec(v_val_602_);
v___x_605_ = lean_apply_3(v_h__1_596_, v_fst_603_, v_snd_604_, lean_box(0));
return v___x_605_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_h__1_596_);
v___x_606_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
v___x_607_ = lean_apply_4(v_h__2_597_, v___x_606_, v_x_595_, lean_box(0), lean_box(0));
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(lean_object* v_s_608_, lean_object* v_motive_609_, lean_object* v_ch_610_, lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
uint32_t v_ch_111__boxed_614_; lean_object* v_res_615_; 
v_ch_111__boxed_614_ = lean_unbox_uint32(v_ch_610_);
lean_dec(v_ch_610_);
v_res_615_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(v_s_608_, v_motive_609_, v_ch_111__boxed_614_, v_x_611_, v_h__1_612_, v_h__2_613_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(uint32_t v_ch_618_, lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_){
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
lean_dec_ref(v_x_619_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(lean_object* v_ch_632_, lean_object* v_x_633_, lean_object* v_h__1_634_, lean_object* v_h__2_635_){
_start:
{
uint32_t v_ch_81__boxed_636_; lean_object* v_res_637_; 
v_ch_81__boxed_636_ = lean_unbox_uint32(v_ch_632_);
lean_dec(v_ch_632_);
v_res_637_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(v_ch_81__boxed_636_, v_x_633_, v_h__1_634_, v_h__2_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(lean_object* v_s_638_, lean_object* v_motive_639_, uint32_t v_ch_640_, lean_object* v_x_641_, lean_object* v_h__1_642_, lean_object* v_h__2_643_){
_start:
{
uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_644_ = 117;
v___x_645_ = lean_uint32_dec_eq(v_ch_640_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_h__1_642_);
v___x_646_ = lean_box_uint32(v_ch_640_);
v___x_647_ = lean_apply_4(v_h__2_643_, v___x_646_, v_x_641_, lean_box(0), lean_box(0));
return v___x_647_;
}
else
{
if (lean_obj_tag(v_x_641_) == 1)
{
lean_object* v_val_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; lean_object* v___x_651_; 
lean_dec(v_h__2_643_);
v_val_648_ = lean_ctor_get(v_x_641_, 0);
lean_inc(v_val_648_);
lean_dec_ref(v_x_641_);
v_fst_649_ = lean_ctor_get(v_val_648_, 0);
lean_inc(v_fst_649_);
v_snd_650_ = lean_ctor_get(v_val_648_, 1);
lean_inc(v_snd_650_);
lean_dec(v_val_648_);
v___x_651_ = lean_apply_3(v_h__1_642_, v_fst_649_, v_snd_650_, lean_box(0));
return v___x_651_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_h__1_642_);
v___x_652_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
v___x_653_ = lean_apply_4(v_h__2_643_, v___x_652_, v_x_641_, lean_box(0), lean_box(0));
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(lean_object* v_s_654_, lean_object* v_motive_655_, lean_object* v_ch_656_, lean_object* v_x_657_, lean_object* v_h__1_658_, lean_object* v_h__2_659_){
_start:
{
uint32_t v_ch_111__boxed_660_; lean_object* v_res_661_; 
v_ch_111__boxed_660_ = lean_unbox_uint32(v_ch_656_);
lean_dec(v_ch_656_);
v_res_661_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(v_s_654_, v_motive_655_, v_ch_111__boxed_660_, v_x_657_, v_h__1_658_, v_h__2_659_);
lean_dec_ref(v_s_654_);
return v_res_661_;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_662_; lean_object* v___x_663_; 
v___x_662_ = 85;
v___x_663_ = lean_box_uint32(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(uint32_t v_ch_664_, lean_object* v_x_665_, lean_object* v_h__1_666_, lean_object* v_h__2_667_){
_start:
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 85;
v___x_669_ = lean_uint32_dec_eq(v_ch_664_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_h__1_666_);
v___x_670_ = lean_box_uint32(v_ch_664_);
v___x_671_ = lean_apply_4(v_h__2_667_, v___x_670_, v_x_665_, lean_box(0), lean_box(0));
return v___x_671_;
}
else
{
if (lean_obj_tag(v_x_665_) == 1)
{
lean_object* v_val_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_675_; 
lean_dec(v_h__2_667_);
v_val_672_ = lean_ctor_get(v_x_665_, 0);
lean_inc(v_val_672_);
lean_dec_ref(v_x_665_);
v_fst_673_ = lean_ctor_get(v_val_672_, 0);
lean_inc(v_fst_673_);
v_snd_674_ = lean_ctor_get(v_val_672_, 1);
lean_inc(v_snd_674_);
lean_dec(v_val_672_);
v___x_675_ = lean_apply_3(v_h__1_666_, v_fst_673_, v_snd_674_, lean_box(0));
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_h__1_666_);
v___x_676_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_677_ = lean_apply_4(v_h__2_667_, v___x_676_, v_x_665_, lean_box(0), lean_box(0));
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(lean_object* v_ch_678_, lean_object* v_x_679_, lean_object* v_h__1_680_, lean_object* v_h__2_681_){
_start:
{
uint32_t v_ch_81__boxed_682_; lean_object* v_res_683_; 
v_ch_81__boxed_682_ = lean_unbox_uint32(v_ch_678_);
lean_dec(v_ch_678_);
v_res_683_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(v_ch_81__boxed_682_, v_x_679_, v_h__1_680_, v_h__2_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(lean_object* v_s_684_, lean_object* v_motive_685_, uint32_t v_ch_686_, lean_object* v_x_687_, lean_object* v_h__1_688_, lean_object* v_h__2_689_){
_start:
{
uint32_t v___x_690_; uint8_t v___x_691_; 
v___x_690_ = 85;
v___x_691_ = lean_uint32_dec_eq(v_ch_686_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_h__1_688_);
v___x_692_ = lean_box_uint32(v_ch_686_);
v___x_693_ = lean_apply_4(v_h__2_689_, v___x_692_, v_x_687_, lean_box(0), lean_box(0));
return v___x_693_;
}
else
{
if (lean_obj_tag(v_x_687_) == 1)
{
lean_object* v_val_694_; lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_697_; 
lean_dec(v_h__2_689_);
v_val_694_ = lean_ctor_get(v_x_687_, 0);
lean_inc(v_val_694_);
lean_dec_ref(v_x_687_);
v_fst_695_ = lean_ctor_get(v_val_694_, 0);
lean_inc(v_fst_695_);
v_snd_696_ = lean_ctor_get(v_val_694_, 1);
lean_inc(v_snd_696_);
lean_dec(v_val_694_);
v___x_697_ = lean_apply_3(v_h__1_688_, v_fst_695_, v_snd_696_, lean_box(0));
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v_h__1_688_);
v___x_698_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
v___x_699_ = lean_apply_4(v_h__2_689_, v___x_698_, v_x_687_, lean_box(0), lean_box(0));
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(lean_object* v_s_700_, lean_object* v_motive_701_, lean_object* v_ch_702_, lean_object* v_x_703_, lean_object* v_h__1_704_, lean_object* v_h__2_705_){
_start:
{
uint32_t v_ch_111__boxed_706_; lean_object* v_res_707_; 
v_ch_111__boxed_706_ = lean_unbox_uint32(v_ch_702_);
lean_dec(v_ch_702_);
v_res_707_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(v_s_700_, v_motive_701_, v_ch_111__boxed_706_, v_x_703_, v_h__1_704_, v_h__2_705_);
lean_dec_ref(v_s_700_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle(lean_object* v_s_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_box(0);
v___x_711_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle___boxed(lean_object* v_s_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Name_demangle(v_s_712_);
lean_dec_ref(v_s_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f(lean_object* v_s_714_){
_start:
{
lean_object* v_n_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_n_715_ = l_Lean_Name_demangle(v_s_714_);
lean_inc(v_n_715_);
v___x_716_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_715_);
v___x_717_ = lean_string_dec_eq(v___x_716_, v_s_714_);
lean_dec_ref(v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v_n_715_);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_n_715_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_demangle_x3f___boxed(lean_object* v_s_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Name_demangle_x3f(v_s_720_);
lean_dec_ref(v_s_720_);
return v_res_721_;
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
