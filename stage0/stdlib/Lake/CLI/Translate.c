// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: public import Lake.Config.Lang public import Lake.Config.Package import Lean.PrettyPrinter import Lake.CLI.Translate.Toml import Lake.CLI.Translate.Lean import Lake.Load.Lean.Elab
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint16_t lean_uint16_land(uint16_t, uint16_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t);
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
lean_object* l_Lake_Toml_ppTable(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_mkConfigString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "(internal) failed to pretty print Lean configuration: "};
static const lean_object* l_Lake_Package_mkConfigString___closed__0 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__0_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Package_mkConfigString___closed__1 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__1_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkConfigString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__2 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__2_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_mkConfigString___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__3 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__3_value;
static const lean_array_object l_Lake_Package_mkConfigString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_Package_mkConfigString___closed__3_value)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__4 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__4_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Package_mkConfigString___closed__5 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__5_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__6;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lake_Package_mkConfigString___closed__7;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__8;
static const lean_string_object l_Lake_Package_mkConfigString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Package_mkConfigString___closed__9 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__9_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkConfigString___closed__9_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__10 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__10_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_mkConfigString___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__11 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__11_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__12 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__12_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__13;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__14;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__15;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__16;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__17;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__18;
static const lean_array_object l_Lake_Package_mkConfigString___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_mkConfigString___closed__19 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__19_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__20;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__21;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__22;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__23;
static const lean_string_object l_Lake_Package_mkConfigString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_Package_mkConfigString___closed__24 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__24_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lake_Package_mkConfigString___closed__25 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__25_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lake_Package_mkConfigString___closed__26 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__26_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lake_Package_mkConfigString___closed__27 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__27_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lake_Package_mkConfigString___closed__28;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Package_mkConfigString___closed__29;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__30;
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_usize_dec_lt(v_i_2_, v_sz_1_);
if (v___x_4_ == 0)
{
return v_bs_3_;
}
else
{
lean_object* v_v_5_; lean_object* v___x_6_; lean_object* v_bs_x27_7_; lean_object* v___x_8_; size_t v___x_9_; size_t v___x_10_; lean_object* v___x_11_; 
v_v_5_ = lean_array_uget(v_bs_3_, v_i_2_);
v___x_6_ = lean_unsigned_to_nat(0u);
v_bs_x27_7_ = lean_array_uset(v_bs_3_, v_i_2_, v___x_6_);
v___x_8_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_v_5_);
v___x_9_ = ((size_t)1ULL);
v___x_10_ = lean_usize_add(v_i_2_, v___x_9_);
v___x_11_ = lean_array_uset(v_bs_x27_7_, v_i_2_, v___x_8_);
v_i_2_ = v___x_10_;
v_bs_3_ = v___x_11_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object* v_x_13_){
_start:
{
switch(lean_obj_tag(v_x_13_))
{
case 3:
{
lean_object* v_info_14_; lean_object* v_rawVal_15_; lean_object* v_val_16_; lean_object* v_preresolved_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_info_14_ = lean_ctor_get(v_x_13_, 0);
v_rawVal_15_ = lean_ctor_get(v_x_13_, 1);
v_val_16_ = lean_ctor_get(v_x_13_, 2);
v_preresolved_17_ = lean_ctor_get(v_x_13_, 3);
v_isSharedCheck_25_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_25_ == 0)
{
v___x_19_ = v_x_13_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_preresolved_17_);
lean_inc(v_val_16_);
lean_inc(v_rawVal_15_);
lean_inc(v_info_14_);
lean_dec(v_x_13_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = l_Lean_Name_eraseMacroScopes(v_val_16_);
lean_dec(v_val_16_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v___x_21_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_info_14_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_rawVal_15_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_24_, 3, v_preresolved_17_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
case 1:
{
lean_object* v_info_26_; lean_object* v_kind_27_; lean_object* v_args_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_info_26_ = lean_ctor_get(v_x_13_, 0);
v_kind_27_ = lean_ctor_get(v_x_13_, 1);
v_args_28_ = lean_ctor_get(v_x_13_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v_x_13_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_args_28_);
lean_inc(v_kind_27_);
lean_inc(v_info_26_);
lean_dec(v_x_13_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
size_t v_sz_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v_sz_32_ = lean_array_size(v_args_28_);
v___x_33_ = ((size_t)0ULL);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_32_, v___x_33_, v_args_28_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 2, v___x_34_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_info_26_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_kind_27_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
default: 
{
return v_x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object* v_sz_39_, lean_object* v_i_40_, lean_object* v_bs_41_){
_start:
{
size_t v_sz_boxed_42_; size_t v_i_boxed_43_; lean_object* v_res_44_; 
v_sz_boxed_42_ = lean_unbox_usize(v_sz_39_);
lean_dec(v_sz_39_);
v_i_boxed_43_ = lean_unbox_usize(v_i_40_);
lean_dec(v_i_40_);
v_res_44_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_boxed_42_, v_i_boxed_43_, v_bs_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object* v_stx_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object* v_k_47_, lean_object* v_stx_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object* v_k_50_, lean_object* v_stx_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(v_k_50_, v_stx_51_);
lean_dec(v_k_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(lean_object* v_opts_53_, lean_object* v_opt_54_){
_start:
{
lean_object* v_name_55_; lean_object* v_defValue_56_; lean_object* v_map_57_; lean_object* v___x_58_; 
v_name_55_ = lean_ctor_get(v_opt_54_, 0);
v_defValue_56_ = lean_ctor_get(v_opt_54_, 1);
v_map_57_ = lean_ctor_get(v_opts_53_, 0);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_57_, v_name_55_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_inc(v_defValue_56_);
return v_defValue_56_;
}
else
{
lean_object* v_val_59_; 
v_val_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v___x_58_, 1);
if (lean_obj_tag(v_val_59_) == 3)
{
lean_object* v_v_60_; 
v_v_60_ = lean_ctor_get(v_val_59_, 0);
lean_inc(v_v_60_);
lean_dec_ref_known(v_val_59_, 1);
return v_v_60_;
}
else
{
lean_dec(v_val_59_);
lean_inc(v_defValue_56_);
return v_defValue_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(lean_object* v_opts_61_, lean_object* v_opt_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v_opts_61_, v_opt_62_);
lean_dec_ref(v_opt_62_);
lean_dec_ref(v_opts_61_);
return v_res_63_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = l_Lean_Options_empty;
v___x_78_ = l_Lean_Core_getMaxHeartbeats(v___x_77_);
return v___x_78_;
}
}
static uint16_t _init_l_Lake_Package_mkConfigString___closed__7(void){
_start:
{
lean_object* v___x_79_; uint16_t v___x_80_; 
v___x_79_ = l_Lean_Options_empty;
v___x_80_ = l_Lean_OptionFlags_ofOptions(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = l_Lean_firstFrontendMacroScope;
v___x_83_ = lean_nat_add(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__13(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__14(void){
_start:
{
size_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_97_ = ((size_t)5ULL);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_unsigned_to_nat(32u);
v___x_100_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_101_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__13, &l_Lake_Package_mkConfigString___closed__13_once, _init_l_Lake_Package_mkConfigString___closed__13);
v___x_102_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_98_);
lean_ctor_set(v___x_102_, 3, v___x_98_);
lean_ctor_set_usize(v___x_102_, 4, v___x_97_);
return v___x_102_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__15(void){
_start:
{
lean_object* v___x_103_; uint64_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_104_ = 0ULL;
v___x_105_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set_uint64(v___x_105_, sizeof(void*)*1, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_106_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__16, &l_Lake_Package_mkConfigString___closed__16_once, _init_l_Lake_Package_mkConfigString___closed__16);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__18(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l_Lean_Options_empty;
v___x_115_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__19));
v___x_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
lean_ctor_set(v___x_116_, 3, v___x_113_);
return v___x_116_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__21(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = l_Lean_NameSet_empty;
v___x_118_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
lean_ctor_set(v___x_119_, 2, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__22(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_121_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_122_ = 1;
v___x_123_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*3, v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__23(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l_Lean_maxRecDepth;
v___x_125_ = l_Lean_Options_empty;
v___x_126_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v___x_125_, v___x_124_);
return v___x_126_;
}
}
static uint16_t _init_l_Lake_Package_mkConfigString___closed__28(void){
_start:
{
uint16_t v___x_131_; uint16_t v___x_132_; uint16_t v___x_133_; 
v___x_131_ = 512;
v___x_132_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_133_ = lean_uint16_land(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static uint8_t _init_l_Lake_Package_mkConfigString___closed__29(void){
_start:
{
uint16_t v___x_134_; uint16_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = 0;
v___x_135_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__28, &l_Lake_Package_mkConfigString___closed__28_once, _init_l_Lake_Package_mkConfigString___closed__28);
v___x_136_ = lean_uint16_dec_eq(v___x_135_, v___x_134_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__30(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* v_pkg_138_, uint8_t v_lang_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_a_143_; lean_object* v_a_153_; 
if (v_lang_139_ == 0)
{
uint8_t v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; 
v___x_155_ = 0;
v___x_156_ = 1;
v___x_157_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__4));
v___x_158_ = l_Lean_Options_empty;
v___x_159_ = 1024;
v___x_160_ = l_Lake_importModulesUsingCache(v___x_157_, v___x_158_, v___x_159_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint16_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currNamespace_189_; lean_object* v_openDecls_190_; lean_object* v_initHeartbeats_191_; lean_object* v_maxHeartbeats_192_; lean_object* v_quotContext_193_; lean_object* v_currMacroScope_194_; lean_object* v_cancelTk_x3f_195_; lean_object* v_inheritedTraceOptions_196_; lean_object* v_currRecDepth_197_; lean_object* v_ref_198_; uint8_t v_suppressElabErrors_199_; uint8_t v_isRecordingDeps_200_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___y_238_; lean_object* v_env_259_; uint8_t v___x_260_; uint8_t v___x_261_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = l_Lake_Package_mkLeanConfig(v_pkg_138_);
v___x_163_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v___x_162_);
v___x_164_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__5));
v___x_165_ = l_Lean_instInhabitedFileMap_default;
v___x_166_ = lean_box(0);
v___x_167_ = lean_box(0);
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_170_ = l_Lean_firstFrontendMacroScope;
v___x_171_ = lean_box(0);
v___x_172_ = lean_box(0);
v___x_173_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_174_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__8, &l_Lake_Package_mkConfigString___closed__8_once, _init_l_Lake_Package_mkConfigString___closed__8);
v___x_175_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__11));
v___x_176_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__12));
v___x_177_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__15, &l_Lake_Package_mkConfigString___closed__15_once, _init_l_Lake_Package_mkConfigString___closed__15);
v___x_178_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__18, &l_Lake_Package_mkConfigString___closed__18_once, _init_l_Lake_Package_mkConfigString___closed__18);
v___x_179_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__19));
v___x_180_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__20, &l_Lake_Package_mkConfigString___closed__20_once, _init_l_Lake_Package_mkConfigString___closed__20);
v___x_181_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__21, &l_Lake_Package_mkConfigString___closed__21_once, _init_l_Lake_Package_mkConfigString___closed__21);
v___x_182_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__22, &l_Lake_Package_mkConfigString___closed__22_once, _init_l_Lake_Package_mkConfigString___closed__22);
v___x_183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_183_, 0, v_a_161_);
lean_ctor_set(v___x_183_, 1, v___x_174_);
lean_ctor_set(v___x_183_, 2, v___x_175_);
lean_ctor_set(v___x_183_, 3, v___x_176_);
lean_ctor_set(v___x_183_, 4, v___x_177_);
lean_ctor_set(v___x_183_, 5, v___x_178_);
lean_ctor_set(v___x_183_, 6, v___x_180_);
lean_ctor_set(v___x_183_, 7, v___x_181_);
lean_ctor_set(v___x_183_, 8, v___x_182_);
lean_ctor_set(v___x_183_, 9, v___x_179_);
v___x_184_ = lean_io_get_num_heartbeats();
v___x_185_ = lean_st_mk_ref(v___x_183_);
v___x_234_ = l_Lean_inheritedTraceOptions;
v___x_235_ = lean_st_ref_get(v___x_234_);
v___x_236_ = lean_st_ref_get(v___x_185_);
v_env_259_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_259_);
lean_dec(v___x_236_);
v___x_260_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_259_);
lean_dec_ref(v_env_259_);
v___x_261_ = lean_uint8_once(&l_Lake_Package_mkConfigString___closed__29, &l_Lake_Package_mkConfigString___closed__29_once, _init_l_Lake_Package_mkConfigString___closed__29);
if (v___x_261_ == 0)
{
if (v___x_260_ == 0)
{
v___y_238_ = v___x_156_;
goto v___jp_237_;
}
else
{
v_fileName_187_ = v___x_164_;
v_fileMap_188_ = v___x_165_;
v_currNamespace_189_ = v___x_166_;
v_openDecls_190_ = v___x_167_;
v_initHeartbeats_191_ = v___x_184_;
v_maxHeartbeats_192_ = v___x_169_;
v_quotContext_193_ = v___x_166_;
v_currMacroScope_194_ = v___x_170_;
v_cancelTk_x3f_195_ = v___x_171_;
v_inheritedTraceOptions_196_ = v___x_235_;
v_currRecDepth_197_ = v___x_168_;
v_ref_198_ = v___x_172_;
v_suppressElabErrors_199_ = v___x_155_;
v_isRecordingDeps_200_ = v___x_155_;
goto v___jp_186_;
}
}
else
{
if (v___x_260_ == 0)
{
v_fileName_187_ = v___x_164_;
v_fileMap_188_ = v___x_165_;
v_currNamespace_189_ = v___x_166_;
v_openDecls_190_ = v___x_167_;
v_initHeartbeats_191_ = v___x_184_;
v_maxHeartbeats_192_ = v___x_169_;
v_quotContext_193_ = v___x_166_;
v_currMacroScope_194_ = v___x_170_;
v_cancelTk_x3f_195_ = v___x_171_;
v_inheritedTraceOptions_196_ = v___x_235_;
v_currRecDepth_197_ = v___x_168_;
v_ref_198_ = v___x_172_;
v_suppressElabErrors_199_ = v___x_155_;
v_isRecordingDeps_200_ = v___x_155_;
goto v___jp_186_;
}
else
{
v___y_238_ = v___x_155_;
goto v___jp_237_;
}
}
v___jp_186_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_201_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__23, &l_Lake_Package_mkConfigString___closed__23_once, _init_l_Lake_Package_mkConfigString___closed__23);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_currMacroScope_194_);
lean_inc(v_quotContext_193_);
lean_inc(v_maxHeartbeats_192_);
lean_inc(v_openDecls_190_);
lean_inc(v_currNamespace_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_202_, 0, v_fileName_187_);
lean_ctor_set(v___x_202_, 1, v_fileMap_188_);
lean_ctor_set(v___x_202_, 2, v___x_158_);
lean_ctor_set(v___x_202_, 3, v___x_201_);
lean_ctor_set(v___x_202_, 4, v_currNamespace_189_);
lean_ctor_set(v___x_202_, 5, v_openDecls_190_);
lean_ctor_set(v___x_202_, 6, v_initHeartbeats_191_);
lean_ctor_set(v___x_202_, 7, v_maxHeartbeats_192_);
lean_ctor_set(v___x_202_, 8, v_quotContext_193_);
lean_ctor_set(v___x_202_, 9, v_currMacroScope_194_);
lean_ctor_set(v___x_202_, 10, v_cancelTk_x3f_195_);
lean_ctor_set(v___x_202_, 11, v_inheritedTraceOptions_196_);
lean_inc(v_ref_198_);
v___x_203_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_currRecDepth_197_);
lean_ctor_set(v___x_203_, 2, v_ref_198_);
lean_ctor_set_uint16(v___x_203_, sizeof(void*)*3, v___x_173_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3 + 2, v_suppressElabErrors_199_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3 + 3, v_isRecordingDeps_200_);
v___x_204_ = l_Lean_PrettyPrinter_ppModule(v___x_163_, v___x_203_, v___x_185_);
lean_dec_ref_known(v___x_203_, 3);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_str_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_204_, 1);
v___x_206_ = lean_st_ref_get(v___x_185_);
lean_dec(v___x_185_);
lean_dec(v___x_206_);
v___x_207_ = l_Std_Format_defWidth;
v___x_208_ = l_Std_Format_pretty(v_a_205_, v___x_207_, v___x_168_, v___x_168_);
v___x_209_ = lean_string_utf8_byte_size(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_168_);
lean_ctor_set(v___x_210_, 2, v___x_209_);
v___x_211_ = l_String_Slice_trimAscii(v___x_210_);
v_str_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_str_212_);
v_startInclusive_213_ = lean_ctor_get(v___x_211_, 1);
lean_inc(v_startInclusive_213_);
v_endExclusive_214_ = lean_ctor_get(v___x_211_, 2);
lean_inc(v_endExclusive_214_);
lean_dec_ref(v___x_211_);
v___x_215_ = lean_string_utf8_extract_fast(v_str_212_, v_startInclusive_213_, v_endExclusive_214_);
lean_dec(v_endExclusive_214_);
lean_dec(v_startInclusive_213_);
lean_dec_ref(v_str_212_);
v___x_216_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__24));
v___x_217_ = lean_string_append(v___x_215_, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v_a_140_);
return v___x_218_;
}
else
{
lean_object* v_a_219_; 
lean_dec(v___x_185_);
v_a_219_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_204_, 1);
if (lean_obj_tag(v_a_219_) == 0)
{
lean_object* v_msg_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_msg_220_ = lean_ctor_get(v_a_219_, 1);
lean_inc_ref(v_msg_220_);
lean_dec_ref_known(v_a_219_, 2);
v___x_221_ = l_Lean_MessageData_toString(v_msg_220_);
v___x_222_ = lean_mk_io_user_error(v___x_221_);
v_a_143_ = v___x_222_;
goto v___jp_142_;
}
else
{
lean_object* v_id_223_; lean_object* v___x_224_; 
v_id_223_ = lean_ctor_get(v_a_219_, 0);
lean_inc(v_id_223_);
lean_dec_ref_known(v_a_219_, 2);
v___x_224_ = l_Lean_InternalExceptionId_getName(v_id_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_id_223_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__25));
v___x_227_ = l_Lean_Name_toString(v_a_225_, v___x_156_);
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
lean_dec_ref(v___x_227_);
v_a_153_ = v___x_228_;
goto v___jp_152_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref_known(v___x_224_, 1);
v___x_229_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__26));
v___x_230_ = l_Nat_reprFast(v_id_223_);
v___x_231_ = lean_string_append(v___x_229_, v___x_230_);
lean_dec_ref(v___x_230_);
v___x_232_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__27));
v___x_233_ = lean_string_append(v___x_231_, v___x_232_);
v_a_153_ = v___x_233_;
goto v___jp_152_;
}
}
}
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v_env_240_; lean_object* v_nextMacroScope_241_; lean_object* v_ngen_242_; lean_object* v_auxDeclNGen_243_; lean_object* v_traceState_244_; lean_object* v_recordedDeps_245_; lean_object* v_messages_246_; lean_object* v_infoState_247_; lean_object* v_snapshotTasks_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v___x_239_ = lean_st_ref_take(v___x_185_);
v_env_240_ = lean_ctor_get(v___x_239_, 0);
v_nextMacroScope_241_ = lean_ctor_get(v___x_239_, 1);
v_ngen_242_ = lean_ctor_get(v___x_239_, 2);
v_auxDeclNGen_243_ = lean_ctor_get(v___x_239_, 3);
v_traceState_244_ = lean_ctor_get(v___x_239_, 4);
v_recordedDeps_245_ = lean_ctor_get(v___x_239_, 6);
v_messages_246_ = lean_ctor_get(v___x_239_, 7);
v_infoState_247_ = lean_ctor_get(v___x_239_, 8);
v_snapshotTasks_248_ = lean_ctor_get(v___x_239_, 9);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_239_, 5);
lean_dec(v_unused_258_);
v___x_250_ = v___x_239_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snapshotTasks_248_);
lean_inc(v_infoState_247_);
lean_inc(v_messages_246_);
lean_inc(v_recordedDeps_245_);
lean_inc(v_traceState_244_);
lean_inc(v_auxDeclNGen_243_);
lean_inc(v_ngen_242_);
lean_inc(v_nextMacroScope_241_);
lean_inc(v_env_240_);
lean_dec(v___x_239_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = l_Lean_Kernel_enableDiag(v_env_240_, v___y_238_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 5, v___x_178_);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_nextMacroScope_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_ngen_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_auxDeclNGen_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_traceState_244_);
lean_ctor_set(v_reuseFailAlloc_256_, 5, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_256_, 6, v_recordedDeps_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 7, v_messages_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 8, v_infoState_247_);
lean_ctor_set(v_reuseFailAlloc_256_, 9, v_snapshotTasks_248_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; 
v___x_255_ = lean_st_ref_put(v___x_185_, v___x_254_);
v_fileName_187_ = v___x_164_;
v_fileMap_188_ = v___x_165_;
v_currNamespace_189_ = v___x_166_;
v_openDecls_190_ = v___x_167_;
v_initHeartbeats_191_ = v___x_184_;
v_maxHeartbeats_192_ = v___x_169_;
v_quotContext_193_ = v___x_166_;
v_currMacroScope_194_ = v___x_170_;
v_cancelTk_x3f_195_ = v___x_171_;
v_inheritedTraceOptions_196_ = v___x_235_;
v_currRecDepth_197_ = v___x_168_;
v_ref_198_ = v___x_172_;
v_suppressElabErrors_199_ = v___x_155_;
v_isRecordingDeps_200_ = v___x_155_;
goto v___jp_186_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_pkg_138_);
v_a_262_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_160_, 1);
v___x_263_ = lean_io_error_to_string(v_a_262_);
v___x_264_ = 3;
v___x_265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = lean_array_get_size(v_a_140_);
v___x_267_ = lean_array_push(v_a_140_, v___x_265_);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
return v___x_268_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__30, &l_Lake_Package_mkConfigString___closed__30_once, _init_l_Lake_Package_mkConfigString___closed__30);
v___x_270_ = l_Lake_Package_mkTomlConfig(v_pkg_138_, v___x_269_);
v___x_271_ = l_Lake_Toml_ppTable(v___x_270_);
lean_dec_ref(v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_a_140_);
return v___x_272_;
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_144_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__0));
v___x_145_ = lean_io_error_to_string(v_a_143_);
v___x_146_ = lean_string_append(v___x_144_, v___x_145_);
lean_dec_ref(v___x_145_);
v___x_147_ = 3;
v___x_148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
v___x_149_ = lean_array_get_size(v_a_140_);
v___x_150_ = lean_array_push(v_a_140_, v___x_148_);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
v___jp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_mk_io_user_error(v_a_153_);
v_a_143_ = v___x_154_;
goto v___jp_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* v_pkg_273_, lean_object* v_lang_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
uint8_t v_lang_boxed_277_; lean_object* v_res_278_; 
v_lang_boxed_277_ = lean_unbox(v_lang_274_);
v_res_278_ = l_Lake_Package_mkConfigString(v_pkg_273_, v_lang_boxed_277_, v_a_275_);
return v_res_278_;
}
}
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lake_CLI_Translate_Toml(uint8_t builtin);
lean_object* runtime_initialize_Lake_CLI_Translate_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Translate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Translate_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Translate_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_CLI_Translate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Toml(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_CLI_Translate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_CLI_Translate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_CLI_Translate(builtin);
}
#ifdef __cplusplus
}
#endif
