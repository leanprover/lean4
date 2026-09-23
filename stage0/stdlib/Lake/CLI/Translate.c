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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t);
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
lean_object* l_Lake_Toml_ppTable(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1___boxed(lean_object*, lean_object*);
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
static lean_object* l_Lake_Package_mkConfigString___closed__7;
static const lean_string_object l_Lake_Package_mkConfigString___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Package_mkConfigString___closed__8 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__8_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkConfigString___closed__8_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__9 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__9_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_mkConfigString___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__10 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__10_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__11 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__11_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__12;
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
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__19;
static const lean_array_object l_Lake_Package_mkConfigString___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_mkConfigString___closed__20 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__20_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Package_mkConfigString___closed__21;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__22;
static const lean_string_object l_Lake_Package_mkConfigString___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_Package_mkConfigString___closed__23 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__23_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lake_Package_mkConfigString___closed__24 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__24_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lake_Package_mkConfigString___closed__25 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__25_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lake_Package_mkConfigString___closed__26 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__26_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__27;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(lean_object* v_opts_53_, lean_object* v_opt_54_){
_start:
{
lean_object* v_name_55_; lean_object* v_defValue_56_; lean_object* v_map_57_; lean_object* v___x_58_; 
v_name_55_ = lean_ctor_get(v_opt_54_, 0);
v_defValue_56_ = lean_ctor_get(v_opt_54_, 1);
v_map_57_ = lean_ctor_get(v_opts_53_, 0);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_57_, v_name_55_);
if (lean_obj_tag(v___x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = lean_unbox(v_defValue_56_);
return v___x_59_;
}
else
{
lean_object* v_val_60_; 
v_val_60_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v___x_58_, 1);
if (lean_obj_tag(v_val_60_) == 1)
{
uint8_t v_v_61_; 
v_v_61_ = lean_ctor_get_uint8(v_val_60_, 0);
lean_dec_ref_known(v_val_60_, 0);
return v_v_61_;
}
else
{
uint8_t v___x_62_; 
lean_dec(v_val_60_);
v___x_62_ = lean_unbox(v_defValue_56_);
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(lean_object* v_opts_63_, lean_object* v_opt_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v_opts_63_, v_opt_64_);
lean_dec_ref(v_opt_64_);
lean_dec_ref(v_opts_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
lean_object* v_name_69_; lean_object* v_defValue_70_; lean_object* v_map_71_; lean_object* v___x_72_; 
v_name_69_ = lean_ctor_get(v_opt_68_, 0);
v_defValue_70_ = lean_ctor_get(v_opt_68_, 1);
v_map_71_ = lean_ctor_get(v_opts_67_, 0);
v___x_72_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_71_, v_name_69_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_inc(v_defValue_70_);
return v_defValue_70_;
}
else
{
lean_object* v_val_73_; 
v_val_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_73_);
lean_dec_ref_known(v___x_72_, 1);
if (lean_obj_tag(v_val_73_) == 3)
{
lean_object* v_v_74_; 
v_v_74_ = lean_ctor_get(v_val_73_, 0);
lean_inc(v_v_74_);
lean_dec_ref_known(v_val_73_, 1);
return v_v_74_;
}
else
{
lean_dec(v_val_73_);
lean_inc(v_defValue_70_);
return v_defValue_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1___boxed(lean_object* v_opts_75_, lean_object* v_opt_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(v_opts_75_, v_opt_76_);
lean_dec_ref(v_opt_76_);
lean_dec_ref(v_opts_75_);
return v_res_77_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = l_Lean_Options_empty;
v___x_92_ = l_Lean_Core_getMaxHeartbeats(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__7(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = l_Lean_firstFrontendMacroScope;
v___x_95_ = lean_nat_add(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__12(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(32u);
v___x_107_ = lean_mk_empty_array_with_capacity(v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__13(void){
_start:
{
size_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_109_ = ((size_t)5ULL);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_unsigned_to_nat(32u);
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_111_);
v___x_113_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__12, &l_Lake_Package_mkConfigString___closed__12_once, _init_l_Lake_Package_mkConfigString___closed__12);
v___x_114_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_110_);
lean_ctor_set(v___x_114_, 3, v___x_110_);
lean_ctor_set_usize(v___x_114_, 4, v___x_109_);
return v___x_114_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__14(void){
_start:
{
lean_object* v___x_115_; uint64_t v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__13, &l_Lake_Package_mkConfigString___closed__13_once, _init_l_Lake_Package_mkConfigString___closed__13);
v___x_116_ = 0ULL;
v___x_117_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint64(v___x_117_, sizeof(void*)*1, v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__15(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_118_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__15, &l_Lake_Package_mkConfigString___closed__15_once, _init_l_Lake_Package_mkConfigString___closed__15);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__16, &l_Lake_Package_mkConfigString___closed__16_once, _init_l_Lake_Package_mkConfigString___closed__16);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__18(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = l_Lean_NameSet_empty;
v___x_124_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__13, &l_Lake_Package_mkConfigString___closed__13_once, _init_l_Lake_Package_mkConfigString___closed__13);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
lean_ctor_set(v___x_125_, 2, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__19(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__13, &l_Lake_Package_mkConfigString___closed__13_once, _init_l_Lake_Package_mkConfigString___closed__13);
v___x_127_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__16, &l_Lake_Package_mkConfigString___closed__16_once, _init_l_Lake_Package_mkConfigString___closed__16);
v___x_128_ = 1;
v___x_129_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3, v___x_128_);
return v___x_129_;
}
}
static uint8_t _init_l_Lake_Package_mkConfigString___closed__21(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = l_Lean_diagnostics;
v___x_133_ = l_Lean_Options_empty;
v___x_134_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__22(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = l_Lean_maxRecDepth;
v___x_136_ = l_Lean_Options_empty;
v___x_137_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__1(v___x_136_, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__27(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* v_pkg_143_, uint8_t v_lang_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_a_148_; lean_object* v_a_158_; 
if (v_lang_144_ == 0)
{
uint8_t v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint32_t v___x_164_; lean_object* v___x_165_; 
v___x_160_ = 0;
v___x_161_ = 1;
v___x_162_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__4));
v___x_163_ = l_Lean_Options_empty;
v___x_164_ = 1024;
v___x_165_ = l_Lake_importModulesUsingCache(v___x_162_, v___x_163_, v___x_164_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___y_193_; lean_object* v___x_227_; uint8_t v___y_229_; lean_object* v_env_249_; uint8_t v___x_250_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
v___x_167_ = l_Lake_Package_mkLeanConfig(v_pkg_143_);
v___x_168_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v___x_167_);
v___x_169_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__5));
v___x_170_ = l_Lean_instInhabitedFileMap_default;
v___x_171_ = lean_box(0);
v___x_172_ = lean_box(0);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_175_ = l_Lean_firstFrontendMacroScope;
v___x_176_ = lean_box(0);
v___x_177_ = lean_box(0);
v___x_178_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_179_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__10));
v___x_180_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__11));
v___x_181_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_182_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_183_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__18, &l_Lake_Package_mkConfigString___closed__18_once, _init_l_Lake_Package_mkConfigString___closed__18);
v___x_184_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__19, &l_Lake_Package_mkConfigString___closed__19_once, _init_l_Lake_Package_mkConfigString___closed__19);
v___x_185_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__20));
v___x_186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_186_, 0, v_a_166_);
lean_ctor_set(v___x_186_, 1, v___x_178_);
lean_ctor_set(v___x_186_, 2, v___x_179_);
lean_ctor_set(v___x_186_, 3, v___x_180_);
lean_ctor_set(v___x_186_, 4, v___x_181_);
lean_ctor_set(v___x_186_, 5, v___x_182_);
lean_ctor_set(v___x_186_, 6, v___x_183_);
lean_ctor_set(v___x_186_, 7, v___x_184_);
lean_ctor_set(v___x_186_, 8, v___x_185_);
v___x_187_ = lean_io_get_num_heartbeats();
v___x_188_ = lean_st_mk_ref(v___x_186_);
v___x_189_ = l_Lean_inheritedTraceOptions;
v___x_190_ = lean_st_ref_get(v___x_189_);
v___x_191_ = lean_uint8_once(&l_Lake_Package_mkConfigString___closed__21, &l_Lake_Package_mkConfigString___closed__21_once, _init_l_Lake_Package_mkConfigString___closed__21);
v___x_227_ = lean_st_ref_get(v___x_188_);
v_env_249_ = lean_ctor_get(v___x_227_, 0);
lean_inc_ref(v_env_249_);
lean_dec(v___x_227_);
v___x_250_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_249_);
lean_dec_ref(v_env_249_);
if (v___x_191_ == 0)
{
if (v___x_250_ == 0)
{
lean_inc(v___x_188_);
v___y_193_ = v___x_188_;
goto v___jp_192_;
}
else
{
v___y_229_ = v___x_191_;
goto v___jp_228_;
}
}
else
{
v___y_229_ = v___x_250_;
goto v___jp_228_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__22, &l_Lake_Package_mkConfigString___closed__22_once, _init_l_Lake_Package_mkConfigString___closed__22);
v___x_195_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_195_, 0, v___x_169_);
lean_ctor_set(v___x_195_, 1, v___x_170_);
lean_ctor_set(v___x_195_, 2, v___x_163_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
lean_ctor_set(v___x_195_, 4, v___x_171_);
lean_ctor_set(v___x_195_, 5, v___x_172_);
lean_ctor_set(v___x_195_, 6, v___x_187_);
lean_ctor_set(v___x_195_, 7, v___x_174_);
lean_ctor_set(v___x_195_, 8, v___x_171_);
lean_ctor_set(v___x_195_, 9, v___x_175_);
lean_ctor_set(v___x_195_, 10, v___x_176_);
lean_ctor_set(v___x_195_, 11, v___x_190_);
v___x_196_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_173_);
lean_ctor_set(v___x_196_, 2, v___x_177_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3, v___x_191_);
lean_ctor_set_uint8(v___x_196_, sizeof(void*)*3 + 1, v___x_160_);
v___x_197_ = l_Lean_PrettyPrinter_ppModule(v___x_168_, v___x_196_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref_known(v___x_196_, 3);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_str_205_; lean_object* v_startInclusive_206_; lean_object* v_endExclusive_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_197_, 1);
v___x_199_ = lean_st_ref_get(v___x_188_);
lean_dec(v___x_188_);
lean_dec(v___x_199_);
v___x_200_ = l_Std_Format_defWidth;
v___x_201_ = l_Std_Format_pretty(v_a_198_, v___x_200_, v___x_173_, v___x_173_);
v___x_202_ = lean_string_utf8_byte_size(v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_173_);
lean_ctor_set(v___x_203_, 2, v___x_202_);
v___x_204_ = l_String_Slice_trimAscii(v___x_203_);
v_str_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_ref(v_str_205_);
v_startInclusive_206_ = lean_ctor_get(v___x_204_, 1);
lean_inc(v_startInclusive_206_);
v_endExclusive_207_ = lean_ctor_get(v___x_204_, 2);
lean_inc(v_endExclusive_207_);
lean_dec_ref(v___x_204_);
v___x_208_ = lean_string_utf8_extract_fast(v_str_205_, v_startInclusive_206_, v_endExclusive_207_);
lean_dec(v_endExclusive_207_);
lean_dec(v_startInclusive_206_);
lean_dec_ref(v_str_205_);
v___x_209_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__23));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v_a_145_);
return v___x_211_;
}
else
{
lean_object* v_a_212_; 
lean_dec(v___x_188_);
v_a_212_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_197_, 1);
if (lean_obj_tag(v_a_212_) == 0)
{
lean_object* v_msg_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_msg_213_ = lean_ctor_get(v_a_212_, 1);
lean_inc_ref(v_msg_213_);
lean_dec_ref_known(v_a_212_, 2);
v___x_214_ = l_Lean_MessageData_toString(v_msg_213_);
v___x_215_ = lean_mk_io_user_error(v___x_214_);
v_a_148_ = v___x_215_;
goto v___jp_147_;
}
else
{
lean_object* v_id_216_; lean_object* v___x_217_; 
v_id_216_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_id_216_);
lean_dec_ref_known(v_a_212_, 2);
v___x_217_ = l_Lean_InternalExceptionId_getName(v_id_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec(v_id_216_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__24));
v___x_220_ = l_Lean_Name_toString(v_a_218_, v___x_161_);
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
lean_dec_ref(v___x_220_);
v_a_158_ = v___x_221_;
goto v___jp_157_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref_known(v___x_217_, 1);
v___x_222_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__25));
v___x_223_ = l_Nat_reprFast(v_id_216_);
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
lean_dec_ref(v___x_223_);
v___x_225_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__26));
v___x_226_ = lean_string_append(v___x_224_, v___x_225_);
v_a_158_ = v___x_226_;
goto v___jp_157_;
}
}
}
}
v___jp_228_:
{
if (v___y_229_ == 0)
{
lean_object* v___x_230_; lean_object* v_env_231_; lean_object* v_nextMacroScope_232_; lean_object* v_ngen_233_; lean_object* v_auxDeclNGen_234_; lean_object* v_traceState_235_; lean_object* v_messages_236_; lean_object* v_infoState_237_; lean_object* v_snapshotTasks_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_247_; 
v___x_230_ = lean_st_ref_take(v___x_188_);
v_env_231_ = lean_ctor_get(v___x_230_, 0);
v_nextMacroScope_232_ = lean_ctor_get(v___x_230_, 1);
v_ngen_233_ = lean_ctor_get(v___x_230_, 2);
v_auxDeclNGen_234_ = lean_ctor_get(v___x_230_, 3);
v_traceState_235_ = lean_ctor_get(v___x_230_, 4);
v_messages_236_ = lean_ctor_get(v___x_230_, 6);
v_infoState_237_ = lean_ctor_get(v___x_230_, 7);
v_snapshotTasks_238_ = lean_ctor_get(v___x_230_, 8);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v___x_230_, 5);
lean_dec(v_unused_248_);
v___x_240_ = v___x_230_;
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snapshotTasks_238_);
lean_inc(v_infoState_237_);
lean_inc(v_messages_236_);
lean_inc(v_traceState_235_);
lean_inc(v_auxDeclNGen_234_);
lean_inc(v_ngen_233_);
lean_inc(v_nextMacroScope_232_);
lean_inc(v_env_231_);
lean_dec(v___x_230_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_247_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = l_Lean_Kernel_enableDiag(v_env_231_, v___x_191_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 5, v___x_182_);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_nextMacroScope_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_ngen_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_auxDeclNGen_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_traceState_235_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_messages_236_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_infoState_237_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_snapshotTasks_238_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_st_ref_put(v___x_188_, v___x_244_);
lean_inc(v___x_188_);
v___y_193_ = v___x_188_;
goto v___jp_192_;
}
}
}
else
{
lean_inc(v___x_188_);
v___y_193_ = v___x_188_;
goto v___jp_192_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref(v_pkg_143_);
v_a_251_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_165_, 1);
v___x_252_ = lean_io_error_to_string(v_a_251_);
v___x_253_ = 3;
v___x_254_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*1, v___x_253_);
v___x_255_ = lean_array_get_size(v_a_145_);
v___x_256_ = lean_array_push(v_a_145_, v___x_254_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__27, &l_Lake_Package_mkConfigString___closed__27_once, _init_l_Lake_Package_mkConfigString___closed__27);
v___x_259_ = l_Lake_Package_mkTomlConfig(v_pkg_143_, v___x_258_);
v___x_260_ = l_Lake_Toml_ppTable(v___x_259_);
lean_dec_ref(v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_145_);
return v___x_261_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_149_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__0));
v___x_150_ = lean_io_error_to_string(v_a_148_);
v___x_151_ = lean_string_append(v___x_149_, v___x_150_);
lean_dec_ref(v___x_150_);
v___x_152_ = 3;
v___x_153_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*1, v___x_152_);
v___x_154_ = lean_array_get_size(v_a_145_);
v___x_155_ = lean_array_push(v_a_145_, v___x_153_);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
v___jp_157_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_mk_io_user_error(v_a_158_);
v_a_148_ = v___x_159_;
goto v___jp_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* v_pkg_262_, lean_object* v_lang_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
uint8_t v_lang_boxed_266_; lean_object* v_res_267_; 
v_lang_boxed_266_ = lean_unbox(v_lang_263_);
v_res_267_ = l_Lake_Package_mkConfigString(v_pkg_262_, v_lang_boxed_266_, v_a_264_);
return v_res_267_;
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
