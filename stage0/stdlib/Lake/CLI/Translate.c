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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__5;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__6;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__7;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__8;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__9;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__10;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__11;
static const lean_string_object l_Lake_Package_mkConfigString___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Package_mkConfigString___closed__12 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__12_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Package_mkConfigString___closed__12_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Package_mkConfigString___closed__13 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__13_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Package_mkConfigString___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__14 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__14_value;
static const lean_ctor_object l_Lake_Package_mkConfigString___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Package_mkConfigString___closed__15 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__15_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__16;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__17;
static const lean_array_object l_Lake_Package_mkConfigString___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_mkConfigString___closed__18 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__18_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Package_mkConfigString___closed__19 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__19_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__20;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Package_mkConfigString___closed__21;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__22;
static const lean_string_object l_Lake_Package_mkConfigString___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lake_Package_mkConfigString___closed__23 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__23_value;
static const lean_string_object l_Lake_Package_mkConfigString___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lake_Package_mkConfigString___closed__24 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__24_value;
static const lean_closure_object l_Lake_Package_mkConfigString___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_mkConfigString___closed__25 = (const lean_object*)&l_Lake_Package_mkConfigString___closed__25_value;
static lean_once_cell_t l_Lake_Package_mkConfigString___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_mkConfigString___closed__26;
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
v___x_21_ = lean_erase_macro_scopes(v_val_16_);
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
lean_dec_ref(v___x_58_);
if (lean_obj_tag(v_val_60_) == 1)
{
uint8_t v_v_61_; 
v_v_61_ = lean_ctor_get_uint8(v_val_60_, 0);
lean_dec_ref(v_val_60_);
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
lean_dec_ref(v___x_72_);
if (lean_obj_tag(v_val_73_) == 3)
{
lean_object* v_v_74_; 
v_v_74_ = lean_ctor_get(v_val_73_, 0);
lean_inc(v_v_74_);
lean_dec_ref(v_val_73_);
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
static lean_object* _init_l_Lake_Package_mkConfigString___closed__5(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_unsigned_to_nat(32u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6(void){
_start:
{
size_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = ((size_t)5ULL);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__5, &l_Lake_Package_mkConfigString___closed__5_once, _init_l_Lake_Package_mkConfigString___closed__5);
v___x_98_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
lean_ctor_set(v___x_98_, 2, v___x_94_);
lean_ctor_set(v___x_98_, 3, v___x_94_);
lean_ctor_set_usize(v___x_98_, 4, v___x_93_);
return v___x_98_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__7(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_99_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__9(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__8, &l_Lake_Package_mkConfigString___closed__8_once, _init_l_Lake_Package_mkConfigString___closed__8);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__10(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_NameSet_empty;
v___x_105_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
lean_ctor_set(v___x_106_, 2, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__11(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = l_Lean_firstFrontendMacroScope;
v___x_109_ = lean_nat_add(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16(void){
_start:
{
lean_object* v___x_120_; uint64_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_121_ = 0ULL;
v___x_122_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint64(v___x_122_, sizeof(void*)*1, v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; 
v___x_123_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_124_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__8, &l_Lake_Package_mkConfigString___closed__8_once, _init_l_Lake_Package_mkConfigString___closed__8);
v___x_125_ = 1;
v___x_126_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
lean_ctor_set(v___x_126_, 2, v___x_123_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*3, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = l_Lean_Options_empty;
v___x_131_ = l_Lean_Core_getMaxHeartbeats(v___x_130_);
return v___x_131_;
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
static lean_object* _init_l_Lake_Package_mkConfigString___closed__26(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__25));
v___x_142_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* v_pkg_143_, uint8_t v_lang_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_a_148_; 
if (v_lang_144_ == 0)
{
uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint32_t v___x_160_; lean_object* v___x_161_; 
v___x_157_ = 0;
v___x_158_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__4));
v___x_159_ = l_Lean_Options_empty;
v___x_160_ = 1024;
v___x_161_ = l_Lake_importModulesUsingCache(v___x_158_, v___x_159_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_env_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v_fileName_191_; lean_object* v_fileMap_192_; lean_object* v_currRecDepth_193_; lean_object* v_ref_194_; lean_object* v_currNamespace_195_; lean_object* v_openDecls_196_; lean_object* v_initHeartbeats_197_; lean_object* v_maxHeartbeats_198_; lean_object* v_quotContext_199_; lean_object* v_currMacroScope_200_; lean_object* v_cancelTk_x3f_201_; uint8_t v_suppressElabErrors_202_; lean_object* v_inheritedTraceOptions_203_; lean_object* v___y_204_; uint8_t v___y_232_; uint8_t v___x_252_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref(v___x_161_);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__9, &l_Lake_Package_mkConfigString___closed__9_once, _init_l_Lake_Package_mkConfigString___closed__9);
v___x_165_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__10, &l_Lake_Package_mkConfigString___closed__10_once, _init_l_Lake_Package_mkConfigString___closed__10);
v___x_166_ = lean_io_get_num_heartbeats();
v___x_167_ = l_Lean_firstFrontendMacroScope;
v___x_168_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__11, &l_Lake_Package_mkConfigString___closed__11_once, _init_l_Lake_Package_mkConfigString___closed__11);
v___x_169_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__14));
v___x_170_ = lean_box(0);
v___x_171_ = lean_box(0);
v___x_172_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__15));
v___x_173_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__16, &l_Lake_Package_mkConfigString___closed__16_once, _init_l_Lake_Package_mkConfigString___closed__16);
v___x_174_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_175_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__18));
v___x_176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_176_, 0, v_a_162_);
lean_ctor_set(v___x_176_, 1, v___x_168_);
lean_ctor_set(v___x_176_, 2, v___x_169_);
lean_ctor_set(v___x_176_, 3, v___x_172_);
lean_ctor_set(v___x_176_, 4, v___x_173_);
lean_ctor_set(v___x_176_, 5, v___x_164_);
lean_ctor_set(v___x_176_, 6, v___x_165_);
lean_ctor_set(v___x_176_, 7, v___x_174_);
lean_ctor_set(v___x_176_, 8, v___x_175_);
v___x_177_ = lean_st_mk_ref(v___x_176_);
v___x_178_ = l_Lean_inheritedTraceOptions;
v___x_179_ = lean_st_ref_get(v___x_178_);
v___x_180_ = lean_st_ref_get(v___x_177_);
v_env_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc_ref(v_env_181_);
lean_dec(v___x_180_);
v___x_182_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__19));
v___x_183_ = l_Lean_instInhabitedFileMap_default;
v___x_184_ = lean_box(0);
v___x_185_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__20, &l_Lake_Package_mkConfigString___closed__20_once, _init_l_Lake_Package_mkConfigString___closed__20);
v___x_186_ = lean_box(0);
v___x_187_ = l_Lake_Package_mkLeanConfig(v_pkg_143_);
v___x_188_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v___x_187_);
v___x_189_ = lean_uint8_once(&l_Lake_Package_mkConfigString___closed__21, &l_Lake_Package_mkConfigString___closed__21_once, _init_l_Lake_Package_mkConfigString___closed__21);
v___x_252_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_181_);
lean_dec_ref(v_env_181_);
if (v___x_252_ == 0)
{
if (v___x_189_ == 0)
{
lean_inc(v___x_177_);
v_fileName_191_ = v___x_182_;
v_fileMap_192_ = v___x_183_;
v_currRecDepth_193_ = v___x_163_;
v_ref_194_ = v___x_184_;
v_currNamespace_195_ = v___x_170_;
v_openDecls_196_ = v___x_171_;
v_initHeartbeats_197_ = v___x_166_;
v_maxHeartbeats_198_ = v___x_185_;
v_quotContext_199_ = v___x_170_;
v_currMacroScope_200_ = v___x_167_;
v_cancelTk_x3f_201_ = v___x_186_;
v_suppressElabErrors_202_ = v___x_157_;
v_inheritedTraceOptions_203_ = v___x_179_;
v___y_204_ = v___x_177_;
goto v___jp_190_;
}
else
{
v___y_232_ = v___x_252_;
goto v___jp_231_;
}
}
else
{
v___y_232_ = v___x_189_;
goto v___jp_231_;
}
v___jp_190_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__22, &l_Lake_Package_mkConfigString___closed__22_once, _init_l_Lake_Package_mkConfigString___closed__22);
v___x_206_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_206_, 0, v_fileName_191_);
lean_ctor_set(v___x_206_, 1, v_fileMap_192_);
lean_ctor_set(v___x_206_, 2, v___x_159_);
lean_ctor_set(v___x_206_, 3, v_currRecDepth_193_);
lean_ctor_set(v___x_206_, 4, v___x_205_);
lean_ctor_set(v___x_206_, 5, v_ref_194_);
lean_ctor_set(v___x_206_, 6, v_currNamespace_195_);
lean_ctor_set(v___x_206_, 7, v_openDecls_196_);
lean_ctor_set(v___x_206_, 8, v_initHeartbeats_197_);
lean_ctor_set(v___x_206_, 9, v_maxHeartbeats_198_);
lean_ctor_set(v___x_206_, 10, v_quotContext_199_);
lean_ctor_set(v___x_206_, 11, v_currMacroScope_200_);
lean_ctor_set(v___x_206_, 12, v_cancelTk_x3f_201_);
lean_ctor_set(v___x_206_, 13, v_inheritedTraceOptions_203_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*14, v___x_189_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*14 + 1, v_suppressElabErrors_202_);
v___x_207_ = l_Lean_PrettyPrinter_ppModule(v___x_188_, v___x_206_, v___y_204_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_str_215_; lean_object* v_startInclusive_216_; lean_object* v_endExclusive_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = lean_st_ref_get(v___x_177_);
lean_dec(v___x_177_);
lean_dec(v___x_209_);
v___x_210_ = l_Std_Format_defWidth;
v___x_211_ = l_Std_Format_pretty(v_a_208_, v___x_210_, v___x_163_, v___x_163_);
v___x_212_ = lean_string_utf8_byte_size(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_163_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
v___x_214_ = l_String_Slice_trimAscii(v___x_213_);
v_str_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_ref(v_str_215_);
v_startInclusive_216_ = lean_ctor_get(v___x_214_, 1);
lean_inc(v_startInclusive_216_);
v_endExclusive_217_ = lean_ctor_get(v___x_214_, 2);
lean_inc(v_endExclusive_217_);
lean_dec_ref(v___x_214_);
v___x_218_ = lean_string_utf8_extract(v_str_215_, v_startInclusive_216_, v_endExclusive_217_);
lean_dec(v_endExclusive_217_);
lean_dec(v_startInclusive_216_);
lean_dec_ref(v_str_215_);
v___x_219_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__23));
v___x_220_ = lean_string_append(v___x_218_, v___x_219_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v_a_145_);
return v___x_221_;
}
else
{
lean_object* v_a_222_; 
lean_dec(v___x_177_);
v_a_222_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_207_);
if (lean_obj_tag(v_a_222_) == 0)
{
lean_object* v_msg_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_msg_223_ = lean_ctor_get(v_a_222_, 1);
lean_inc_ref(v_msg_223_);
lean_dec_ref(v_a_222_);
v___x_224_ = l_Lean_MessageData_toString(v_msg_223_);
v___x_225_ = lean_mk_io_user_error(v___x_224_);
v_a_148_ = v___x_225_;
goto v___jp_147_;
}
else
{
lean_object* v_id_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_id_226_ = lean_ctor_get(v_a_222_, 0);
lean_inc(v_id_226_);
lean_dec_ref(v_a_222_);
v___x_227_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__24));
v___x_228_ = l_Nat_reprFast(v_id_226_);
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
lean_dec_ref(v___x_228_);
v___x_230_ = lean_mk_io_user_error(v___x_229_);
v_a_148_ = v___x_230_;
goto v___jp_147_;
}
}
}
v___jp_231_:
{
if (v___y_232_ == 0)
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v_nextMacroScope_235_; lean_object* v_ngen_236_; lean_object* v_auxDeclNGen_237_; lean_object* v_traceState_238_; lean_object* v_messages_239_; lean_object* v_infoState_240_; lean_object* v_snapshotTasks_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_250_; 
v___x_233_ = lean_st_ref_take(v___x_177_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
v_nextMacroScope_235_ = lean_ctor_get(v___x_233_, 1);
v_ngen_236_ = lean_ctor_get(v___x_233_, 2);
v_auxDeclNGen_237_ = lean_ctor_get(v___x_233_, 3);
v_traceState_238_ = lean_ctor_get(v___x_233_, 4);
v_messages_239_ = lean_ctor_get(v___x_233_, 6);
v_infoState_240_ = lean_ctor_get(v___x_233_, 7);
v_snapshotTasks_241_ = lean_ctor_get(v___x_233_, 8);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v___x_233_, 5);
lean_dec(v_unused_251_);
v___x_243_ = v___x_233_;
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_snapshotTasks_241_);
lean_inc(v_infoState_240_);
lean_inc(v_messages_239_);
lean_inc(v_traceState_238_);
lean_inc(v_auxDeclNGen_237_);
lean_inc(v_ngen_236_);
lean_inc(v_nextMacroScope_235_);
lean_inc(v_env_234_);
lean_dec(v___x_233_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_250_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = l_Lean_Kernel_enableDiag(v_env_234_, v___x_189_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 5, v___x_164_);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v_nextMacroScope_235_);
lean_ctor_set(v_reuseFailAlloc_249_, 2, v_ngen_236_);
lean_ctor_set(v_reuseFailAlloc_249_, 3, v_auxDeclNGen_237_);
lean_ctor_set(v_reuseFailAlloc_249_, 4, v_traceState_238_);
lean_ctor_set(v_reuseFailAlloc_249_, 5, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_249_, 6, v_messages_239_);
lean_ctor_set(v_reuseFailAlloc_249_, 7, v_infoState_240_);
lean_ctor_set(v_reuseFailAlloc_249_, 8, v_snapshotTasks_241_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = lean_st_ref_set(v___x_177_, v___x_247_);
lean_inc(v___x_177_);
v_fileName_191_ = v___x_182_;
v_fileMap_192_ = v___x_183_;
v_currRecDepth_193_ = v___x_163_;
v_ref_194_ = v___x_184_;
v_currNamespace_195_ = v___x_170_;
v_openDecls_196_ = v___x_171_;
v_initHeartbeats_197_ = v___x_166_;
v_maxHeartbeats_198_ = v___x_185_;
v_quotContext_199_ = v___x_170_;
v_currMacroScope_200_ = v___x_167_;
v_cancelTk_x3f_201_ = v___x_186_;
v_suppressElabErrors_202_ = v___x_157_;
v_inheritedTraceOptions_203_ = v___x_179_;
v___y_204_ = v___x_177_;
goto v___jp_190_;
}
}
}
else
{
lean_inc(v___x_177_);
v_fileName_191_ = v___x_182_;
v_fileMap_192_ = v___x_183_;
v_currRecDepth_193_ = v___x_163_;
v_ref_194_ = v___x_184_;
v_currNamespace_195_ = v___x_170_;
v_openDecls_196_ = v___x_171_;
v_initHeartbeats_197_ = v___x_166_;
v_maxHeartbeats_198_ = v___x_185_;
v_quotContext_199_ = v___x_170_;
v_currMacroScope_200_ = v___x_167_;
v_cancelTk_x3f_201_ = v___x_186_;
v_suppressElabErrors_202_ = v___x_157_;
v_inheritedTraceOptions_203_ = v___x_179_;
v___y_204_ = v___x_177_;
goto v___jp_190_;
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_254_; uint8_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v_pkg_143_);
v_a_253_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_161_);
v___x_254_ = lean_io_error_to_string(v_a_253_);
v___x_255_ = 3;
v___x_256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*1, v___x_255_);
v___x_257_ = lean_array_get_size(v_a_145_);
v___x_258_ = lean_array_push(v_a_145_, v___x_256_);
v___x_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
return v___x_259_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__26, &l_Lake_Package_mkConfigString___closed__26_once, _init_l_Lake_Package_mkConfigString___closed__26);
v___x_261_ = l_Lake_Package_mkTomlConfig(v_pkg_143_, v___x_260_);
v___x_262_ = l_Lake_Toml_ppTable(v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_a_145_);
return v___x_263_;
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
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* v_pkg_264_, lean_object* v_lang_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
uint8_t v_lang_boxed_268_; lean_object* v_res_269_; 
v_lang_boxed_268_ = lean_unbox(v_lang_265_);
v_res_269_ = l_Lake_Package_mkConfigString(v_pkg_264_, v_lang_boxed_268_, v_a_266_);
return v_res_269_;
}
}
lean_object* runtime_initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Package(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin);
lean_object* runtime_initialize_Lake_CLI_Translate_Toml(uint8_t builtin);
lean_object* runtime_initialize_Lake_CLI_Translate_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lake_Load_Lean_Elab(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_CLI_Translate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
