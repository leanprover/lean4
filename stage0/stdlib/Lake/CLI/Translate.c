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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t v_sz_1_, size_t v_i_2_, lean_object* v_bs_3_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1_ = stack[0].m_num;
size_t v_i_2_ = stack[1].m_num;
lean_object* v_bs_3_ = stack[2].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_1_, v_i_2_, v_bs_3_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object* v_x_14_){
_start:
{
switch(lean_obj_tag(v_x_14_))
{
case 3:
{
lean_object* v_info_15_; lean_object* v_rawVal_16_; lean_object* v_val_17_; lean_object* v_preresolved_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_26_; 
v_info_15_ = lean_ctor_get(v_x_14_, 0);
v_rawVal_16_ = lean_ctor_get(v_x_14_, 1);
v_val_17_ = lean_ctor_get(v_x_14_, 2);
v_preresolved_18_ = lean_ctor_get(v_x_14_, 3);
v_isSharedCheck_26_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_26_ == 0)
{
v___x_20_ = v_x_14_;
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_preresolved_18_);
lean_inc(v_val_17_);
lean_inc(v_rawVal_16_);
lean_inc(v_info_15_);
lean_dec(v_x_14_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_26_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = l_Lean_Name_eraseMacroScopes(v_val_17_);
lean_dec(v_val_17_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 2, v___x_22_);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_info_15_);
lean_ctor_set(v_reuseFailAlloc_25_, 1, v_rawVal_16_);
lean_ctor_set(v_reuseFailAlloc_25_, 2, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_25_, 3, v_preresolved_18_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
case 1:
{
lean_object* v_info_27_; lean_object* v_kind_28_; lean_object* v_args_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_39_; 
v_info_27_ = lean_ctor_get(v_x_14_, 0);
v_kind_28_ = lean_ctor_get(v_x_14_, 1);
v_args_29_ = lean_ctor_get(v_x_14_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_39_ == 0)
{
v___x_31_ = v_x_14_;
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_args_29_);
lean_inc(v_kind_28_);
lean_inc(v_info_27_);
lean_dec(v_x_14_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_39_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
size_t v_sz_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v_sz_33_ = lean_array_size(v_args_29_);
v___x_34_ = ((size_t)0ULL);
v___x_35_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_33_, v___x_34_, v_args_29_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 2, v___x_35_);
v___x_37_ = v___x_31_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_info_27_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_kind_28_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
default: 
{
return v_x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object* v_sz_40_, lean_object* v_i_41_, lean_object* v_bs_42_){
_start:
{
size_t v_sz_boxed_43_; size_t v_i_boxed_44_; lean_object* v_res_45_; 
v_sz_boxed_43_ = lean_unbox_usize(v_sz_40_);
lean_dec(v_sz_40_);
v_i_boxed_44_ = lean_unbox_usize(v_i_41_);
lean_dec(v_i_41_);
v_res_45_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(v_sz_boxed_43_, v_i_boxed_44_, v_bs_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object* v_stx_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object* v_k_48_, lean_object* v_stx_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v_stx_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object* v_k_51_, lean_object* v_stx_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(v_k_51_, v_stx_52_);
lean_dec(v_k_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(lean_object* v_opts_54_, lean_object* v_opt_55_){
_start:
{
lean_object* v_name_56_; lean_object* v_defValue_57_; lean_object* v_map_58_; lean_object* v___x_59_; 
v_name_56_ = lean_ctor_get(v_opt_55_, 0);
v_defValue_57_ = lean_ctor_get(v_opt_55_, 1);
v_map_58_ = lean_ctor_get(v_opts_54_, 0);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_58_, v_name_56_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_inc(v_defValue_57_);
return v_defValue_57_;
}
else
{
lean_object* v_val_60_; 
v_val_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v___x_59_, 1);
if (lean_obj_tag(v_val_60_) == 3)
{
lean_object* v_v_61_; 
v_v_61_ = lean_ctor_get(v_val_60_, 0);
lean_inc(v_v_61_);
lean_dec_ref_known(v_val_60_, 1);
return v_v_61_;
}
else
{
lean_dec(v_val_60_);
lean_inc(v_defValue_57_);
return v_defValue_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0___boxed(lean_object* v_opts_62_, lean_object* v_opt_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v_opts_62_, v_opt_63_);
lean_dec_ref(v_opt_63_);
lean_dec_ref(v_opts_62_);
return v_res_64_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = l_Lean_Options_empty;
v___x_79_ = l_Lean_Core_getMaxHeartbeats(v___x_78_);
return v___x_79_;
}
}
static uint16_t _init_l_Lake_Package_mkConfigString___closed__7(void){
_start:
{
lean_object* v___x_80_; uint16_t v___x_81_; 
v___x_80_ = l_Lean_Options_empty;
v___x_81_ = l_Lean_OptionFlags_ofOptions(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = l_Lean_firstFrontendMacroScope;
v___x_84_ = lean_nat_add(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__13(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__14(void){
_start:
{
size_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = ((size_t)5ULL);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_unsigned_to_nat(32u);
v___x_101_ = lean_mk_empty_array_with_capacity(v___x_100_);
v___x_102_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__13, &l_Lake_Package_mkConfigString___closed__13_once, _init_l_Lake_Package_mkConfigString___closed__13);
v___x_103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_99_);
lean_ctor_set(v___x_103_, 3, v___x_99_);
lean_ctor_set_usize(v___x_103_, 4, v___x_98_);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__15(void){
_start:
{
lean_object* v___x_104_; uint64_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_105_ = 0ULL;
v___x_106_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set_uint64(v___x_106_, sizeof(void*)*1, v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_107_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__16, &l_Lake_Package_mkConfigString___closed__16_once, _init_l_Lake_Package_mkConfigString___closed__16);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__18(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Lean_Options_empty;
v___x_116_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__19));
v___x_117_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
lean_ctor_set(v___x_117_, 3, v___x_114_);
lean_ctor_set(v___x_117_, 4, v___x_114_);
lean_ctor_set(v___x_117_, 5, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__21(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = l_Lean_NameSet_empty;
v___x_119_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_ctor_set(v___x_120_, 2, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__22(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__14, &l_Lake_Package_mkConfigString___closed__14_once, _init_l_Lake_Package_mkConfigString___closed__14);
v___x_122_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__17, &l_Lake_Package_mkConfigString___closed__17_once, _init_l_Lake_Package_mkConfigString___closed__17);
v___x_123_ = 1;
v___x_124_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
lean_ctor_set_uint8(v___x_124_, sizeof(void*)*3, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__23(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = l_Lean_maxRecDepth;
v___x_126_ = l_Lean_Options_empty;
v___x_127_ = l_Lean_Option_get___at___00Lake_Package_mkConfigString_spec__0(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static uint16_t _init_l_Lake_Package_mkConfigString___closed__28(void){
_start:
{
uint16_t v___x_132_; uint16_t v___x_133_; uint16_t v___x_134_; 
v___x_132_ = 512;
v___x_133_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_134_ = lean_uint16_land(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static uint8_t _init_l_Lake_Package_mkConfigString___closed__29(void){
_start:
{
uint16_t v___x_135_; uint16_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = 0;
v___x_136_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__28, &l_Lake_Package_mkConfigString___closed__28_once, _init_l_Lake_Package_mkConfigString___closed__28);
v___x_137_ = lean_uint16_dec_eq(v___x_136_, v___x_135_);
return v___x_137_;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__30(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_138_;
}
}
lean_object* l_Lake_Package_mkConfigString(lean_object* v_pkg_139_, uint8_t v_lang_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_a_144_; lean_object* v_a_154_; 
if (v_lang_140_ == 0)
{
uint8_t v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint32_t v___x_160_; lean_object* v___x_161_; 
v___x_156_ = 0;
v___x_157_ = 1;
v___x_158_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__4));
v___x_159_ = l_Lean_Options_empty;
v___x_160_ = 1024;
v___x_161_ = l_Lake_importModulesUsingCache(v___x_158_, v___x_159_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint16_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_fileName_188_; lean_object* v_fileMap_189_; lean_object* v_currNamespace_190_; lean_object* v_openDecls_191_; lean_object* v_initHeartbeats_192_; lean_object* v_maxHeartbeats_193_; lean_object* v_quotContext_194_; lean_object* v_currMacroScope_195_; lean_object* v_cancelTk_x3f_196_; lean_object* v_inheritedTraceOptions_197_; lean_object* v_currRecDepth_198_; lean_object* v_ref_199_; uint8_t v_suppressElabErrors_200_; uint8_t v_isRecordingDeps_201_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___y_239_; lean_object* v_env_260_; uint8_t v___x_261_; uint8_t v___x_262_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_161_, 1);
v___x_163_ = l_Lake_Package_mkLeanConfig(v_pkg_139_);
v___x_164_ = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(v___x_163_);
v___x_165_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__5));
v___x_166_ = l_Lean_instInhabitedFileMap_default;
v___x_167_ = lean_box(0);
v___x_168_ = lean_box(0);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__6, &l_Lake_Package_mkConfigString___closed__6_once, _init_l_Lake_Package_mkConfigString___closed__6);
v___x_171_ = l_Lean_firstFrontendMacroScope;
v___x_172_ = lean_box(0);
v___x_173_ = lean_box(0);
v___x_174_ = lean_uint16_once(&l_Lake_Package_mkConfigString___closed__7, &l_Lake_Package_mkConfigString___closed__7_once, _init_l_Lake_Package_mkConfigString___closed__7);
v___x_175_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__8, &l_Lake_Package_mkConfigString___closed__8_once, _init_l_Lake_Package_mkConfigString___closed__8);
v___x_176_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__11));
v___x_177_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__12));
v___x_178_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__15, &l_Lake_Package_mkConfigString___closed__15_once, _init_l_Lake_Package_mkConfigString___closed__15);
v___x_179_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__18, &l_Lake_Package_mkConfigString___closed__18_once, _init_l_Lake_Package_mkConfigString___closed__18);
v___x_180_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__19));
v___x_181_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__20, &l_Lake_Package_mkConfigString___closed__20_once, _init_l_Lake_Package_mkConfigString___closed__20);
v___x_182_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__21, &l_Lake_Package_mkConfigString___closed__21_once, _init_l_Lake_Package_mkConfigString___closed__21);
v___x_183_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__22, &l_Lake_Package_mkConfigString___closed__22_once, _init_l_Lake_Package_mkConfigString___closed__22);
v___x_184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_184_, 0, v_a_162_);
lean_ctor_set(v___x_184_, 1, v___x_175_);
lean_ctor_set(v___x_184_, 2, v___x_176_);
lean_ctor_set(v___x_184_, 3, v___x_177_);
lean_ctor_set(v___x_184_, 4, v___x_178_);
lean_ctor_set(v___x_184_, 5, v___x_179_);
lean_ctor_set(v___x_184_, 6, v___x_181_);
lean_ctor_set(v___x_184_, 7, v___x_182_);
lean_ctor_set(v___x_184_, 8, v___x_183_);
lean_ctor_set(v___x_184_, 9, v___x_180_);
v___x_185_ = lean_io_get_num_heartbeats();
v___x_186_ = lean_st_mk_ref(v___x_184_);
v___x_235_ = l_Lean_inheritedTraceOptions;
v___x_236_ = lean_st_ref_get(v___x_235_);
v___x_237_ = lean_st_ref_get(v___x_186_);
v_env_260_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_237_);
v___x_261_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_260_);
lean_dec_ref(v_env_260_);
v___x_262_ = lean_uint8_once(&l_Lake_Package_mkConfigString___closed__29, &l_Lake_Package_mkConfigString___closed__29_once, _init_l_Lake_Package_mkConfigString___closed__29);
if (v___x_262_ == 0)
{
if (v___x_261_ == 0)
{
v___y_239_ = v___x_157_;
goto v___jp_238_;
}
else
{
v_fileName_188_ = v___x_165_;
v_fileMap_189_ = v___x_166_;
v_currNamespace_190_ = v___x_167_;
v_openDecls_191_ = v___x_168_;
v_initHeartbeats_192_ = v___x_185_;
v_maxHeartbeats_193_ = v___x_170_;
v_quotContext_194_ = v___x_167_;
v_currMacroScope_195_ = v___x_171_;
v_cancelTk_x3f_196_ = v___x_172_;
v_inheritedTraceOptions_197_ = v___x_236_;
v_currRecDepth_198_ = v___x_169_;
v_ref_199_ = v___x_173_;
v_suppressElabErrors_200_ = v___x_156_;
v_isRecordingDeps_201_ = v___x_156_;
goto v___jp_187_;
}
}
else
{
if (v___x_261_ == 0)
{
v_fileName_188_ = v___x_165_;
v_fileMap_189_ = v___x_166_;
v_currNamespace_190_ = v___x_167_;
v_openDecls_191_ = v___x_168_;
v_initHeartbeats_192_ = v___x_185_;
v_maxHeartbeats_193_ = v___x_170_;
v_quotContext_194_ = v___x_167_;
v_currMacroScope_195_ = v___x_171_;
v_cancelTk_x3f_196_ = v___x_172_;
v_inheritedTraceOptions_197_ = v___x_236_;
v_currRecDepth_198_ = v___x_169_;
v_ref_199_ = v___x_173_;
v_suppressElabErrors_200_ = v___x_156_;
v_isRecordingDeps_201_ = v___x_156_;
goto v___jp_187_;
}
else
{
v___y_239_ = v___x_156_;
goto v___jp_238_;
}
}
v___jp_187_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__23, &l_Lake_Package_mkConfigString___closed__23_once, _init_l_Lake_Package_mkConfigString___closed__23);
lean_inc(v_cancelTk_x3f_196_);
lean_inc(v_currMacroScope_195_);
lean_inc(v_quotContext_194_);
lean_inc(v_maxHeartbeats_193_);
lean_inc(v_openDecls_191_);
lean_inc(v_currNamespace_190_);
lean_inc_ref(v_fileMap_189_);
lean_inc_ref(v_fileName_188_);
v___x_203_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_203_, 0, v_fileName_188_);
lean_ctor_set(v___x_203_, 1, v_fileMap_189_);
lean_ctor_set(v___x_203_, 2, v___x_159_);
lean_ctor_set(v___x_203_, 3, v___x_202_);
lean_ctor_set(v___x_203_, 4, v_currNamespace_190_);
lean_ctor_set(v___x_203_, 5, v_openDecls_191_);
lean_ctor_set(v___x_203_, 6, v_initHeartbeats_192_);
lean_ctor_set(v___x_203_, 7, v_maxHeartbeats_193_);
lean_ctor_set(v___x_203_, 8, v_quotContext_194_);
lean_ctor_set(v___x_203_, 9, v_currMacroScope_195_);
lean_ctor_set(v___x_203_, 10, v_cancelTk_x3f_196_);
lean_ctor_set(v___x_203_, 11, v_inheritedTraceOptions_197_);
lean_inc(v_ref_199_);
v___x_204_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_currRecDepth_198_);
lean_ctor_set(v___x_204_, 2, v_ref_199_);
lean_ctor_set_uint16(v___x_204_, sizeof(void*)*3, v___x_174_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*3 + 2, v_suppressElabErrors_200_);
lean_ctor_set_uint8(v___x_204_, sizeof(void*)*3 + 3, v_isRecordingDeps_201_);
v___x_205_ = l_Lean_PrettyPrinter_ppModule(v___x_164_, v___x_204_, v___x_186_);
lean_dec_ref_known(v___x_204_, 3);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_str_213_; lean_object* v_startInclusive_214_; lean_object* v_endExclusive_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
v___x_207_ = lean_st_ref_get(v___x_186_);
lean_dec(v___x_186_);
lean_dec(v___x_207_);
v___x_208_ = l_Std_Format_defWidth;
v___x_209_ = l_Std_Format_pretty(v_a_206_, v___x_208_, v___x_169_, v___x_169_);
v___x_210_ = lean_string_utf8_byte_size(v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_169_);
lean_ctor_set(v___x_211_, 2, v___x_210_);
v___x_212_ = l_String_Slice_trimAscii(v___x_211_);
v_str_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc_ref(v_str_213_);
v_startInclusive_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_startInclusive_214_);
v_endExclusive_215_ = lean_ctor_get(v___x_212_, 2);
lean_inc(v_endExclusive_215_);
lean_dec_ref(v___x_212_);
v___x_216_ = lean_string_utf8_extract_fast(v_str_213_, v_startInclusive_214_, v_endExclusive_215_);
lean_dec(v_endExclusive_215_);
lean_dec(v_startInclusive_214_);
lean_dec_ref(v_str_213_);
v___x_217_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__24));
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v_a_141_);
return v___x_219_;
}
else
{
lean_object* v_a_220_; 
lean_dec(v___x_186_);
v_a_220_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_a_220_) == 0)
{
lean_object* v_msg_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_msg_221_ = lean_ctor_get(v_a_220_, 1);
lean_inc_ref(v_msg_221_);
lean_dec_ref_known(v_a_220_, 2);
v___x_222_ = l_Lean_MessageData_toString(v_msg_221_);
v___x_223_ = lean_mk_io_user_error(v___x_222_);
v_a_144_ = v___x_223_;
goto v___jp_143_;
}
else
{
lean_object* v_id_224_; lean_object* v___x_225_; 
v_id_224_ = lean_ctor_get(v_a_220_, 0);
lean_inc(v_id_224_);
lean_dec_ref_known(v_a_220_, 2);
v___x_225_ = l_Lean_InternalExceptionId_getName(v_id_224_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_id_224_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__25));
v___x_228_ = l_Lean_Name_toString(v_a_226_, v___x_157_);
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
lean_dec_ref(v___x_228_);
v_a_154_ = v___x_229_;
goto v___jp_153_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_230_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__26));
v___x_231_ = l_Nat_reprFast(v_id_224_);
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__27));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v_a_154_ = v___x_234_;
goto v___jp_153_;
}
}
}
}
v___jp_238_:
{
lean_object* v___x_240_; lean_object* v_env_241_; lean_object* v_nextMacroScope_242_; lean_object* v_ngen_243_; lean_object* v_auxDeclNGen_244_; lean_object* v_traceState_245_; lean_object* v_recordedDeps_246_; lean_object* v_messages_247_; lean_object* v_infoState_248_; lean_object* v_snapshotTasks_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_258_; 
v___x_240_ = lean_st_ref_take(v___x_186_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
v_nextMacroScope_242_ = lean_ctor_get(v___x_240_, 1);
v_ngen_243_ = lean_ctor_get(v___x_240_, 2);
v_auxDeclNGen_244_ = lean_ctor_get(v___x_240_, 3);
v_traceState_245_ = lean_ctor_get(v___x_240_, 4);
v_recordedDeps_246_ = lean_ctor_get(v___x_240_, 6);
v_messages_247_ = lean_ctor_get(v___x_240_, 7);
v_infoState_248_ = lean_ctor_get(v___x_240_, 8);
v_snapshotTasks_249_ = lean_ctor_get(v___x_240_, 9);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_240_, 5);
lean_dec(v_unused_259_);
v___x_251_ = v___x_240_;
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snapshotTasks_249_);
lean_inc(v_infoState_248_);
lean_inc(v_messages_247_);
lean_inc(v_recordedDeps_246_);
lean_inc(v_traceState_245_);
lean_inc(v_auxDeclNGen_244_);
lean_inc(v_ngen_243_);
lean_inc(v_nextMacroScope_242_);
lean_inc(v_env_241_);
lean_dec(v___x_240_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_258_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_Kernel_enableDiag(v_env_241_, v___y_239_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 5, v___x_179_);
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_nextMacroScope_242_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_ngen_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v_auxDeclNGen_244_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_traceState_245_);
lean_ctor_set(v_reuseFailAlloc_257_, 5, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_257_, 6, v_recordedDeps_246_);
lean_ctor_set(v_reuseFailAlloc_257_, 7, v_messages_247_);
lean_ctor_set(v_reuseFailAlloc_257_, 8, v_infoState_248_);
lean_ctor_set(v_reuseFailAlloc_257_, 9, v_snapshotTasks_249_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_st_ref_put(v___x_186_, v___x_255_);
v_fileName_188_ = v___x_165_;
v_fileMap_189_ = v___x_166_;
v_currNamespace_190_ = v___x_167_;
v_openDecls_191_ = v___x_168_;
v_initHeartbeats_192_ = v___x_185_;
v_maxHeartbeats_193_ = v___x_170_;
v_quotContext_194_ = v___x_167_;
v_currMacroScope_195_ = v___x_171_;
v_cancelTk_x3f_196_ = v___x_172_;
v_inheritedTraceOptions_197_ = v___x_236_;
v_currRecDepth_198_ = v___x_169_;
v_ref_199_ = v___x_173_;
v_suppressElabErrors_200_ = v___x_156_;
v_isRecordingDeps_201_ = v___x_156_;
goto v___jp_187_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v_pkg_139_);
v_a_263_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_161_, 1);
v___x_264_ = lean_io_error_to_string(v_a_263_);
v___x_265_ = 3;
v___x_266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_265_);
v___x_267_ = lean_array_get_size(v_a_141_);
v___x_268_ = lean_array_push(v_a_141_, v___x_266_);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
return v___x_269_;
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_270_ = lean_obj_once(&l_Lake_Package_mkConfigString___closed__30, &l_Lake_Package_mkConfigString___closed__30_once, _init_l_Lake_Package_mkConfigString___closed__30);
v___x_271_ = l_Lake_Package_mkTomlConfig(v_pkg_139_, v___x_270_);
v___x_272_ = l_Lake_Toml_ppTable(v___x_271_);
lean_dec_ref(v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_a_141_);
return v___x_273_;
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_145_ = ((lean_object*)(l_Lake_Package_mkConfigString___closed__0));
v___x_146_ = lean_io_error_to_string(v_a_144_);
v___x_147_ = lean_string_append(v___x_145_, v___x_146_);
lean_dec_ref(v___x_146_);
v___x_148_ = 3;
v___x_149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = lean_array_get_size(v_a_141_);
v___x_151_ = lean_array_push(v_a_141_, v___x_149_);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
return v___x_152_;
}
v___jp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_mk_io_user_error(v_a_154_);
v_a_144_ = v___x_155_;
goto v___jp_143_;
}
}
}
LEAN_EXPORT void l_Lake_Package_mkConfigString_0interp(lean_interpreter_value* stack)
{
lean_object* v_pkg_139_ = stack[0].m_obj;
uint8_t v_lang_140_ = stack[1].m_num;
lean_object* v_a_141_ = stack[2].m_obj;
lean_object* v_res_274_;
v_res_274_ = l_Lake_Package_mkConfigString(v_pkg_139_, v_lang_140_, v_a_141_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* v_pkg_275_, lean_object* v_lang_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
uint8_t v_lang_boxed_279_; lean_object* v_res_280_; 
v_lang_boxed_279_ = lean_unbox(v_lang_276_);
v_res_280_ = l_Lake_Package_mkConfigString(v_pkg_275_, v_lang_boxed_279_, v_a_277_);
return v_res_280_;
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
