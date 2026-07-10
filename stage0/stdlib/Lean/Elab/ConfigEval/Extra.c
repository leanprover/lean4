// Lean compiler output
// Module: Lean.Elab.ConfigEval.Extra
// Imports: public import Lean.Elab.ConfigEval.Instances
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool;
extern lean_object* l_Lean_KVMap_instValueBool;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
extern lean_object* l_Lean_KVMap_instValueNat;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt;
extern lean_object* l_Lean_KVMap_instValueInt;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString;
extern lean_object* l_Lean_KVMap_instValueString;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName;
extern lean_object* l_Lean_KVMap_instValueName;
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Cannot set `Syntax` option `"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(lean_object* v_t_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_infoState_5_; uint8_t v_enabled_6_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_infoState_5_ = lean_ctor_get(v___x_4_, 7);
lean_inc_ref(v_infoState_5_);
lean_dec(v___x_4_);
v_enabled_6_ = lean_ctor_get_uint8(v_infoState_5_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5_);
if (v_enabled_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec_ref(v_t_1_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v_infoState_10_; lean_object* v_env_11_; lean_object* v_nextMacroScope_12_; lean_object* v_ngen_13_; lean_object* v_auxDeclNGen_14_; lean_object* v_traceState_15_; lean_object* v_cache_16_; lean_object* v_messages_17_; lean_object* v_snapshotTasks_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_40_; 
v___x_9_ = lean_st_ref_take(v___y_2_);
v_infoState_10_ = lean_ctor_get(v___x_9_, 7);
v_env_11_ = lean_ctor_get(v___x_9_, 0);
v_nextMacroScope_12_ = lean_ctor_get(v___x_9_, 1);
v_ngen_13_ = lean_ctor_get(v___x_9_, 2);
v_auxDeclNGen_14_ = lean_ctor_get(v___x_9_, 3);
v_traceState_15_ = lean_ctor_get(v___x_9_, 4);
v_cache_16_ = lean_ctor_get(v___x_9_, 5);
v_messages_17_ = lean_ctor_get(v___x_9_, 6);
v_snapshotTasks_18_ = lean_ctor_get(v___x_9_, 8);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_40_ == 0)
{
v___x_20_ = v___x_9_;
v_isShared_21_ = v_isSharedCheck_40_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_snapshotTasks_18_);
lean_inc(v_infoState_10_);
lean_inc(v_messages_17_);
lean_inc(v_cache_16_);
lean_inc(v_traceState_15_);
lean_inc(v_auxDeclNGen_14_);
lean_inc(v_ngen_13_);
lean_inc(v_nextMacroScope_12_);
lean_inc(v_env_11_);
lean_dec(v___x_9_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_40_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
uint8_t v_enabled_22_; lean_object* v_assignment_23_; lean_object* v_lazyAssignment_24_; lean_object* v_trees_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_39_; 
v_enabled_22_ = lean_ctor_get_uint8(v_infoState_10_, sizeof(void*)*3);
v_assignment_23_ = lean_ctor_get(v_infoState_10_, 0);
v_lazyAssignment_24_ = lean_ctor_get(v_infoState_10_, 1);
v_trees_25_ = lean_ctor_get(v_infoState_10_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_infoState_10_);
if (v_isSharedCheck_39_ == 0)
{
v___x_27_ = v_infoState_10_;
v_isShared_28_ = v_isSharedCheck_39_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_trees_25_);
lean_inc(v_lazyAssignment_24_);
lean_inc(v_assignment_23_);
lean_dec(v_infoState_10_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_39_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_29_ = l_Lean_PersistentArray_push___redArg(v_trees_25_, v_t_1_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 2, v___x_29_);
v___x_31_ = v___x_27_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_assignment_23_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_lazyAssignment_24_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_29_);
lean_ctor_set_uint8(v_reuseFailAlloc_38_, sizeof(void*)*3, v_enabled_22_);
v___x_31_ = v_reuseFailAlloc_38_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 7, v___x_31_);
v___x_33_ = v___x_20_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_env_11_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_nextMacroScope_12_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_ngen_13_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_auxDeclNGen_14_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_traceState_15_);
lean_ctor_set(v_reuseFailAlloc_37_, 5, v_cache_16_);
lean_ctor_set(v_reuseFailAlloc_37_, 6, v_messages_17_);
lean_ctor_set(v_reuseFailAlloc_37_, 7, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_37_, 8, v_snapshotTasks_18_);
v___x_33_ = v_reuseFailAlloc_37_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_st_ref_set(v___y_2_, v___x_33_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(lean_object* v_t_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_41_, v___y_42_);
lean_dec(v___y_42_);
return v_res_44_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_unsigned_to_nat(32u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1(void){
_start:
{
size_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_48_ = ((size_t)5ULL);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_unsigned_to_nat(32u);
v___x_51_ = lean_mk_empty_array_with_capacity(v___x_50_);
v___x_52_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0);
v___x_53_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_49_);
lean_ctor_set(v___x_53_, 3, v___x_49_);
lean_ctor_set_usize(v___x_53_, 4, v___x_48_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(lean_object* v_t_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_infoState_63_; uint8_t v_enabled_64_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_infoState_63_ = lean_ctor_get(v___x_62_, 7);
lean_inc_ref(v_infoState_63_);
lean_dec(v___x_62_);
v_enabled_64_ = lean_ctor_get_uint8(v_infoState_63_, sizeof(void*)*3);
lean_dec_ref(v_infoState_63_);
if (v_enabled_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref(v_t_54_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v_t_54_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v___x_68_, v___y_60_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(lean_object* v_t_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v_t_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(lean_object* v_info_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_87_, 0, v_info_79_);
v___x_88_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_87_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(lean_object* v_info_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v_info_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(lean_object* v_msgData_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_env_105_; lean_object* v___x_106_; lean_object* v_mctx_107_; lean_object* v_lctx_108_; lean_object* v_options_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_104_ = lean_st_ref_get(v___y_102_);
v_env_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_env_105_);
lean_dec(v___x_104_);
v___x_106_ = lean_st_ref_get(v___y_100_);
v_mctx_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_mctx_107_);
lean_dec(v___x_106_);
v_lctx_108_ = lean_ctor_get(v___y_99_, 2);
v_options_109_ = lean_ctor_get(v___y_101_, 2);
lean_inc_ref(v_options_109_);
lean_inc_ref(v_lctx_108_);
v___x_110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_110_, 0, v_env_105_);
lean_ctor_set(v___x_110_, 1, v_mctx_107_);
lean_ctor_set(v___x_110_, 2, v_lctx_108_);
lean_ctor_set(v___x_110_, 3, v_options_109_);
v___x_111_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_msgData_98_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msgData_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_119_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_box(1);
v___x_121_ = l_Lean_MessageData_ofFormat(v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2));
v___x_126_ = l_Lean_MessageData_ofFormat(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
return v_x_127_;
}
else
{
lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_152_; 
v_head_129_ = lean_ctor_get(v_x_128_, 0);
v_tail_130_ = lean_ctor_get(v_x_128_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_128_);
if (v_isSharedCheck_152_ == 0)
{
v___x_132_ = v_x_128_;
v_isShared_133_ = v_isSharedCheck_152_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_tail_130_);
lean_inc(v_head_129_);
lean_dec(v_x_128_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_152_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_before_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_150_; 
v_before_134_ = lean_ctor_get(v_head_129_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v_head_129_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v_head_129_, 1);
lean_dec(v_unused_151_);
v___x_136_ = v_head_129_;
v_isShared_137_ = v_isSharedCheck_150_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_before_134_);
lean_dec(v_head_129_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_150_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 7);
lean_ctor_set(v___x_136_, 1, v___x_138_);
lean_ctor_set(v___x_136_, 0, v_x_127_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_x_127_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_138_);
v___x_140_ = v_reuseFailAlloc_149_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3);
if (v_isShared_133_ == 0)
{
lean_ctor_set_tag(v___x_132_, 7);
lean_ctor_set(v___x_132_, 1, v___x_141_);
lean_ctor_set(v___x_132_, 0, v___x_140_);
v___x_143_ = v___x_132_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = l_Lean_MessageData_ofSyntax(v_before_134_);
v___x_145_ = l_Lean_indentD(v___x_144_);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_143_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v_x_127_ = v___x_146_;
v_x_128_ = v_tail_130_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(lean_object* v_opts_153_, lean_object* v_opt_154_){
_start:
{
lean_object* v_name_155_; lean_object* v_defValue_156_; lean_object* v_map_157_; lean_object* v___x_158_; 
v_name_155_ = lean_ctor_get(v_opt_154_, 0);
v_defValue_156_ = lean_ctor_get(v_opt_154_, 1);
v_map_157_ = lean_ctor_get(v_opts_153_, 0);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_157_, v_name_155_);
if (lean_obj_tag(v___x_158_) == 0)
{
uint8_t v___x_159_; 
v___x_159_ = lean_unbox(v_defValue_156_);
return v___x_159_;
}
else
{
lean_object* v_val_160_; 
v_val_160_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v___x_158_, 1);
if (lean_obj_tag(v_val_160_) == 1)
{
uint8_t v_v_161_; 
v_v_161_ = lean_ctor_get_uint8(v_val_160_, 0);
lean_dec_ref_known(v_val_160_, 0);
return v_v_161_;
}
else
{
uint8_t v___x_162_; 
lean_dec(v_val_160_);
v___x_162_ = lean_unbox(v_defValue_156_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_opts_163_, lean_object* v_opt_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_opts_163_, v_opt_164_);
lean_dec_ref(v_opt_164_);
lean_dec_ref(v_opts_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1));
v___x_171_ = l_Lean_MessageData_ofFormat(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(lean_object* v_msgData_172_, lean_object* v_macroStack_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_options_176_; lean_object* v___x_177_; uint8_t v___x_178_; uint8_t v___x_179_; 
v_options_176_ = lean_ctor_get(v___y_174_, 2);
v___x_177_ = l_Lean_Elab_pp_macroStack;
v___x_178_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_options_176_, v___x_177_);
v___x_179_ = lean_bool_not(v___x_178_);
if (v___x_179_ == 0)
{
if (lean_obj_tag(v_macroStack_173_) == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v_msgData_172_);
return v___x_180_;
}
else
{
lean_object* v_head_181_; lean_object* v_after_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_197_; 
v_head_181_ = lean_ctor_get(v_macroStack_173_, 0);
lean_inc(v_head_181_);
v_after_182_ = lean_ctor_get(v_head_181_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v_head_181_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v_head_181_, 0);
lean_dec(v_unused_198_);
v___x_184_ = v_head_181_;
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_after_182_);
lean_dec(v_head_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_197_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 7);
lean_ctor_set(v___x_184_, 1, v___x_186_);
lean_ctor_set(v___x_184_, 0, v_msgData_172_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_msgData_172_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_196_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_msgData_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_189_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = l_Lean_MessageData_ofSyntax(v_after_182_);
v___x_192_ = l_Lean_indentD(v___x_191_);
v_msgData_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_193_, 0, v___x_190_);
lean_ctor_set(v_msgData_193_, 1, v___x_192_);
v___x_194_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(v_msgData_193_, v_macroStack_173_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_macroStack_173_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v_msgData_172_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_200_, lean_object* v_macroStack_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_200_, v_macroStack_201_, v___y_202_);
lean_dec_ref(v___y_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v_macroStack_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_ref_213_ = lean_ctor_get(v___y_210_, 5);
v___x_214_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msg_205_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref(v___x_214_);
v_macroStack_216_ = lean_ctor_get(v___y_206_, 1);
v___x_217_ = l_Lean_Elab_getBetterRef(v_ref_213_, v_macroStack_216_);
lean_inc(v_macroStack_216_);
v___x_218_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_a_215_, v_macroStack_216_, v___y_210_);
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_217_);
lean_ctor_set(v___x_223_, 1, v_a_219_);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 1);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(lean_object* v_ref_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_fileName_246_; lean_object* v_fileMap_247_; lean_object* v_options_248_; lean_object* v_currRecDepth_249_; lean_object* v_maxRecDepth_250_; lean_object* v_ref_251_; lean_object* v_currNamespace_252_; lean_object* v_openDecls_253_; lean_object* v_initHeartbeats_254_; lean_object* v_maxHeartbeats_255_; lean_object* v_quotContext_256_; lean_object* v_currMacroScope_257_; uint8_t v_diag_258_; lean_object* v_cancelTk_x3f_259_; uint8_t v_suppressElabErrors_260_; lean_object* v_inheritedTraceOptions_261_; lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_fileName_246_ = lean_ctor_get(v___y_243_, 0);
v_fileMap_247_ = lean_ctor_get(v___y_243_, 1);
v_options_248_ = lean_ctor_get(v___y_243_, 2);
v_currRecDepth_249_ = lean_ctor_get(v___y_243_, 3);
v_maxRecDepth_250_ = lean_ctor_get(v___y_243_, 4);
v_ref_251_ = lean_ctor_get(v___y_243_, 5);
v_currNamespace_252_ = lean_ctor_get(v___y_243_, 6);
v_openDecls_253_ = lean_ctor_get(v___y_243_, 7);
v_initHeartbeats_254_ = lean_ctor_get(v___y_243_, 8);
v_maxHeartbeats_255_ = lean_ctor_get(v___y_243_, 9);
v_quotContext_256_ = lean_ctor_get(v___y_243_, 10);
v_currMacroScope_257_ = lean_ctor_get(v___y_243_, 11);
v_diag_258_ = lean_ctor_get_uint8(v___y_243_, sizeof(void*)*14);
v_cancelTk_x3f_259_ = lean_ctor_get(v___y_243_, 12);
v_suppressElabErrors_260_ = lean_ctor_get_uint8(v___y_243_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_261_ = lean_ctor_get(v___y_243_, 13);
v_ref_262_ = l_Lean_replaceRef(v_ref_237_, v_ref_251_);
lean_inc_ref(v_inheritedTraceOptions_261_);
lean_inc(v_cancelTk_x3f_259_);
lean_inc(v_currMacroScope_257_);
lean_inc(v_quotContext_256_);
lean_inc(v_maxHeartbeats_255_);
lean_inc(v_initHeartbeats_254_);
lean_inc(v_openDecls_253_);
lean_inc(v_currNamespace_252_);
lean_inc(v_maxRecDepth_250_);
lean_inc(v_currRecDepth_249_);
lean_inc_ref(v_options_248_);
lean_inc_ref(v_fileMap_247_);
lean_inc_ref(v_fileName_246_);
v___x_263_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_263_, 0, v_fileName_246_);
lean_ctor_set(v___x_263_, 1, v_fileMap_247_);
lean_ctor_set(v___x_263_, 2, v_options_248_);
lean_ctor_set(v___x_263_, 3, v_currRecDepth_249_);
lean_ctor_set(v___x_263_, 4, v_maxRecDepth_250_);
lean_ctor_set(v___x_263_, 5, v_ref_262_);
lean_ctor_set(v___x_263_, 6, v_currNamespace_252_);
lean_ctor_set(v___x_263_, 7, v_openDecls_253_);
lean_ctor_set(v___x_263_, 8, v_initHeartbeats_254_);
lean_ctor_set(v___x_263_, 9, v_maxHeartbeats_255_);
lean_ctor_set(v___x_263_, 10, v_quotContext_256_);
lean_ctor_set(v___x_263_, 11, v_currMacroScope_257_);
lean_ctor_set(v___x_263_, 12, v_cancelTk_x3f_259_);
lean_ctor_set(v___x_263_, 13, v_inheritedTraceOptions_261_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*14, v_diag_258_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*14 + 1, v_suppressElabErrors_260_);
v___x_264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___x_263_, v___y_244_);
lean_dec_ref_known(v___x_263_, 14);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(lean_object* v_ref_265_, lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_265_, v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v_ref_265_);
return v_res_274_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(lean_object* v_optionPrefix_284_, lean_object* v_opts_285_, lean_object* v_item_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_option_309_; lean_object* v_value_310_; lean_object* v_optionComps_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_423_; 
v___x_294_ = l_Lean_Elab_ConfigEval_EvalTerm_instBool;
v___x_295_ = l_Lean_Elab_ConfigEval_EvalExpr_instBool;
v___x_296_ = l_Lean_KVMap_instValueBool;
v___x_297_ = l_Lean_Elab_ConfigEval_EvalTerm_instNat;
v___x_298_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_299_ = l_Lean_KVMap_instValueNat;
v___x_300_ = l_Lean_Elab_ConfigEval_EvalTerm_instInt;
v___x_301_ = l_Lean_Elab_ConfigEval_EvalExpr_instInt;
v___x_302_ = l_Lean_KVMap_instValueInt;
v___x_303_ = l_Lean_Elab_ConfigEval_EvalTerm_instString;
v___x_304_ = l_Lean_Elab_ConfigEval_EvalExpr_instString;
v___x_305_ = l_Lean_KVMap_instValueString;
v___x_306_ = l_Lean_Elab_ConfigEval_EvalTerm_instName;
v___x_307_ = l_Lean_Elab_ConfigEval_EvalExpr_instName;
v___x_308_ = l_Lean_KVMap_instValueName;
v_option_309_ = lean_ctor_get(v_item_286_, 1);
v_value_310_ = lean_ctor_get(v_item_286_, 2);
lean_inc(v_value_310_);
v_optionComps_311_ = lean_ctor_get(v_item_286_, 5);
v___x_312_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_286_);
lean_inc(v_optionComps_311_);
v___x_313_ = lean_array_mk(v_optionComps_311_);
v___x_314_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
v___x_317_ = lean_unsigned_to_nat(2u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_array_push(v___x_318_, v___x_312_);
v___x_320_ = lean_array_push(v___x_319_, v___x_316_);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v___x_314_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
v___x_322_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v___x_322_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_323_, 0);
lean_dec(v_unused_424_);
v___x_325_ = v___x_323_;
v_isShared_326_ = v_isSharedCheck_423_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_323_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_423_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v_optName_328_; lean_object* v_inst_330_; lean_object* v_inst_331_; lean_object* v_inst_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___x_357_; 
lean_inc_ref(v_item_286_);
v___x_327_ = l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(v_item_286_);
v_optName_328_ = l_Lean_Name_append(v_optionPrefix_284_, v___x_327_);
lean_inc(v_optName_328_);
v___x_357_ = l_Lean_getOptionDecl(v_optName_328_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v_declName_359_; lean_object* v_defValue_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v_declName_359_ = lean_ctor_get(v_a_358_, 1);
lean_inc(v_declName_359_);
v_defValue_360_ = lean_ctor_get(v_a_358_, 2);
lean_inc_ref(v_defValue_360_);
lean_dec(v_a_358_);
lean_inc(v_optName_328_);
lean_inc(v_option_309_);
v___x_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_361_, 0, v_option_309_);
lean_ctor_set(v___x_361_, 1, v_optName_328_);
lean_ctor_set(v___x_361_, 2, v_declName_359_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 5);
lean_ctor_set(v___x_325_, 0, v___x_361_);
v___x_363_ = v___x_325_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_407_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_363_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec_ref(v___x_364_);
switch(lean_obj_tag(v_defValue_360_))
{
case 0:
{
lean_object* v___x_365_; 
lean_dec_ref_known(v_defValue_360_, 1);
v___x_365_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_dec_ref_known(v___x_365_, 1);
v_inst_330_ = v___x_303_;
v_inst_331_ = v___x_304_;
v_inst_332_ = v___x_305_;
v___y_333_ = v_a_287_;
v___y_334_ = v_a_288_;
v___y_335_ = v_a_289_;
v___y_336_ = v_a_290_;
v___y_337_ = v_a_291_;
v___y_338_ = v_a_292_;
goto v___jp_329_;
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_dec(v_optName_328_);
lean_dec(v_value_310_);
lean_dec_ref(v_opts_285_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_defValue_360_, 0);
lean_dec_ref(v_item_286_);
v_inst_330_ = v___x_294_;
v_inst_331_ = v___x_295_;
v_inst_332_ = v___x_296_;
v___y_333_ = v_a_287_;
v___y_334_ = v_a_288_;
v___y_335_ = v_a_289_;
v___y_336_ = v_a_290_;
v___y_337_ = v_a_291_;
v___y_338_ = v_a_292_;
goto v___jp_329_;
}
case 2:
{
lean_object* v___x_374_; 
lean_dec_ref_known(v_defValue_360_, 1);
v___x_374_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_dec_ref_known(v___x_374_, 1);
v_inst_330_ = v___x_306_;
v_inst_331_ = v___x_307_;
v_inst_332_ = v___x_308_;
v___y_333_ = v_a_287_;
v___y_334_ = v_a_288_;
v___y_335_ = v_a_289_;
v___y_336_ = v_a_290_;
v___y_337_ = v_a_291_;
v___y_338_ = v_a_292_;
goto v___jp_329_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_optName_328_);
lean_dec(v_value_310_);
lean_dec_ref(v_opts_285_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
case 3:
{
lean_object* v___x_383_; 
lean_dec_ref_known(v_defValue_360_, 1);
v___x_383_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_dec_ref_known(v___x_383_, 1);
v_inst_330_ = v___x_297_;
v_inst_331_ = v___x_298_;
v_inst_332_ = v___x_299_;
v___y_333_ = v_a_287_;
v___y_334_ = v_a_288_;
v___y_335_ = v_a_289_;
v___y_336_ = v_a_290_;
v___y_337_ = v_a_291_;
v___y_338_ = v_a_292_;
goto v___jp_329_;
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_optName_328_);
lean_dec(v_value_310_);
lean_dec_ref(v_opts_285_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
case 4:
{
lean_object* v___x_392_; 
lean_dec_ref_known(v_defValue_360_, 1);
v___x_392_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref_known(v___x_392_, 1);
v_inst_330_ = v___x_300_;
v_inst_331_ = v___x_301_;
v_inst_332_ = v___x_302_;
v___y_333_ = v_a_287_;
v___y_334_ = v_a_288_;
v___y_335_ = v_a_289_;
v___y_336_ = v_a_290_;
v___y_337_ = v_a_291_;
v___y_338_ = v_a_292_;
goto v___jp_329_;
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_optName_328_);
lean_dec(v_value_310_);
lean_dec_ref(v_opts_285_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
default: 
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_option_309_);
lean_dec_ref_known(v_defValue_360_, 1);
lean_dec(v_value_310_);
lean_dec_ref(v_item_286_);
lean_dec_ref(v_opts_285_);
v___x_401_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3);
v___x_402_ = l_Lean_MessageData_ofName(v_optName_328_);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_option_309_, v___x_405_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_option_309_);
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_optName_328_);
lean_dec(v_value_310_);
lean_dec_ref(v_item_286_);
lean_dec_ref(v_opts_285_);
v_a_408_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_422_ == 0)
{
v___x_410_ = v___x_357_;
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_357_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_ref_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v_ref_412_ = lean_ctor_get(v_a_291_, 5);
v___x_413_ = lean_io_error_to_string(v_a_408_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 3);
lean_ctor_set(v___x_325_, 0, v___x_413_);
v___x_415_ = v___x_325_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_421_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_416_ = l_Lean_MessageData_ofFormat(v___x_415_);
lean_inc(v_ref_412_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_ref_412_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_417_);
v___x_419_ = v___x_410_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
v___jp_329_:
{
lean_object* v___x_339_; 
lean_inc_ref(v_inst_331_);
lean_inc_ref(v_inst_330_);
v___x_339_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_330_, v_inst_331_, v_value_310_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
lean_inc_ref(v_inst_332_);
v___x_344_ = l_Lean_Options_set___redArg(v_inst_332_, v_opts_285_, v_optName_328_, v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_optName_328_);
lean_dec_ref(v_opts_285_);
v_a_349_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(lean_object* v_optionPrefix_425_, lean_object* v_opts_426_, lean_object* v_item_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(v_optionPrefix_425_, v_opts_426_, v_item_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(lean_object* v_t_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_436_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(lean_object* v_t_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(v_t_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_object* v_00_u03b1_454_, lean_object* v_ref_455_, lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_455_, v_msg_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(lean_object* v_00_u03b1_465_, lean_object* v_ref_466_, lean_object* v_msg_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(v_00_u03b1_465_, v_ref_466_, v_msg_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v_ref_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_object* v_00_u03b1_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(lean_object* v_00_u03b1_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(v_00_u03b1_486_, v_msg_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(lean_object* v_msgData_496_, lean_object* v_macroStack_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_496_, v_macroStack_497_, v___y_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_506_, lean_object* v_macroStack_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(v_msgData_506_, v_macroStack_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_515_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
