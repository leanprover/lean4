// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term public import Lean.Elab.Do.ForwardSyntax meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = ", numRegularExits: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ",\n    noFallthrough: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value)} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 75, 74, 17, 172, 74, 138, 206)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 182, 102, 169, 76, 87, 55, 254)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 65, 144, 138, 55, 55, 217, 220)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ControlInfoHandler"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 126, 127, 228, 104, 205, 61, 148)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "control info inference"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 238, .m_capacity = 238, .m_length = 235, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`."};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(119) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(127) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not a let or reassignment declaration: "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Not a catch or catch match: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doErasedArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value),LEAN_SCALAR_PTR_LITERAL(176, 216, 203, 158, 108, 103, 134, 112)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doErased"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_value),LEAN_SCALAR_PTR_LITERAL(69, 69, 120, 16, 133, 86, 56, 26)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__91_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__93_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; 
v___x_1_ = l_Lean_NameSet_empty;
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_3_ = 0;
v___x_4_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4_, 0, v___x_2_);
lean_ctor_set(v___x_4_, 1, v___x_1_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 1, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 2, v___x_3_);
lean_ctor_set_uint8(v___x_4_, sizeof(void*)*2 + 3, v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0(void){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; 
v___x_8_ = l_Lean_NameSet_empty;
v___x_9_ = 1;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = 0;
v___x_12_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_12_, 0, v___x_10_);
lean_ctor_set(v___x_12_, 1, v___x_8_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 1, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 2, v___x_11_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*2 + 3, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_empty(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_empty___closed__0, &l_Lean_Elab_Do_ControlInfo_empty___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_empty___closed__0);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* v_a_14_, lean_object* v_b_15_){
_start:
{
uint8_t v_breaks_16_; uint8_t v_continues_17_; uint8_t v_returnsEarly_18_; uint8_t v_noFallthrough_19_; lean_object* v_reassigns_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_52_; 
v_breaks_16_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2);
v_continues_17_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 1);
v_returnsEarly_18_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 2);
v_noFallthrough_19_ = lean_ctor_get_uint8(v_a_14_, sizeof(void*)*2 + 3);
v_reassigns_20_ = lean_ctor_get(v_a_14_, 1);
v_isSharedCheck_52_ = !lean_is_exclusive(v_a_14_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v_a_14_, 0);
lean_dec(v_unused_53_);
v___x_22_ = v_a_14_;
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_reassigns_20_);
lean_dec(v_a_14_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_52_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___y_25_; uint8_t v___y_26_; uint8_t v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
if (v_breaks_16_ == 0)
{
uint8_t v_breaks_51_; 
v_breaks_51_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2);
v___y_49_ = v_breaks_51_;
goto v___jp_48_;
}
else
{
v___y_49_ = v_breaks_16_;
goto v___jp_48_;
}
v___jp_24_:
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_28_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_29_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_29_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_27_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_26_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 2, v___y_25_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 3, v___y_30_);
return v___x_33_;
}
}
v___jp_35_:
{
if (v_noFallthrough_19_ == 0)
{
lean_object* v_numRegularExits_39_; uint8_t v_noFallthrough_40_; lean_object* v_reassigns_41_; 
v_numRegularExits_39_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_39_);
v_noFallthrough_40_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 3);
v_reassigns_41_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_41_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v___y_36_;
v___y_27_ = v___y_37_;
v___y_28_ = v_reassigns_41_;
v___y_29_ = v_numRegularExits_39_;
v___y_30_ = v_noFallthrough_40_;
goto v___jp_24_;
}
else
{
lean_object* v_numRegularExits_42_; lean_object* v_reassigns_43_; 
v_numRegularExits_42_ = lean_ctor_get(v_b_15_, 0);
lean_inc(v_numRegularExits_42_);
v_reassigns_43_ = lean_ctor_get(v_b_15_, 1);
lean_inc(v_reassigns_43_);
lean_dec_ref(v_b_15_);
v___y_25_ = v___y_38_;
v___y_26_ = v___y_36_;
v___y_27_ = v___y_37_;
v___y_28_ = v_reassigns_43_;
v___y_29_ = v_numRegularExits_42_;
v___y_30_ = v_noFallthrough_19_;
goto v___jp_24_;
}
}
v___jp_44_:
{
if (v_returnsEarly_18_ == 0)
{
uint8_t v_returnsEarly_47_; 
v_returnsEarly_47_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 2);
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_46_;
v___y_37_ = v___y_45_;
v___y_38_ = v_returnsEarly_18_;
goto v___jp_35_;
}
}
v___jp_48_:
{
if (v_continues_17_ == 0)
{
uint8_t v_continues_50_; 
v_continues_50_ = lean_ctor_get_uint8(v_b_15_, sizeof(void*)*2 + 1);
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_50_;
goto v___jp_44_;
}
else
{
v___y_45_ = v___y_49_;
v___y_46_ = v_continues_17_;
goto v___jp_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* v_a_54_, lean_object* v_b_55_){
_start:
{
uint8_t v___y_57_; lean_object* v___y_58_; uint8_t v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; uint8_t v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
v_breaks_66_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2);
v_continues_67_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 1);
v_returnsEarly_68_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 2);
v_numRegularExits_69_ = lean_ctor_get(v_a_54_, 0);
lean_inc(v_numRegularExits_69_);
v_noFallthrough_70_ = lean_ctor_get_uint8(v_a_54_, sizeof(void*)*2 + 3);
v_reassigns_71_ = lean_ctor_get(v_a_54_, 1);
lean_inc(v_reassigns_71_);
lean_dec_ref(v_a_54_);
if (v_breaks_66_ == 0)
{
uint8_t v_breaks_87_; 
v_breaks_87_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2);
v___y_85_ = v_breaks_87_;
goto v___jp_84_;
}
else
{
v___y_85_ = v_breaks_66_;
goto v___jp_84_;
}
v___jp_56_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_NameSet_append(v___y_58_, v___y_61_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_60_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_59_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_57_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_62_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 3, v___y_63_);
return v___x_65_;
}
v___jp_72_:
{
lean_object* v_numRegularExits_76_; uint8_t v_noFallthrough_77_; lean_object* v_reassigns_78_; lean_object* v___x_79_; 
v_numRegularExits_76_ = lean_ctor_get(v_b_55_, 0);
lean_inc(v_numRegularExits_76_);
v_noFallthrough_77_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 3);
v_reassigns_78_ = lean_ctor_get(v_b_55_, 1);
lean_inc(v_reassigns_78_);
lean_dec_ref(v_b_55_);
v___x_79_ = lean_nat_add(v_numRegularExits_69_, v_numRegularExits_76_);
lean_dec(v_numRegularExits_76_);
lean_dec(v_numRegularExits_69_);
if (v_noFallthrough_70_ == 0)
{
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_71_;
v___y_59_ = v___y_74_;
v___y_60_ = v___x_79_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___y_75_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_73_;
v___y_58_ = v_reassigns_71_;
v___y_59_ = v___y_74_;
v___y_60_ = v___x_79_;
v___y_61_ = v_reassigns_78_;
v___y_62_ = v___y_75_;
v___y_63_ = v_noFallthrough_77_;
goto v___jp_56_;
}
}
v___jp_80_:
{
if (v_returnsEarly_68_ == 0)
{
uint8_t v_returnsEarly_83_; 
v_returnsEarly_83_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 2);
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_83_;
goto v___jp_72_;
}
else
{
v___y_73_ = v___y_82_;
v___y_74_ = v___y_81_;
v___y_75_ = v_returnsEarly_68_;
goto v___jp_72_;
}
}
v___jp_84_:
{
if (v_continues_67_ == 0)
{
uint8_t v_continues_86_; 
v_continues_86_ = lean_ctor_get_uint8(v_b_55_, sizeof(void*)*2 + 1);
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_86_;
goto v___jp_80_;
}
else
{
v___y_81_ = v___y_85_;
v___y_82_ = v_continues_67_;
goto v___jp_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* v_x1_88_, lean_object* v_x2_89_, lean_object* v_x3_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x1_88_);
lean_ctor_set(v___x_91_, 1, v_x3_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
v___x_94_ = l_Lean_stringToMessageData(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
v___x_117_ = l_Lean_stringToMessageData(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
v___x_120_ = l_Lean_stringToMessageData(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
v___x_128_ = l_Lean_stringToMessageData(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__23));
v___x_131_ = l_Lean_stringToMessageData(v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* v___f_132_, lean_object* v_info_133_){
_start:
{
lean_object* v___y_135_; lean_object* v___y_136_; lean_object* v___y_137_; uint8_t v_breaks_150_; uint8_t v_continues_151_; uint8_t v_returnsEarly_152_; lean_object* v_numRegularExits_153_; uint8_t v_noFallthrough_154_; lean_object* v_reassigns_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___x_182_; lean_object* v___y_184_; 
v_breaks_150_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2);
v_continues_151_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 1);
v_returnsEarly_152_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 2);
v_numRegularExits_153_ = lean_ctor_get(v_info_133_, 0);
lean_inc(v_numRegularExits_153_);
v_noFallthrough_154_ = lean_ctor_get_uint8(v_info_133_, sizeof(void*)*2 + 3);
v_reassigns_155_ = lean_ctor_get(v_info_133_, 1);
lean_inc(v_reassigns_155_);
lean_dec_ref(v_info_133_);
v___x_182_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
if (v_breaks_150_ == 0)
{
lean_object* v___x_192_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_184_ = v___x_192_;
goto v___jp_183_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_184_ = v___x_193_;
goto v___jp_183_;
}
v___jp_134_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc_ref(v___y_137_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___y_137_);
v___x_139_ = l_Lean_MessageData_ofFormat(v___x_138_);
v___x_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_136_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
v___x_142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_box(0);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11));
v___x_145_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_144_, v___f_132_, v___x_143_, v___y_135_);
v___x_146_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12));
v___x_147_ = l_List_mapTR_loop___redArg(v___x_146_, v___x_145_, v___x_143_);
v___x_148_ = l_Lean_MessageData_ofList(v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_142_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
v___jp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_inc_ref(v___y_158_);
v___x_159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_159_, 0, v___y_158_);
v___x_160_ = l_Lean_MessageData_ofFormat(v___x_159_);
v___x_161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_161_, 0, v___y_157_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Nat_reprFast(v_numRegularExits_153_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = l_Lean_MessageData_ofFormat(v___x_165_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
if (v_noFallthrough_154_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_170_;
goto v___jp_134_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_135_ = v_reassigns_155_;
v___y_136_ = v___x_169_;
v___y_137_ = v___x_171_;
goto v___jp_134_;
}
}
v___jp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref(v___y_174_);
v___x_175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_175_, 0, v___y_174_);
v___x_176_ = l_Lean_MessageData_ofFormat(v___x_175_);
v___x_177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_177_, 0, v___y_173_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_returnsEarly_152_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_180_;
goto v___jp_156_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_157_ = v___x_179_;
v___y_158_ = v___x_181_;
goto v___jp_156_;
}
}
v___jp_183_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc_ref(v___y_184_);
v___x_185_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_185_, 0, v___y_184_);
v___x_186_ = l_Lean_MessageData_ofFormat(v___x_185_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_182_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__24);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
if (v_continues_151_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_190_;
goto v___jp_172_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
v___y_173_ = v___x_189_;
v___y_174_ = v___x_191_;
goto v___jp_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* v_ref_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
v___x_225_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
v___x_226_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
v___x_227_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
v___x_228_ = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
v___x_229_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_224_, v___x_225_, v___x_226_, v___x_227_, v___x_228_, v_ref_222_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* v_ref_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v_ref_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_241_ = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2____boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
v___x_248_ = l_Lean_addBuiltinDocString(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3(){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_));
v___x_278_ = ((lean_object*)(l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
v___x_279_ = l_Lean_addBuiltinDeclarationRanges(v___x_277_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; uint8_t v___x_290_; lean_object* v_env_291_; lean_object* v___x_292_; lean_object* v_toCold_293_; lean_object* v_mctx_294_; lean_object* v_lctx_295_; lean_object* v_options_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = 0;
v_env_291_ = l_Lean_Environment_setRecordingDeps(v_env_289_, v___x_290_);
v___x_292_ = lean_st_ref_get(v___y_284_);
v_toCold_293_ = lean_ctor_get(v___y_285_, 0);
v_mctx_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc_ref(v_mctx_294_);
lean_dec(v___x_292_);
v_lctx_295_ = lean_ctor_get(v___y_283_, 2);
v_options_296_ = lean_ctor_get(v_toCold_293_, 2);
lean_inc_ref(v_options_296_);
lean_inc_ref(v_lctx_295_);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v_env_291_);
lean_ctor_set(v___x_297_, 1, v_mctx_294_);
lean_ctor_set(v___x_297_, 2, v_lctx_295_);
lean_ctor_set(v___x_297_, 3, v_options_296_);
v___x_298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v_msgData_282_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_box(1);
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
return v_x_314_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_339_; 
v_head_316_ = lean_ctor_get(v_x_315_, 0);
v_tail_317_ = lean_ctor_get(v_x_315_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_339_ == 0)
{
v___x_319_ = v_x_315_;
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_head_316_);
lean_dec(v_x_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_339_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_before_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_337_; 
v_before_321_ = lean_ctor_get(v_head_316_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_head_316_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_head_316_, 1);
lean_dec(v_unused_338_);
v___x_323_ = v_head_316_;
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_before_321_);
lean_dec(v_head_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_324_ == 0)
{
lean_ctor_set_tag(v___x_323_, 7);
lean_ctor_set(v___x_323_, 1, v___x_325_);
lean_ctor_set(v___x_323_, 0, v_x_314_);
v___x_327_ = v___x_323_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_x_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_336_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 7);
lean_ctor_set(v___x_319_, 1, v___x_328_);
lean_ctor_set(v___x_319_, 0, v___x_327_);
v___x_330_ = v___x_319_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_335_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = l_Lean_MessageData_ofSyntax(v_before_321_);
v___x_332_ = l_Lean_indentD(v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v_x_314_ = v___x_333_;
v_x_315_ = v_tail_317_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_340_, lean_object* v_opt_341_){
_start:
{
lean_object* v_name_342_; lean_object* v_defValue_343_; lean_object* v_map_344_; lean_object* v___x_345_; 
v_name_342_ = lean_ctor_get(v_opt_341_, 0);
v_defValue_343_ = lean_ctor_get(v_opt_341_, 1);
v_map_344_ = lean_ctor_get(v_opts_340_, 0);
v___x_345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_344_, v_name_342_);
if (lean_obj_tag(v___x_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = lean_unbox(v_defValue_343_);
return v___x_346_;
}
else
{
lean_object* v_val_347_; 
v_val_347_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v___x_345_, 1);
if (lean_obj_tag(v_val_347_) == 1)
{
uint8_t v_v_348_; 
v_v_348_ = lean_ctor_get_uint8(v_val_347_, 0);
lean_dec_ref_known(v_val_347_, 0);
return v_v_348_;
}
else
{
uint8_t v___x_349_; 
lean_dec(v_val_347_);
v___x_349_ = lean_unbox(v_defValue_343_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_350_, lean_object* v_opt_351_){
_start:
{
uint8_t v_res_352_; lean_object* v_r_353_; 
v_res_352_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_350_, v_opt_351_);
lean_dec_ref(v_opt_351_);
lean_dec_ref(v_opts_350_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_358_ = l_Lean_MessageData_ofFormat(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_359_, lean_object* v_macroStack_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_361_);
v___x_364_ = l_Lean_Elab_pp_macroStack;
v___x_365_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v___x_363_, v___x_364_);
lean_dec_ref(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_macroStack_360_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_359_);
return v___x_366_;
}
else
{
if (lean_obj_tag(v_macroStack_360_) == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_msgData_359_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_after_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_384_; 
v_head_368_ = lean_ctor_get(v_macroStack_360_, 0);
lean_inc(v_head_368_);
v_after_369_ = lean_ctor_get(v_head_368_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_head_368_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v_head_368_, 0);
lean_dec(v_unused_385_);
v___x_371_ = v_head_368_;
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_after_369_);
lean_dec(v_head_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_384_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 7);
lean_ctor_set(v___x_371_, 1, v___x_373_);
lean_ctor_set(v___x_371_, 0, v_msgData_359_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_msgData_359_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_383_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_msgData_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_MessageData_ofSyntax(v_after_369_);
v___x_379_ = l_Lean_indentD(v___x_378_);
v_msgData_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_380_, 0, v___x_377_);
lean_ctor_set(v_msgData_380_, 1, v___x_379_);
v___x_381_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_380_, v_macroStack_360_);
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_386_, lean_object* v_macroStack_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_386_, v_macroStack_387_, v___y_388_);
lean_dec_ref(v___y_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_ref_399_; lean_object* v_macroStack_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_413_; 
v_ref_399_ = lean_ctor_get(v___y_396_, 2);
v_macroStack_400_ = lean_ctor_get(v___y_392_, 1);
v___x_401_ = l_Lean_Elab_getBetterRef(v_ref_399_, v_macroStack_400_);
v___x_402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_391_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
lean_inc(v_macroStack_400_);
v___x_404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_403_, v_macroStack_400_, v___y_396_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_413_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_413_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_401_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v___x_409_);
v___x_411_ = v___x_407_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_423_, size_t v_i_424_, size_t v_stop_425_, lean_object* v_b_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_eq(v_i_424_, v_stop_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; size_t v___x_430_; size_t v___x_431_; 
v___x_428_ = lean_array_uget_borrowed(v_as_423_, v_i_424_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_NameSet_insert(v_b_426_, v___x_428_);
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_424_, v___x_430_);
v_i_424_ = v___x_431_;
v_b_426_ = v___x_429_;
goto _start;
}
else
{
return v_b_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_433_, lean_object* v_i_434_, lean_object* v_stop_435_, lean_object* v_b_436_){
_start:
{
size_t v_i_boxed_437_; size_t v_stop_boxed_438_; lean_object* v_res_439_; 
v_i_boxed_437_ = lean_unbox_usize(v_i_434_);
lean_dec(v_i_434_);
v_stop_boxed_438_ = lean_unbox_usize(v_stop_435_);
lean_dec(v_stop_435_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_433_, v_i_boxed_437_, v_stop_boxed_438_, v_b_436_);
lean_dec_ref(v_as_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
return v_bs_442_;
}
else
{
lean_object* v_v_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget(v_bs_442_, v_i_441_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_445_);
v___x_447_ = l_Lean_TSyntax_getId(v_v_444_);
lean_dec(v_v_444_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_446_, v_i_441_, v___x_447_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_466_, size_t v_i_467_, lean_object* v_bs_468_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_467_, v_sz_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v_bs_468_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v_bs_x27_472_; lean_object* v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v_bs_x27_472_ = lean_array_uset(v_bs_468_, v_i_467_, v___x_471_);
v___x_473_ = lean_box(0);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_467_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_472_, v_i_467_, v___x_473_);
v_i_467_ = v___x_475_;
v_bs_468_ = v___x_476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_478_, lean_object* v_i_479_, lean_object* v_bs_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_478_);
lean_dec(v_sz_478_);
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_481_, v_i_boxed_482_, v_bs_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_484_, uint8_t v___x_485_, lean_object* v_as_486_, size_t v_i_487_, size_t v_stop_488_, lean_object* v_b_489_){
_start:
{
lean_object* v___y_491_; uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_487_, v_stop_488_);
if (v___x_495_ == 0)
{
lean_object* v_fst_496_; uint8_t v___x_497_; 
v_fst_496_ = lean_ctor_get(v_b_489_, 0);
v___x_497_ = lean_unbox(v_fst_496_);
if (v___x_497_ == 0)
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_snd_498_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_507_);
v___x_500_ = v_b_489_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_b_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_box(v___x_484_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_snd_498_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v___y_491_ = v___x_504_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_snd_508_ = lean_ctor_get(v_b_489_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_b_489_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_b_489_, 0);
lean_dec(v_unused_519_);
v___x_510_ = v_b_489_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_dec(v_b_489_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = lean_array_uget_borrowed(v_as_486_, v_i_487_);
lean_inc(v___x_512_);
v___x_513_ = lean_array_push(v_snd_508_, v___x_512_);
v___x_514_ = lean_box(v___x_485_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_513_);
lean_ctor_set(v___x_510_, 0, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_513_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
}
}
}
else
{
return v_b_489_;
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_487_, v___x_492_);
v_i_487_ = v___x_493_;
v_b_489_ = v___y_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_as_522_, lean_object* v_i_523_, lean_object* v_stop_524_, lean_object* v_b_525_){
_start:
{
uint8_t v___x_175826__boxed_526_; uint8_t v___x_175827__boxed_527_; size_t v_i_boxed_528_; size_t v_stop_boxed_529_; lean_object* v_res_530_; 
v___x_175826__boxed_526_ = lean_unbox(v___x_520_);
v___x_175827__boxed_527_ = lean_unbox(v___x_521_);
v_i_boxed_528_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_stop_boxed_529_ = lean_unbox_usize(v_stop_524_);
lean_dec(v_stop_524_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_175826__boxed_526_, v___x_175827__boxed_527_, v_as_522_, v_i_boxed_528_, v_stop_boxed_529_, v_b_525_);
lean_dec_ref(v_as_522_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_531_, lean_object* v___y_532_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
v_a_533_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_533_);
v___x_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_534_, 0, v_a_533_);
lean_ctor_set(v___x_534_, 1, v___y_532_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; 
v_a_535_ = lean_ctor_get(v_x_531_, 0);
lean_inc(v_a_535_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_a_535_);
lean_ctor_set(v___x_536_, 1, v___y_532_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_537_, v___y_538_);
lean_dec_ref(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_540_, lean_object* v_stx_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_540_, v_stx_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
v_a_546_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v___x_544_, 0);
lean_dec(v_unused_555_);
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_546_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_584_; 
v_val_556_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_584_ == 0)
{
v___x_558_ = v_a_545_;
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_a_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_584_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_snd_560_; 
v_snd_560_ = lean_ctor_get(v_val_556_, 1);
lean_inc(v_snd_560_);
lean_dec(v_val_556_);
if (lean_obj_tag(v_snd_560_) == 0)
{
lean_object* v_a_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
lean_del_object(v___x_558_);
v_a_561_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_544_, 2);
v_a_562_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_snd_560_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_snd_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_567_, v_a_561_);
lean_dec_ref(v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_583_; 
v_a_571_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_544_, 2);
v_a_572_ = lean_ctor_get(v_snd_560_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_560_);
if (v_isSharedCheck_583_ == 0)
{
v___x_574_ = v_snd_560_;
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v_snd_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_583_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v_a_572_);
v___x_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_582_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_581_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; 
v___x_580_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_579_, v_a_571_);
lean_dec_ref(v___x_579_);
return v___x_580_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_544_, 0);
v_a_586_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_544_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_544_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_594_, lean_object* v_stx_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_594_, v_stx_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_maxRecDepthErrorMessage;
v___x_605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_607_ = l_Lean_MessageData_ofFormat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_609_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_610_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_ref_611_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_619_, lean_object* v_declName_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_623_; lean_object* v_env_624_; lean_object* v___x_625_; uint8_t v___x_626_; uint8_t v___x_627_; 
v___x_623_ = 0;
v_env_624_ = l_Lean_Environment_setExporting(v_env_619_, v___x_623_);
lean_inc(v_declName_620_);
v___x_625_ = l_Lean_mkPrivateName(v_env_624_, v_declName_620_);
v___x_626_ = 1;
lean_inc_ref(v_env_624_);
v___x_627_ = l_Lean_Environment_contains(v_env_624_, v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_privateToUserName(v_declName_620_);
v___x_629_ = l_Lean_Environment_contains(v_env_624_, v___x_628_, v___x_626_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_622_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_env_624_);
lean_dec(v_declName_620_);
v___x_632_ = lean_box(v___x_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___y_622_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_634_, lean_object* v_declName_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_634_, v_declName_635_, v___y_636_, v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_639_, lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_toCold_648_; lean_object* v_currRecDepth_649_; lean_object* v_ref_650_; uint16_t v_optionFlags_651_; uint8_t v_suppressElabErrors_652_; uint8_t v_isRecordingDeps_653_; lean_object* v_ref_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_toCold_648_ = lean_ctor_get(v___y_645_, 0);
v_currRecDepth_649_ = lean_ctor_get(v___y_645_, 1);
v_ref_650_ = lean_ctor_get(v___y_645_, 2);
v_optionFlags_651_ = lean_ctor_get_uint16(v___y_645_, sizeof(void*)*3);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 2);
v_isRecordingDeps_653_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 3);
v_ref_654_ = l_Lean_replaceRef(v_ref_639_, v_ref_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_toCold_648_);
v___x_655_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_655_, 0, v_toCold_648_);
lean_ctor_set(v___x_655_, 1, v_currRecDepth_649_);
lean_ctor_set(v___x_655_, 2, v_ref_654_);
lean_ctor_set_uint16(v___x_655_, sizeof(void*)*3, v_optionFlags_651_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 2, v_suppressElabErrors_652_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*3 + 3, v_isRecordingDeps_653_);
v___x_656_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___x_655_, v___y_646_);
lean_dec_ref_known(v___x_655_, 3);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_657_, v_msg_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_ref_657_);
return v_res_666_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_667_; double v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_float_of_nat(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_ref_679_; lean_object* v___x_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_726_; 
v_ref_679_ = lean_ctor_get(v___y_676_, 2);
v___x_680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_726_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v_traceState_686_; lean_object* v_env_687_; lean_object* v_nextMacroScope_688_; lean_object* v_ngen_689_; lean_object* v_auxDeclNGen_690_; lean_object* v_cache_691_; lean_object* v_recordedDeps_692_; lean_object* v_messages_693_; lean_object* v_infoState_694_; lean_object* v_snapshotTasks_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_725_; 
v___x_685_ = lean_st_ref_take(v___y_677_);
v_traceState_686_ = lean_ctor_get(v___x_685_, 4);
v_env_687_ = lean_ctor_get(v___x_685_, 0);
v_nextMacroScope_688_ = lean_ctor_get(v___x_685_, 1);
v_ngen_689_ = lean_ctor_get(v___x_685_, 2);
v_auxDeclNGen_690_ = lean_ctor_get(v___x_685_, 3);
v_cache_691_ = lean_ctor_get(v___x_685_, 5);
v_recordedDeps_692_ = lean_ctor_get(v___x_685_, 6);
v_messages_693_ = lean_ctor_get(v___x_685_, 7);
v_infoState_694_ = lean_ctor_get(v___x_685_, 8);
v_snapshotTasks_695_ = lean_ctor_get(v___x_685_, 9);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_725_ == 0)
{
v___x_697_ = v___x_685_;
v_isShared_698_ = v_isSharedCheck_725_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snapshotTasks_695_);
lean_inc(v_infoState_694_);
lean_inc(v_messages_693_);
lean_inc(v_recordedDeps_692_);
lean_inc(v_cache_691_);
lean_inc(v_traceState_686_);
lean_inc(v_auxDeclNGen_690_);
lean_inc(v_ngen_689_);
lean_inc(v_nextMacroScope_688_);
lean_inc(v_env_687_);
lean_dec(v___x_685_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_725_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
uint64_t v_tid_699_; lean_object* v_traces_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_724_; 
v_tid_699_ = lean_ctor_get_uint64(v_traceState_686_, sizeof(void*)*1);
v_traces_700_ = lean_ctor_get(v_traceState_686_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_traceState_686_);
if (v_isSharedCheck_724_ == 0)
{
v___x_702_ = v_traceState_686_;
v_isShared_703_ = v_isSharedCheck_724_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_traces_700_);
lean_dec(v_traceState_686_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_724_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; double v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_box(0);
v___x_706_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_707_ = 0;
v___x_708_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_709_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_709_, 0, v_cls_672_);
lean_ctor_set(v___x_709_, 1, v___x_705_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
lean_ctor_set_float(v___x_709_, sizeof(void*)*3, v___x_706_);
lean_ctor_set_float(v___x_709_, sizeof(void*)*3 + 8, v___x_706_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*3 + 16, v___x_707_);
v___x_710_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_711_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v_a_681_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
lean_inc(v_ref_679_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_ref_679_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_PersistentArray_push___redArg(v_traces_700_, v___x_712_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_713_);
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_713_);
lean_ctor_set_uint64(v_reuseFailAlloc_723_, sizeof(void*)*1, v_tid_699_);
v___x_715_ = v_reuseFailAlloc_723_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 4, v___x_715_);
v___x_717_ = v___x_697_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_env_687_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_nextMacroScope_688_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_ngen_689_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_auxDeclNGen_690_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_cache_691_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v_recordedDeps_692_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_messages_693_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v_infoState_694_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_snapshotTasks_695_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_st_ref_put(v___y_677_, v___x_717_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_704_);
v___x_720_ = v___x_683_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_704_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_727_, v_msg_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
if (lean_obj_tag(v_as_738_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v_toCold_748_; lean_object* v_options_749_; uint8_t v_hasTrace_750_; 
v_toCold_748_ = lean_ctor_get(v___y_743_, 0);
v_options_749_ = lean_ctor_get(v_toCold_748_, 2);
v_hasTrace_750_ = lean_ctor_get_uint8(v_options_749_, sizeof(void*)*1);
if (v_hasTrace_750_ == 0)
{
lean_object* v_tail_751_; 
v_tail_751_ = lean_ctor_get(v_as_738_, 1);
lean_inc(v_tail_751_);
lean_dec_ref_known(v_as_738_, 2);
v_as_738_ = v_tail_751_;
goto _start;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v_inheritedTraceOptions_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_head_753_ = lean_ctor_get(v_as_738_, 0);
lean_inc(v_head_753_);
v_tail_754_ = lean_ctor_get(v_as_738_, 1);
lean_inc(v_tail_754_);
lean_dec_ref_known(v_as_738_, 2);
v_fst_755_ = lean_ctor_get(v_head_753_, 0);
lean_inc_n(v_fst_755_, 2);
v_snd_756_ = lean_ctor_get(v_head_753_, 1);
lean_inc(v_snd_756_);
lean_dec(v_head_753_);
v_inheritedTraceOptions_757_ = lean_ctor_get(v_toCold_748_, 11);
v___x_758_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_759_ = l_Lean_Name_append(v___x_758_, v_fst_755_);
v___x_760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_757_, v_options_749_, v___x_759_);
lean_dec(v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_snd_756_);
lean_dec(v_fst_755_);
v_as_738_ = v_tail_754_;
goto _start;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_762_, 0, v_snd_756_);
v___x_763_ = l_Lean_MessageData_ofFormat(v___x_762_);
v___x_764_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_755_, v___x_763_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec_ref_known(v___x_764_, 1);
v_as_738_ = v_tail_754_;
goto _start;
}
else
{
lean_dec(v_tail_754_);
return v___x_764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
else
{
lean_object* v_key_778_; lean_object* v_value_779_; lean_object* v_tail_780_; uint8_t v___x_781_; 
v_key_778_ = lean_ctor_get(v_x_776_, 0);
v_value_779_ = lean_ctor_get(v_x_776_, 1);
v_tail_780_ = lean_ctor_get(v_x_776_, 2);
v___x_781_ = lean_name_eq(v_key_778_, v_a_775_);
if (v___x_781_ == 0)
{
v_x_776_ = v_tail_780_;
goto _start;
}
else
{
lean_object* v___x_783_; 
lean_inc(v_value_779_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v_value_779_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_784_, v_x_785_);
lean_dec(v_x_785_);
lean_dec(v_a_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_buckets_789_; lean_object* v___x_790_; uint64_t v___y_792_; 
v_buckets_789_ = lean_ctor_get(v_m_787_, 1);
v___x_790_ = lean_array_get_size(v_buckets_789_);
if (lean_obj_tag(v_a_788_) == 0)
{
uint64_t v___x_806_; 
v___x_806_ = 1723ULL;
v___y_792_ = v___x_806_;
goto v___jp_791_;
}
else
{
uint64_t v_hash_807_; 
v_hash_807_ = lean_ctor_get_uint64(v_a_788_, sizeof(void*)*2);
v___y_792_ = v_hash_807_;
goto v___jp_791_;
}
v___jp_791_:
{
uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v_fold_795_; uint64_t v___x_796_; uint64_t v___x_797_; uint64_t v___x_798_; size_t v___x_799_; size_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_793_ = 32ULL;
v___x_794_ = lean_uint64_shift_right(v___y_792_, v___x_793_);
v_fold_795_ = lean_uint64_xor(v___y_792_, v___x_794_);
v___x_796_ = 16ULL;
v___x_797_ = lean_uint64_shift_right(v_fold_795_, v___x_796_);
v___x_798_ = lean_uint64_xor(v_fold_795_, v___x_797_);
v___x_799_ = lean_uint64_to_usize(v___x_798_);
v___x_800_ = lean_usize_of_nat(v___x_790_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_sub(v___x_800_, v___x_801_);
v___x_803_ = lean_usize_land(v___x_799_, v___x_802_);
v___x_804_ = lean_array_uget_borrowed(v_buckets_789_, v___x_803_);
v___x_805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_788_, v___x_804_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_m_808_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0(lean_object* v___x_811_, lean_object* v_entry_812_, lean_object* v_s_813_){
_start:
{
lean_object* v_addEntryFn_814_; lean_object* v_importedEntries_815_; lean_object* v_state_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_addEntryFn_814_ = lean_ctor_get(v___x_811_, 3);
lean_inc(v_addEntryFn_814_);
lean_dec_ref(v___x_811_);
v_importedEntries_815_ = lean_ctor_get(v_s_813_, 0);
v_state_816_ = lean_ctor_get(v_s_813_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_s_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_s_813_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_state_816_);
lean_inc(v_importedEntries_815_);
lean_dec(v_s_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_state_820_; lean_object* v___x_822_; 
v_state_820_ = lean_apply_2(v_addEntryFn_814_, v_state_816_, v_entry_812_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v_state_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_importedEntries_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_state_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_825_, lean_object* v_i_826_, lean_object* v_k_827_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_array_get_size(v_keys_825_);
v___x_829_ = lean_nat_dec_lt(v_i_826_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_i_826_);
return v___x_829_;
}
else
{
lean_object* v_k_x27_830_; uint8_t v___x_831_; 
v_k_x27_830_ = lean_array_fget_borrowed(v_keys_825_, v_i_826_);
v___x_831_ = l_Lean_instBEqExtraModUse_beq(v_k_827_, v_k_x27_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_add(v_i_826_, v___x_832_);
lean_dec(v_i_826_);
v_i_826_ = v___x_833_;
goto _start;
}
else
{
lean_dec(v_i_826_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_835_, lean_object* v_i_836_, lean_object* v_k_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_835_, v_i_836_, v_k_837_);
lean_dec_ref(v_k_837_);
lean_dec_ref(v_keys_835_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_840_, size_t v_x_841_, lean_object* v_x_842_){
_start:
{
if (lean_obj_tag(v_x_840_) == 0)
{
lean_object* v_es_843_; lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v_j_847_; lean_object* v___x_848_; 
v_es_843_ = lean_ctor_get(v_x_840_, 0);
v___x_844_ = lean_box(2);
v___x_845_ = ((size_t)31ULL);
v___x_846_ = lean_usize_land(v_x_841_, v___x_845_);
v_j_847_ = lean_usize_to_nat(v___x_846_);
v___x_848_ = lean_array_get_borrowed(v___x_844_, v_es_843_, v_j_847_);
lean_dec(v_j_847_);
switch(lean_obj_tag(v___x_848_))
{
case 0:
{
lean_object* v_key_849_; uint8_t v___x_850_; 
v_key_849_ = lean_ctor_get(v___x_848_, 0);
v___x_850_ = l_Lean_instBEqExtraModUse_beq(v_x_842_, v_key_849_);
return v___x_850_;
}
case 1:
{
lean_object* v_node_851_; size_t v___x_852_; size_t v___x_853_; 
v_node_851_ = lean_ctor_get(v___x_848_, 0);
v___x_852_ = ((size_t)5ULL);
v___x_853_ = lean_usize_shift_right(v_x_841_, v___x_852_);
v_x_840_ = v_node_851_;
v_x_841_ = v___x_853_;
goto _start;
}
default: 
{
uint8_t v___x_855_; 
v___x_855_ = 0;
return v___x_855_;
}
}
}
else
{
lean_object* v_ks_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_ks_856_ = lean_ctor_get(v_x_840_, 0);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_856_, v___x_857_, v_x_842_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
size_t v_x_176354__boxed_862_; uint8_t v_res_863_; lean_object* v_r_864_; 
v_x_176354__boxed_862_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_863_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_859_, v_x_176354__boxed_862_, v_x_861_);
lean_dec_ref(v_x_861_);
lean_dec_ref(v_x_859_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
uint64_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v___x_867_ = l_Lean_instHashableExtraModUse_hash(v_x_866_);
v___x_868_ = lean_uint64_to_usize(v___x_867_);
v___x_869_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_865_, v___x_868_, v_x_866_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_870_, v_x_871_);
lean_dec_ref(v_x_871_);
lean_dec_ref(v_x_870_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_880_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
lean_ctor_set(v___x_880_, 3, v___x_879_);
lean_ctor_set(v___x_880_, 4, v___x_879_);
lean_ctor_set(v___x_880_, 5, v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_cls_893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_894_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_895_ = l_Lean_Name_append(v___x_894_, v_cls_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_898_ = l_Lean_stringToMessageData(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_906_, uint8_t v_isMeta_907_, lean_object* v_hint_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_env_950_; uint8_t v_isExporting_951_; lean_object* v_entry_952_; lean_object* v___x_953_; lean_object* v_env_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_948_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_949_ = lean_st_ref_get(v___y_914_);
v_env_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc_ref(v_env_950_);
lean_dec(v___x_949_);
v_isExporting_951_ = lean_ctor_get_uint8(v_env_950_, sizeof(void*)*13);
lean_dec_ref(v_env_950_);
lean_inc(v_mod_906_);
v_entry_952_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_952_, 0, v_mod_906_);
lean_ctor_set_uint8(v_entry_952_, sizeof(void*)*1, v_isExporting_951_);
lean_ctor_set_uint8(v_entry_952_, sizeof(void*)*1 + 1, v_isMeta_907_);
v___x_953_ = lean_st_ref_get(v___y_914_);
v_env_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc_ref(v_env_954_);
lean_dec(v___x_953_);
v___x_955_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_956_ = lean_box(1);
v___x_957_ = lean_box(0);
v___x_958_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_948_, v___x_955_, v_env_954_, v___x_956_, v___x_957_);
v___x_959_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_958_, v_entry_952_);
lean_dec(v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v_toCold_960_; lean_object* v_options_961_; lean_object* v_inheritedTraceOptions_962_; uint8_t v_hasTrace_963_; lean_object* v___f_964_; uint8_t v___x_965_; lean_object* v___y_967_; lean_object* v___y_968_; 
v_toCold_960_ = lean_ctor_get(v___y_913_, 0);
v_options_961_ = lean_ctor_get(v_toCold_960_, 2);
v_inheritedTraceOptions_962_ = lean_ctor_get(v_toCold_960_, 11);
v_hasTrace_963_ = lean_ctor_get_uint8(v_options_961_, sizeof(void*)*1);
v___f_964_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___lam__0), 3, 2);
lean_closure_set(v___f_964_, 0, v___x_955_);
lean_closure_set(v___f_964_, 1, v_entry_952_);
v___x_965_ = 1;
if (v_hasTrace_963_ == 0)
{
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_object* v_cls_995_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_cls_995_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_1015_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_1016_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_962_, v_options_961_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_object* v___x_1017_; lean_object* v___y_1019_; 
v___x_1017_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_951_ == 0)
{
lean_object* v___x_1026_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_1019_ = v___x_1026_;
goto v___jp_1018_;
}
else
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_1019_ = v___x_1027_;
goto v___jp_1018_;
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_inc_ref(v___y_1019_);
v___x_1020_ = l_Lean_stringToMessageData(v___y_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1017_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
if (v_isMeta_907_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_1002_ = v___x_1023_;
v___y_1003_ = v___x_1024_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_1002_ = v___x_1023_;
v___y_1003_ = v___x_1025_;
goto v___jp_1001_;
}
}
}
v___jp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___y_997_);
lean_ctor_set(v___x_999_, 1, v___y_998_);
v___x_1000_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_995_, v___x_999_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_dec_ref_known(v___x_1000_, 1);
v___y_967_ = v___y_912_;
v___y_968_ = v___y_914_;
goto v___jp_966_;
}
else
{
lean_dec_ref(v___f_964_);
return v___x_1000_;
}
}
v___jp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
lean_inc_ref(v___y_1003_);
v___x_1004_ = l_Lean_stringToMessageData(v___y_1003_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_MessageData_ofName(v_mod_906_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_Name_isAnonymous(v_hint_908_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_1012_ = l_Lean_MessageData_ofName(v_hint_908_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___y_997_ = v___x_1009_;
v___y_998_ = v___x_1013_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1014_; 
lean_dec(v_hint_908_);
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_997_ = v___x_1009_;
v___y_998_ = v___x_1014_;
goto v___jp_996_;
}
}
}
v___jp_966_:
{
lean_object* v___x_969_; lean_object* v_toEnvExtension_970_; uint8_t v_logWrites_971_; 
v___x_969_ = lean_st_ref_take(v___y_968_);
v_toEnvExtension_970_ = lean_ctor_get(v___x_955_, 0);
v_logWrites_971_ = lean_ctor_get_uint8(v_toEnvExtension_970_, sizeof(void*)*6);
if (v_logWrites_971_ == 0)
{
lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_recordedDeps_977_; lean_object* v_messages_978_; lean_object* v_infoState_979_; lean_object* v_snapshotTasks_980_; lean_object* v_asyncMode_981_; lean_object* v___x_982_; 
v_env_972_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_972_);
v_nextMacroScope_973_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_nextMacroScope_973_);
v_ngen_974_ = lean_ctor_get(v___x_969_, 2);
lean_inc_ref(v_ngen_974_);
v_auxDeclNGen_975_ = lean_ctor_get(v___x_969_, 3);
lean_inc_ref(v_auxDeclNGen_975_);
v_traceState_976_ = lean_ctor_get(v___x_969_, 4);
lean_inc_ref(v_traceState_976_);
v_recordedDeps_977_ = lean_ctor_get(v___x_969_, 6);
lean_inc_ref(v_recordedDeps_977_);
v_messages_978_ = lean_ctor_get(v___x_969_, 7);
lean_inc_ref(v_messages_978_);
v_infoState_979_ = lean_ctor_get(v___x_969_, 8);
lean_inc_ref(v_infoState_979_);
v_snapshotTasks_980_ = lean_ctor_get(v___x_969_, 9);
lean_inc_ref(v_snapshotTasks_980_);
lean_dec(v___x_969_);
v_asyncMode_981_ = lean_ctor_get(v_toEnvExtension_970_, 2);
lean_inc_ref(v_toEnvExtension_970_);
v___x_982_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_970_, v_env_972_, v___f_964_, v_asyncMode_981_, v___x_957_, v___x_965_);
v___y_917_ = v_auxDeclNGen_975_;
v___y_918_ = v_recordedDeps_977_;
v___y_919_ = v_nextMacroScope_973_;
v___y_920_ = v_messages_978_;
v___y_921_ = v_infoState_979_;
v___y_922_ = v___y_967_;
v___y_923_ = v_snapshotTasks_980_;
v___y_924_ = v___y_968_;
v___y_925_ = v_ngen_974_;
v___y_926_ = v_traceState_976_;
v___y_927_ = v___x_982_;
goto v___jp_916_;
}
else
{
lean_object* v_env_983_; lean_object* v_nextMacroScope_984_; lean_object* v_ngen_985_; lean_object* v_auxDeclNGen_986_; lean_object* v_traceState_987_; lean_object* v_recordedDeps_988_; lean_object* v_messages_989_; lean_object* v_infoState_990_; lean_object* v_snapshotTasks_991_; lean_object* v_asyncMode_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_env_983_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_983_);
v_nextMacroScope_984_ = lean_ctor_get(v___x_969_, 1);
lean_inc(v_nextMacroScope_984_);
v_ngen_985_ = lean_ctor_get(v___x_969_, 2);
lean_inc_ref(v_ngen_985_);
v_auxDeclNGen_986_ = lean_ctor_get(v___x_969_, 3);
lean_inc_ref(v_auxDeclNGen_986_);
v_traceState_987_ = lean_ctor_get(v___x_969_, 4);
lean_inc_ref(v_traceState_987_);
v_recordedDeps_988_ = lean_ctor_get(v___x_969_, 6);
lean_inc_ref(v_recordedDeps_988_);
v_messages_989_ = lean_ctor_get(v___x_969_, 7);
lean_inc_ref(v_messages_989_);
v_infoState_990_ = lean_ctor_get(v___x_969_, 8);
lean_inc_ref(v_infoState_990_);
v_snapshotTasks_991_ = lean_ctor_get(v___x_969_, 9);
lean_inc_ref(v_snapshotTasks_991_);
lean_dec(v___x_969_);
v_asyncMode_992_ = lean_ctor_get(v_toEnvExtension_970_, 2);
lean_inc_ref_n(v_toEnvExtension_970_, 2);
v___x_993_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_970_, v_env_983_);
lean_dec_ref(v_env_983_);
v___x_994_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_970_, v___x_993_, v___f_964_, v_asyncMode_992_, v___x_957_, v___x_965_);
v___y_917_ = v_auxDeclNGen_986_;
v___y_918_ = v_recordedDeps_988_;
v___y_919_ = v_nextMacroScope_984_;
v___y_920_ = v_messages_989_;
v___y_921_ = v_infoState_990_;
v___y_922_ = v___y_967_;
v___y_923_ = v_snapshotTasks_991_;
v___y_924_ = v___y_968_;
v___y_925_ = v_ngen_985_;
v___y_926_ = v_traceState_987_;
v___y_927_ = v___x_994_;
goto v___jp_916_;
}
}
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref_known(v_entry_952_, 1);
lean_dec(v_hint_908_);
lean_dec(v_mod_906_);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
v___jp_916_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_mctx_932_; lean_object* v_zetaDeltaFVarIds_933_; lean_object* v_postponed_934_; lean_object* v_diag_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v___x_928_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_929_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_929_, 0, v___y_927_);
lean_ctor_set(v___x_929_, 1, v___y_919_);
lean_ctor_set(v___x_929_, 2, v___y_925_);
lean_ctor_set(v___x_929_, 3, v___y_917_);
lean_ctor_set(v___x_929_, 4, v___y_926_);
lean_ctor_set(v___x_929_, 5, v___x_928_);
lean_ctor_set(v___x_929_, 6, v___y_918_);
lean_ctor_set(v___x_929_, 7, v___y_920_);
lean_ctor_set(v___x_929_, 8, v___y_921_);
lean_ctor_set(v___x_929_, 9, v___y_923_);
v___x_930_ = lean_st_ref_put(v___y_924_, v___x_929_);
v___x_931_ = lean_st_ref_take(v___y_922_);
v_mctx_932_ = lean_ctor_get(v___x_931_, 0);
v_zetaDeltaFVarIds_933_ = lean_ctor_get(v___x_931_, 2);
v_postponed_934_ = lean_ctor_get(v___x_931_, 3);
v_diag_935_ = lean_ctor_get(v___x_931_, 4);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_931_, 1);
lean_dec(v_unused_947_);
v___x_937_ = v___x_931_;
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_diag_935_);
lean_inc(v_postponed_934_);
lean_inc(v_zetaDeltaFVarIds_933_);
lean_inc(v_mctx_932_);
lean_dec(v___x_931_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_946_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_939_ = lean_box(0);
v___x_940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_mctx_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_zetaDeltaFVarIds_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_postponed_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_diag_935_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v___y_922_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1030_, lean_object* v_isMeta_1031_, lean_object* v_hint_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_isMeta_boxed_1040_; lean_object* v_res_1041_; 
v_isMeta_boxed_1040_ = lean_unbox(v_isMeta_1031_);
v_res_1041_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1030_, v_isMeta_boxed_1040_, v_hint_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1042_, lean_object* v_declName_1043_, lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_declName_1043_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_b_1047_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v_modules_1058_; lean_object* v___x_1059_; lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v_toImport_1062_; lean_object* v_module_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
v___x_1057_ = l_Lean_Environment_header(v___x_1042_);
v_modules_1058_ = lean_ctor_get(v___x_1057_, 3);
lean_inc_ref(v_modules_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1060_ = lean_array_uget_borrowed(v_as_1044_, v_i_1046_);
v___x_1061_ = lean_array_get(v___x_1059_, v_modules_1058_, v_a_1060_);
lean_dec_ref(v_modules_1058_);
v_toImport_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_toImport_1062_);
lean_dec(v___x_1061_);
v_module_1063_ = lean_ctor_get(v_toImport_1062_, 0);
lean_inc(v_module_1063_);
lean_dec_ref(v_toImport_1062_);
v___x_1064_ = lean_box(0);
v___x_1065_ = 0;
lean_inc(v_declName_1043_);
v___x_1066_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1063_, v___x_1065_, v_declName_1043_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1066_) == 0)
{
size_t v___x_1067_; size_t v___x_1068_; 
lean_dec_ref_known(v___x_1066_, 1);
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1046_, v___x_1067_);
v_i_1046_ = v___x_1068_;
v_b_1047_ = v___x_1064_;
goto _start;
}
else
{
lean_dec(v_declName_1043_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1070_, lean_object* v_declName_1071_, lean_object* v_as_1072_, lean_object* v_sz_1073_, lean_object* v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
size_t v_sz_boxed_1083_; size_t v_i_boxed_1084_; lean_object* v_res_1085_; 
v_sz_boxed_1083_ = lean_unbox_usize(v_sz_1073_);
lean_dec(v_sz_1073_);
v_i_boxed_1084_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1070_, v_declName_1071_, v_as_1072_, v_sz_boxed_1083_, v_i_boxed_1084_, v_b_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_as_1072_);
lean_dec_ref(v___x_1070_);
return v_res_1085_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1089_, uint8_t v_isMeta_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v_env_1103_; lean_object* v___y_1105_; lean_object* v___x_1118_; 
v___x_1098_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1099_ = lean_st_ref_get(v___y_1096_);
v_env_1103_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1099_);
v___x_1118_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1103_, v_declName_1089_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
goto v___jp_1100_;
}
else
{
lean_object* v_val_1119_; lean_object* v___x_1120_; lean_object* v_modules_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_val_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l_Lean_Environment_header(v_env_1103_);
v_modules_1121_ = lean_ctor_get(v___x_1120_, 3);
lean_inc_ref(v_modules_1121_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = lean_array_get_size(v_modules_1121_);
v___x_1123_ = lean_nat_dec_lt(v_val_1119_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v_modules_1121_);
lean_dec(v_val_1119_);
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
goto v___jp_1100_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___y_1127_; 
v___x_1124_ = lean_array_fget(v_modules_1121_, v_val_1119_);
lean_dec(v_val_1119_);
lean_dec_ref(v_modules_1121_);
v___x_1125_ = lean_st_ref_get(v___y_1096_);
if (v_isMeta_1090_ == 0)
{
lean_dec(v___x_1125_);
v___y_1127_ = v_isMeta_1090_;
goto v___jp_1126_;
}
else
{
lean_object* v_env_1138_; uint8_t v___x_1139_; 
v_env_1138_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1138_);
lean_dec(v___x_1125_);
lean_inc(v_declName_1089_);
v___x_1139_ = l_Lean_isMarkedMeta(v_env_1138_, v_declName_1089_);
if (v___x_1139_ == 0)
{
v___y_1127_ = v_isMeta_1090_;
goto v___jp_1126_;
}
else
{
uint8_t v___x_1140_; 
v___x_1140_ = 0;
v___y_1127_ = v___x_1140_;
goto v___jp_1126_;
}
}
v___jp_1126_:
{
lean_object* v_toImport_1128_; lean_object* v_module_1129_; lean_object* v___x_1130_; 
v_toImport_1128_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_toImport_1128_);
lean_dec(v___x_1124_);
v_module_1129_ = lean_ctor_get(v_toImport_1128_, 0);
lean_inc(v_module_1129_);
lean_dec_ref(v_toImport_1128_);
lean_inc(v_declName_1089_);
v___x_1130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1129_, v___y_1127_, v_declName_1089_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1130_, 1);
v___x_1131_ = l_Lean_indirectModUseExt;
v___x_1132_ = lean_box(1);
v___x_1133_ = lean_box(0);
lean_inc_ref(v_env_1103_);
v___x_1134_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1098_, v___x_1131_, v_env_1103_, v___x_1132_, v___x_1133_);
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1134_, v_declName_1089_);
lean_dec(v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1105_ = v___x_1136_;
goto v___jp_1104_;
}
else
{
lean_object* v_val_1137_; 
v_val_1137_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1137_);
lean_dec_ref_known(v___x_1135_, 1);
v___y_1105_ = v_val_1137_;
goto v___jp_1104_;
}
}
else
{
lean_dec_ref(v_env_1103_);
lean_dec(v_declName_1089_);
return v___x_1130_;
}
}
}
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; size_t v_sz_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = lean_box(0);
v_sz_1107_ = lean_array_size(v___y_1105_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1103_, v_declName_1089_, v___y_1105_, v_sz_1107_, v___x_1108_, v___x_1106_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec_ref(v___y_1105_);
lean_dec_ref(v_env_1103_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v___x_1109_, 0);
lean_dec(v_unused_1117_);
v___x_1111_ = v___x_1109_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_dec(v___x_1109_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1106_);
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1106_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1141_, lean_object* v_isMeta_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_isMeta_boxed_1150_; lean_object* v_res_1151_; 
v_isMeta_boxed_1150_ = lean_unbox(v_isMeta_1142_);
v_res_1151_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1141_, v_isMeta_boxed_1150_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
if (lean_obj_tag(v_as_x27_1152_) == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1153_);
return v___x_1161_;
}
else
{
lean_object* v_head_1162_; lean_object* v_tail_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; 
v_head_1162_ = lean_ctor_get(v_as_x27_1152_, 0);
v_tail_1163_ = lean_ctor_get(v_as_x27_1152_, 1);
v___x_1164_ = lean_box(0);
v___x_1165_ = 1;
lean_inc(v_head_1162_);
v___x_1166_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1162_, v___x_1165_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_dec_ref_known(v___x_1166_, 1);
v_as_x27_1152_ = v_tail_1163_;
v_b_1153_ = v___x_1164_;
goto _start;
}
else
{
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1168_, v_b_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v_as_x27_1168_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_currNamespace_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_currNamespace_1178_);
lean_ctor_set(v___x_1181_, 1, v___y_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_currNamespace_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_env_1186_, lean_object* v___x_1187_, lean_object* v_currNamespace_1188_, lean_object* v_openDecls_1189_, lean_object* v_n_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_ResolveName_resolveGlobalName(v_env_1186_, v___x_1187_, v_currNamespace_1188_, v_openDecls_1189_, v_n_1190_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___y_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_env_1195_, lean_object* v___x_1196_, lean_object* v_currNamespace_1197_, lean_object* v_openDecls_1198_, lean_object* v_n_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_env_1195_, v___x_1196_, v_currNamespace_1197_, v_openDecls_1198_, v_n_1199_, v___y_1200_, v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec_ref(v___x_1196_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1203_, lean_object* v_currNamespace_1204_, lean_object* v_openDecls_1205_, lean_object* v_n_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = l_Lean_ResolveName_resolveNamespace(v_env_1203_, v_currNamespace_1204_, v_openDecls_1205_, v_n_1206_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1211_, lean_object* v_currNamespace_1212_, lean_object* v_openDecls_1213_, lean_object* v_n_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1211_, v_currNamespace_1212_, v_openDecls_1213_, v_n_1214_, v___y_1215_, v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; lean_object* v_toCold_1228_; lean_object* v_env_1229_; lean_object* v_currRecDepth_1230_; lean_object* v_ref_1231_; lean_object* v_maxRecDepth_1232_; lean_object* v_currNamespace_1233_; lean_object* v_openDecls_1234_; lean_object* v_quotContext_1235_; lean_object* v_currMacroScope_1236_; lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v_methods_1243_; lean_object* v___x_1244_; lean_object* v_nextMacroScope_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1227_ = lean_st_ref_get(v___y_1225_);
v_toCold_1228_ = lean_ctor_get(v___y_1224_, 0);
v_env_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc_ref_n(v_env_1229_, 4);
lean_dec(v___x_1227_);
v_currRecDepth_1230_ = lean_ctor_get(v___y_1224_, 1);
v_ref_1231_ = lean_ctor_get(v___y_1224_, 2);
v_maxRecDepth_1232_ = lean_ctor_get(v_toCold_1228_, 3);
v_currNamespace_1233_ = lean_ctor_get(v_toCold_1228_, 4);
v_openDecls_1234_ = lean_ctor_get(v_toCold_1228_, 5);
v_quotContext_1235_ = lean_ctor_get(v_toCold_1228_, 8);
v_currMacroScope_1236_ = lean_ctor_get(v_toCold_1228_, 9);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1237_, 0, v_env_1229_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1238_, 0, v_env_1229_);
v___x_1239_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1224_);
lean_inc_n(v_currNamespace_1233_, 3);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1240_, 0, v_currNamespace_1233_);
lean_inc_n(v_openDecls_1234_, 2);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1241_, 0, v_env_1229_);
lean_closure_set(v___f_1241_, 1, v___x_1239_);
lean_closure_set(v___f_1241_, 2, v_currNamespace_1233_);
lean_closure_set(v___f_1241_, 3, v_openDecls_1234_);
v___f_1242_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1242_, 0, v_env_1229_);
lean_closure_set(v___f_1242_, 1, v_currNamespace_1233_);
lean_closure_set(v___f_1242_, 2, v_openDecls_1234_);
v_methods_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1243_, 0, v___f_1238_);
lean_ctor_set(v_methods_1243_, 1, v___f_1240_);
lean_ctor_set(v_methods_1243_, 2, v___f_1237_);
lean_ctor_set(v_methods_1243_, 3, v___f_1242_);
lean_ctor_set(v_methods_1243_, 4, v___f_1241_);
v___x_1244_ = lean_st_ref_get(v___y_1225_);
v_nextMacroScope_1245_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_nextMacroScope_1245_);
lean_dec(v___x_1244_);
lean_inc(v_ref_1231_);
lean_inc(v_maxRecDepth_1232_);
lean_inc(v_currRecDepth_1230_);
lean_inc(v_currMacroScope_1236_);
lean_inc(v_quotContext_1235_);
v___x_1246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1246_, 0, v_methods_1243_);
lean_ctor_set(v___x_1246_, 1, v_quotContext_1235_);
lean_ctor_set(v___x_1246_, 2, v_currMacroScope_1236_);
lean_ctor_set(v___x_1246_, 3, v_currRecDepth_1230_);
lean_ctor_set(v___x_1246_, 4, v_maxRecDepth_1232_);
lean_ctor_set(v___x_1246_, 5, v_ref_1231_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_nextMacroScope_1245_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_ctor_set(v___x_1248_, 2, v___x_1247_);
v___x_1249_ = lean_apply_2(v_x_1219_, v___x_1246_, v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v_a_1251_; lean_object* v_macroScope_1252_; lean_object* v_traceMsgs_1253_; lean_object* v_expandedMacroDecls_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_a_1250_);
v_a_1251_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1249_, 2);
v_macroScope_1252_ = lean_ctor_get(v_a_1250_, 0);
lean_inc(v_macroScope_1252_);
v_traceMsgs_1253_ = lean_ctor_get(v_a_1250_, 1);
lean_inc(v_traceMsgs_1253_);
v_expandedMacroDecls_1254_ = lean_ctor_get(v_a_1250_, 2);
lean_inc(v_expandedMacroDecls_1254_);
lean_dec(v_a_1250_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1254_, v___x_1255_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v_expandedMacroDecls_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v_env_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_traceState_1261_; lean_object* v_cache_1262_; lean_object* v_recordedDeps_1263_; lean_object* v_messages_1264_; lean_object* v_infoState_1265_; lean_object* v_snapshotTasks_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref_known(v___x_1256_, 1);
v___x_1257_ = lean_st_ref_take(v___y_1225_);
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
v_ngen_1259_ = lean_ctor_get(v___x_1257_, 2);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1257_, 3);
v_traceState_1261_ = lean_ctor_get(v___x_1257_, 4);
v_cache_1262_ = lean_ctor_get(v___x_1257_, 5);
v_recordedDeps_1263_ = lean_ctor_get(v___x_1257_, 6);
v_messages_1264_ = lean_ctor_get(v___x_1257_, 7);
v_infoState_1265_ = lean_ctor_get(v___x_1257_, 8);
v_snapshotTasks_1266_ = lean_ctor_get(v___x_1257_, 9);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1257_, 1);
lean_dec(v_unused_1293_);
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snapshotTasks_1266_);
lean_inc(v_infoState_1265_);
lean_inc(v_messages_1264_);
lean_inc(v_recordedDeps_1263_);
lean_inc(v_cache_1262_);
lean_inc(v_traceState_1261_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_env_1258_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1292_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_macroScope_1252_);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_env_1258_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_macroScope_1252_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_traceState_1261_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v_cache_1262_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_recordedDeps_1263_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_messages_1264_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_infoState_1265_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v_snapshotTasks_1266_);
v___x_1271_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_st_ref_put(v___y_1225_, v___x_1271_);
v___x_1273_ = l_List_reverse___redArg(v_traceMsgs_1253_);
v___x_1274_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1273_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1274_, 0);
lean_dec(v_unused_1282_);
v___x_1276_ = v___x_1274_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___x_1274_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_a_1251_);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1251_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1251_);
v_a_1283_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1274_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1274_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_traceMsgs_1253_);
lean_dec(v_macroScope_1252_);
lean_dec(v_a_1251_);
v_a_1294_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1256_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1256_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1249_, 2);
if (lean_obj_tag(v_a_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1303_ = lean_ctor_get(v_a_1302_, 0);
lean_inc(v_a_1303_);
v_a_1304_ = lean_ctor_get(v_a_1302_, 1);
lean_inc_ref(v_a_1304_);
lean_dec_ref_known(v_a_1302_, 2);
v___x_1305_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1306_ = lean_string_dec_eq(v_a_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1304_);
v___x_1308_ = l_Lean_MessageData_ofFormat(v___x_1307_);
v___x_1309_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1303_, v___x_1308_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec(v_a_1303_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref(v_a_1304_);
v___x_1310_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1303_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_bs_1326_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1325_, v_sz_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_bs_1326_);
return v___x_1328_;
}
else
{
lean_object* v_v_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_v_1329_ = lean_array_uget(v_bs_1326_, v_i_1325_);
v___x_1330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1329_);
v___x_1331_ = l_Lean_Syntax_isOfKind(v_v_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v_v_1329_);
lean_dec_ref(v_bs_1326_);
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1333_);
v___x_1335_ = l_Lean_Syntax_isOfKind(v___x_1334_, v___x_1330_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec(v_v_1329_);
lean_dec_ref(v_bs_1326_);
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
else
{
lean_object* v___x_1337_; lean_object* v_bs_x27_1338_; lean_object* v___x_1339_; size_t v___x_1340_; size_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = lean_unsigned_to_nat(3u);
v_bs_x27_1338_ = lean_array_uset(v_bs_1326_, v_i_1325_, v___x_1333_);
v___x_1339_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1337_);
lean_dec(v_v_1329_);
v___x_1340_ = ((size_t)1ULL);
v___x_1341_ = lean_usize_add(v_i_1325_, v___x_1340_);
v___x_1342_ = lean_array_uset(v_bs_x27_1338_, v_i_1325_, v___x_1339_);
v_i_1325_ = v___x_1341_;
v_bs_1326_ = v___x_1342_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1344_, lean_object* v_i_1345_, lean_object* v_bs_1346_){
_start:
{
size_t v_sz_boxed_1347_; size_t v_i_boxed_1348_; lean_object* v_res_1349_; 
v_sz_boxed_1347_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v_i_boxed_1348_ = lean_unbox_usize(v_i_1345_);
lean_dec(v_i_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1347_, v_i_boxed_1348_, v_bs_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t v___x_1362_, size_t v_sz_1363_, size_t v_i_1364_, lean_object* v_bs_1365_){
_start:
{
uint8_t v___x_1366_; 
v___x_1366_ = lean_usize_dec_lt(v_i_1364_, v_sz_1363_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1367_, 0, v_bs_1365_);
return v___x_1367_;
}
else
{
lean_object* v_v_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_v_1368_ = lean_array_uget(v_bs_1365_, v_i_1364_);
v___x_1369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1368_);
v___x_1370_ = l_Lean_Syntax_isOfKind(v_v_1368_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec(v_v_1368_);
lean_dec_ref(v_bs_1365_);
v___x_1371_ = lean_box(0);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_bs_x27_1374_; 
v___x_1372_ = lean_unsigned_to_nat(3u);
v___x_1373_ = lean_unsigned_to_nat(0u);
v_bs_x27_1374_ = lean_array_uset(v_bs_1365_, v_i_1364_, v___x_1373_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = l_Lean_Syntax_getArg(v_v_1368_, v___x_1381_);
v___x_1383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1384_ = l_Lean_Syntax_isOfKind(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec_ref(v_bs_x27_1374_);
lean_dec(v_v_1368_);
v___x_1385_ = lean_box(0);
return v___x_1385_;
}
else
{
goto v___jp_1375_;
}
}
else
{
goto v___jp_1375_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = l_Lean_Syntax_getArg(v_v_1368_, v___x_1372_);
lean_dec(v_v_1368_);
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1364_, v___x_1377_);
v___x_1379_ = lean_array_uset(v_bs_x27_1374_, v_i_1364_, v___x_1376_);
v_i_1364_ = v___x_1378_;
v_bs_1365_ = v___x_1379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v___x_1386_, lean_object* v_sz_1387_, lean_object* v_i_1388_, lean_object* v_bs_1389_){
_start:
{
uint8_t v___x_177141__boxed_1390_; size_t v_sz_boxed_1391_; size_t v_i_boxed_1392_; lean_object* v_res_1393_; 
v___x_177141__boxed_1390_ = lean_unbox(v___x_1386_);
v_sz_boxed_1391_ = lean_unbox_usize(v_sz_1387_);
lean_dec(v_sz_1387_);
v_i_boxed_1392_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_177141__boxed_1390_, v_sz_boxed_1391_, v_i_boxed_1392_, v_bs_1389_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1400_, size_t v_i_1401_, lean_object* v_bs_1402_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_usize_dec_lt(v_i_1401_, v_sz_1400_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_bs_1402_);
return v___x_1404_;
}
else
{
lean_object* v_v_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_v_1405_ = lean_array_uget(v_bs_1402_, v_i_1401_);
v___x_1406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1405_);
v___x_1407_ = l_Lean_Syntax_isOfKind(v_v_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec(v_v_1405_);
lean_dec_ref(v_bs_1402_);
v___x_1408_ = lean_box(0);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v_bs_x27_1410_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v_bs_x27_1410_ = lean_array_uset(v_bs_1402_, v_i_1401_, v___x_1409_);
v___x_1417_ = l_Lean_Syntax_getArg(v_v_1405_, v___x_1409_);
lean_dec(v_v_1405_);
v___x_1418_ = l_Lean_Syntax_isNone(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1419_ = lean_unsigned_to_nat(2u);
v___x_1420_ = l_Lean_Syntax_matchesNull(v___x_1417_, v___x_1419_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_bs_x27_1410_);
v___x_1421_ = lean_box(0);
return v___x_1421_;
}
else
{
goto v___jp_1411_;
}
}
else
{
lean_dec(v___x_1417_);
goto v___jp_1411_;
}
v___jp_1411_:
{
lean_object* v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1401_, v___x_1413_);
v___x_1415_ = lean_array_uset(v_bs_x27_1410_, v_i_1401_, v___x_1412_);
v_i_1401_ = v___x_1414_;
v_bs_1402_ = v___x_1415_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1422_, lean_object* v_i_1423_, lean_object* v_bs_1424_){
_start:
{
size_t v_sz_boxed_1425_; size_t v_i_boxed_1426_; lean_object* v_res_1427_; 
v_sz_boxed_1425_ = lean_unbox_usize(v_sz_1422_);
lean_dec(v_sz_1422_);
v_i_boxed_1426_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1425_, v_i_boxed_1426_, v_bs_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1428_, size_t v_i_1429_, lean_object* v_bs_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_usize_dec_lt(v_i_1429_, v_sz_1428_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_bs_1430_);
return v___x_1432_;
}
else
{
lean_object* v_v_1433_; lean_object* v___x_1434_; lean_object* v_bs_x27_1435_; size_t v___x_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v_v_1433_ = lean_array_uget(v_bs_1430_, v_i_1429_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v_bs_x27_1435_ = lean_array_uset(v_bs_1430_, v_i_1429_, v___x_1434_);
v___x_1436_ = ((size_t)1ULL);
v___x_1437_ = lean_usize_add(v_i_1429_, v___x_1436_);
v___x_1438_ = lean_array_uset(v_bs_x27_1435_, v_i_1429_, v_v_1433_);
v_i_1429_ = v___x_1437_;
v_bs_1430_ = v___x_1438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1440_, lean_object* v_i_1441_, lean_object* v_bs_1442_){
_start:
{
size_t v_sz_boxed_1443_; size_t v_i_boxed_1444_; lean_object* v_res_1445_; 
v_sz_boxed_1443_ = lean_unbox_usize(v_sz_1440_);
lean_dec(v_sz_1440_);
v_i_boxed_1444_ = lean_unbox_usize(v_i_1441_);
lean_dec(v_i_1441_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1443_, v_i_boxed_1444_, v_bs_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1447_, v___y_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1451_, v_x_1452_, v___y_1453_, v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_x_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1459_, lean_object* v_as_x27_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
if (lean_obj_tag(v_as_x27_1460_) == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_stx_1459_);
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1461_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_tail_1471_; lean_object* v_value_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v_b_1461_);
v_head_1470_ = lean_ctor_get(v_as_x27_1460_, 0);
v_tail_1471_ = lean_ctor_get(v_as_x27_1460_, 1);
v_value_1472_ = lean_ctor_get(v_head_1470_, 1);
v___x_1473_ = lean_box(0);
v___x_1474_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1475_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1472_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v_stx_1459_);
v___x_1476_ = lean_apply_8(v_value_1472_, v_stx_1459_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, lean_box(0));
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_stx_1459_);
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1479_ = v___x_1476_;
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1477_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1473_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1482_);
v___x_1484_ = v___x_1479_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1507_; 
v_a_1487_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1489_ = v___x_1476_;
v_isShared_1490_ = v_isSharedCheck_1507_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1476_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1507_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
uint8_t v___y_1492_; uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_Exception_isInterrupt(v_a_1487_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
lean_inc(v_a_1487_);
v___x_1506_ = l_Lean_Exception_isRuntime(v_a_1487_);
v___y_1492_ = v___x_1506_;
goto v___jp_1491_;
}
else
{
v___y_1492_ = v___x_1505_;
goto v___jp_1491_;
}
v___jp_1491_:
{
if (v___y_1492_ == 0)
{
if (lean_obj_tag(v_a_1487_) == 0)
{
lean_object* v___x_1494_; 
lean_dec(v_stx_1459_);
if (v_isShared_1490_ == 0)
{
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1487_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
else
{
lean_object* v_id_1496_; uint8_t v___x_1497_; 
v_id_1496_ = lean_ctor_get(v_a_1487_, 0);
v___x_1497_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1475_, v_id_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1499_; 
lean_dec(v_stx_1459_);
if (v_isShared_1490_ == 0)
{
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1487_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
lean_dec_ref_known(v_a_1487_, 2);
lean_del_object(v___x_1489_);
v_as_x27_1460_ = v_tail_1471_;
v_b_1461_ = v___x_1474_;
goto _start;
}
}
}
else
{
lean_object* v___x_1503_; 
lean_dec(v_stx_1459_);
if (v_isShared_1490_ == 0)
{
v___x_1503_ = v___x_1489_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1487_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1508_, lean_object* v_as_x27_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1508_, v_as_x27_1509_, v_b_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_as_x27_1509_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1521_, lean_object* v_rhs_x3f_1522_, lean_object* v_otherwise_x3f_1523_, lean_object* v_body_x3f_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
uint8_t v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; uint8_t v___y_1536_; uint8_t v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v_body_1544_; lean_object* v___y_1565_; lean_object* v_otherwise_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v_rhs_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; 
if (lean_obj_tag(v_rhs_x3f_1522_) == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1578_ = v___x_1589_;
v___y_1579_ = v_a_1525_;
v___y_1580_ = v_a_1526_;
v___y_1581_ = v_a_1527_;
v___y_1582_ = v_a_1528_;
v___y_1583_ = v_a_1529_;
v___y_1584_ = v_a_1530_;
goto v___jp_1577_;
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1591_; 
v_val_1590_ = lean_ctor_get(v_rhs_x3f_1522_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v_rhs_x3f_1522_, 1);
v___x_1591_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1590_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_rhs_1578_ = v_a_1592_;
v___y_1579_ = v_a_1525_;
v___y_1580_ = v_a_1526_;
v___y_1581_ = v_a_1527_;
v___y_1582_ = v_a_1528_;
v___y_1583_ = v_a_1529_;
v___y_1584_ = v_a_1530_;
goto v___jp_1577_;
}
else
{
lean_dec(v_body_x3f_1524_);
lean_dec(v_otherwise_x3f_1523_);
lean_dec_ref(v_reassigned_1521_);
return v___x_1591_;
}
}
v___jp_1532_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1539_, 0, v___y_1535_);
lean_ctor_set(v___x_1539_, 1, v___y_1538_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*2, v___y_1536_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*2 + 1, v___y_1537_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*2 + 2, v___y_1533_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*2 + 3, v___y_1534_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
return v___x_1540_;
}
v___jp_1541_:
{
lean_object* v___x_1545_; lean_object* v_info_1546_; uint8_t v_breaks_1547_; uint8_t v_continues_1548_; uint8_t v_returnsEarly_1549_; lean_object* v_numRegularExits_1550_; uint8_t v_noFallthrough_1551_; lean_object* v_reassigns_1552_; size_t v_sz_1553_; size_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1545_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1544_, v___y_1542_);
v_info_1546_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1543_, v___x_1545_);
v_breaks_1547_ = lean_ctor_get_uint8(v_info_1546_, sizeof(void*)*2);
v_continues_1548_ = lean_ctor_get_uint8(v_info_1546_, sizeof(void*)*2 + 1);
v_returnsEarly_1549_ = lean_ctor_get_uint8(v_info_1546_, sizeof(void*)*2 + 2);
v_numRegularExits_1550_ = lean_ctor_get(v_info_1546_, 0);
lean_inc(v_numRegularExits_1550_);
v_noFallthrough_1551_ = lean_ctor_get_uint8(v_info_1546_, sizeof(void*)*2 + 3);
v_reassigns_1552_ = lean_ctor_get(v_info_1546_, 1);
lean_inc(v_reassigns_1552_);
lean_dec_ref(v_info_1546_);
v_sz_1553_ = lean_array_size(v_reassigned_1521_);
v___x_1554_ = ((size_t)0ULL);
v___x_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1553_, v___x_1554_, v_reassigned_1521_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_array_get_size(v___x_1555_);
v___x_1558_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v___x_1555_);
v___y_1533_ = v_returnsEarly_1549_;
v___y_1534_ = v_noFallthrough_1551_;
v___y_1535_ = v_numRegularExits_1550_;
v___y_1536_ = v_breaks_1547_;
v___y_1537_ = v_continues_1548_;
v___y_1538_ = v_reassigns_1552_;
goto v___jp_1532_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1559_ == 0)
{
if (v___x_1558_ == 0)
{
lean_dec_ref(v___x_1555_);
v___y_1533_ = v_returnsEarly_1549_;
v___y_1534_ = v_noFallthrough_1551_;
v___y_1535_ = v_numRegularExits_1550_;
v___y_1536_ = v_breaks_1547_;
v___y_1537_ = v_continues_1548_;
v___y_1538_ = v_reassigns_1552_;
goto v___jp_1532_;
}
else
{
size_t v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_usize_of_nat(v___x_1557_);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1555_, v___x_1554_, v___x_1560_, v_reassigns_1552_);
lean_dec_ref(v___x_1555_);
v___y_1533_ = v_returnsEarly_1549_;
v___y_1534_ = v_noFallthrough_1551_;
v___y_1535_ = v_numRegularExits_1550_;
v___y_1536_ = v_breaks_1547_;
v___y_1537_ = v_continues_1548_;
v___y_1538_ = v___x_1561_;
goto v___jp_1532_;
}
}
else
{
size_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_usize_of_nat(v___x_1557_);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1555_, v___x_1554_, v___x_1562_, v_reassigns_1552_);
lean_dec_ref(v___x_1555_);
v___y_1533_ = v_returnsEarly_1549_;
v___y_1534_ = v_noFallthrough_1551_;
v___y_1535_ = v_numRegularExits_1550_;
v___y_1536_ = v_breaks_1547_;
v___y_1537_ = v_continues_1548_;
v___y_1538_ = v___x_1563_;
goto v___jp_1532_;
}
}
}
v___jp_1564_:
{
if (lean_obj_tag(v_body_x3f_1524_) == 0)
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1542_ = v_otherwise_1566_;
v___y_1543_ = v___y_1565_;
v_body_1544_ = v___x_1573_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1574_; lean_object* v___x_1575_; 
v_val_1574_ = lean_ctor_get(v_body_x3f_1524_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_body_x3f_1524_, 1);
v___x_1575_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1574_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___y_1542_ = v_otherwise_1566_;
v___y_1543_ = v___y_1565_;
v_body_1544_ = v_a_1576_;
goto v___jp_1541_;
}
else
{
lean_dec_ref(v_otherwise_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v_reassigned_1521_);
return v___x_1575_;
}
}
}
v___jp_1577_:
{
if (lean_obj_tag(v_otherwise_x3f_1523_) == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1565_ = v_rhs_1578_;
v_otherwise_1566_ = v___x_1585_;
v___y_1567_ = v___y_1579_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1582_;
v___y_1571_ = v___y_1583_;
v___y_1572_ = v___y_1584_;
goto v___jp_1564_;
}
else
{
lean_object* v_val_1586_; lean_object* v___x_1587_; 
v_val_1586_ = lean_ctor_get(v_otherwise_x3f_1523_, 0);
lean_inc(v_val_1586_);
lean_dec_ref_known(v_otherwise_x3f_1523_, 1);
v___x_1587_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1586_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___y_1565_ = v_rhs_1578_;
v_otherwise_1566_ = v_a_1588_;
v___y_1567_ = v___y_1579_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1582_;
v___y_1571_ = v___y_1583_;
v___y_1572_ = v___y_1584_;
goto v___jp_1564_;
}
else
{
lean_dec_ref(v_rhs_1578_);
lean_dec(v_body_x3f_1524_);
lean_dec_ref(v_reassigned_1521_);
return v___x_1587_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1695_, lean_object* v_decl_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v_reassigns_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1696_);
v___x_1733_ = l_Lean_Syntax_isOfKind(v_decl_1696_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1696_);
v___x_1735_ = l_Lean_Syntax_isOfKind(v_decl_1696_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1736_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1737_ = lean_box(0);
v___x_1738_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1737_, v___x_1735_);
v___x_1739_ = l_Std_Format_defWidth;
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = l_Std_Format_pretty(v___x_1738_, v___x_1739_, v___x_1740_, v___x_1740_);
v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1736_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1743_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1744_;
}
else
{
lean_object* v___x_1745_; lean_object* v_pattern_1746_; lean_object* v___y_1748_; lean_object* v_otherwise_x3f_1749_; lean_object* v_body_x3f_x3f_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v_body_x3f_x3f_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___x_1780_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1745_ = lean_unsigned_to_nat(0u);
v_pattern_1746_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1745_);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1819_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1780_);
v___x_1820_ = l_Lean_Syntax_isNone(v___x_1819_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
lean_inc(v___x_1819_);
v___x_1821_ = l_Lean_Syntax_matchesNull(v___x_1819_, v___x_1780_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v___x_1819_);
lean_dec(v_pattern_1746_);
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1823_, v___x_1821_);
v___x_1825_ = l_Std_Format_defWidth;
v___x_1826_ = l_Std_Format_pretty(v___x_1824_, v___x_1825_, v___x_1745_, v___x_1745_);
v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1822_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1828_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = l_Lean_Syntax_getArg(v___x_1819_, v___x_1745_);
lean_dec(v___x_1819_);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1832_ = l_Lean_Syntax_isOfKind(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec(v_pattern_1746_);
v___x_1833_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1834_ = lean_box(0);
v___x_1835_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1834_, v___x_1832_);
v___x_1836_ = l_Std_Format_defWidth;
v___x_1837_ = l_Std_Format_pretty(v___x_1835_, v___x_1836_, v___x_1745_, v___x_1745_);
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1833_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1839_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1840_;
}
else
{
v___y_1782_ = v_a_1697_;
v___y_1783_ = v_a_1698_;
v___y_1784_ = v_a_1699_;
v___y_1785_ = v_a_1700_;
v___y_1786_ = v_a_1701_;
v___y_1787_ = v_a_1702_;
goto v___jp_1781_;
}
}
}
else
{
lean_dec(v___x_1819_);
v___y_1782_ = v_a_1697_;
v___y_1783_ = v_a_1698_;
v___y_1784_ = v_a_1699_;
v___y_1785_ = v_a_1700_;
v___y_1786_ = v_a_1701_;
v___y_1787_ = v_a_1702_;
goto v___jp_1781_;
}
v___jp_1747_:
{
if (v_reassignment_1695_ == 0)
{
lean_object* v___x_1757_; 
lean_dec(v_pattern_1746_);
v___x_1757_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1717_ = v_body_x3f_x3f_1750_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v_otherwise_x3f_1749_;
v_reassigns_1720_ = v___x_1757_;
v___y_1721_ = v___y_1751_;
v___y_1722_ = v___y_1752_;
v___y_1723_ = v___y_1753_;
v___y_1724_ = v___y_1754_;
v___y_1725_ = v___y_1755_;
v___y_1726_ = v___y_1756_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1746_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___y_1717_ = v_body_x3f_x3f_1750_;
v___y_1718_ = v___y_1748_;
v___y_1719_ = v_otherwise_x3f_1749_;
v_reassigns_1720_ = v_a_1759_;
v___y_1721_ = v___y_1751_;
v___y_1722_ = v___y_1752_;
v___y_1723_ = v___y_1753_;
v___y_1724_ = v___y_1754_;
v___y_1725_ = v___y_1755_;
v___y_1726_ = v___y_1756_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_body_x3f_x3f_1750_);
lean_dec(v_otherwise_x3f_1749_);
lean_dec(v___y_1748_);
v_a_1760_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1758_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
v___jp_1768_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___y_1770_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_body_x3f_x3f_1771_);
v___y_1748_ = v___y_1769_;
v_otherwise_x3f_1749_ = v___x_1778_;
v_body_x3f_x3f_1750_ = v___x_1779_;
v___y_1751_ = v___y_1772_;
v___y_1752_ = v___y_1773_;
v___y_1753_ = v___y_1774_;
v___y_1754_ = v___y_1775_;
v___y_1755_ = v___y_1776_;
v___y_1756_ = v___y_1777_;
goto v___jp_1747_;
}
v___jp_1781_:
{
lean_object* v___x_1788_; lean_object* v_rhs_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1788_ = lean_unsigned_to_nat(3u);
v_rhs_1789_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1788_);
v___x_1790_ = lean_unsigned_to_nat(4u);
v___x_1791_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1790_);
v___x_1792_ = l_Lean_Syntax_isNone(v___x_1791_);
if (v___x_1792_ == 0)
{
uint8_t v___x_1793_; 
lean_inc(v___x_1791_);
v___x_1793_ = l_Lean_Syntax_matchesNull(v___x_1791_, v___x_1788_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v___x_1791_);
lean_dec(v_rhs_1789_);
lean_dec(v_pattern_1746_);
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1795_ = lean_box(0);
v___x_1796_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1795_, v___x_1793_);
v___x_1797_ = l_Std_Format_defWidth;
v___x_1798_ = l_Std_Format_pretty(v___x_1796_, v___x_1797_, v___x_1745_, v___x_1745_);
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1800_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v_otherwise_x3f_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1802_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1803_ = l_Lean_Syntax_getArg(v___x_1791_, v___x_1780_);
v___x_1804_ = l_Lean_Syntax_getArg(v___x_1791_, v___x_1802_);
lean_dec(v___x_1791_);
v___x_1805_ = l_Lean_Syntax_isNone(v___x_1804_);
if (v___x_1805_ == 0)
{
uint8_t v___x_1806_; 
lean_inc(v___x_1804_);
v___x_1806_ = l_Lean_Syntax_matchesNull(v___x_1804_, v___x_1780_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v___x_1804_);
lean_dec(v_otherwise_x3f_1803_);
lean_dec(v_rhs_1789_);
lean_dec(v_pattern_1746_);
v___x_1807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1808_ = lean_box(0);
v___x_1809_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1808_, v___x_1806_);
v___x_1810_ = l_Std_Format_defWidth;
v___x_1811_ = l_Std_Format_pretty(v___x_1809_, v___x_1810_, v___x_1745_, v___x_1745_);
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1813_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v___x_1814_;
}
else
{
lean_object* v_body_x3f_x3f_1815_; lean_object* v___x_1816_; 
lean_dec(v_decl_1696_);
v_body_x3f_x3f_1815_ = l_Lean_Syntax_getArg(v___x_1804_, v___x_1745_);
lean_dec(v___x_1804_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_body_x3f_x3f_1815_);
v___y_1769_ = v_rhs_1789_;
v___y_1770_ = v_otherwise_x3f_1803_;
v_body_x3f_x3f_1771_ = v___x_1816_;
v___y_1772_ = v___y_1782_;
v___y_1773_ = v___y_1783_;
v___y_1774_ = v___y_1784_;
v___y_1775_ = v___y_1785_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v___y_1787_;
goto v___jp_1768_;
}
}
else
{
lean_object* v___x_1817_; 
lean_dec(v___x_1804_);
lean_dec(v_decl_1696_);
v___x_1817_ = lean_box(0);
v___y_1769_ = v_rhs_1789_;
v___y_1770_ = v_otherwise_x3f_1803_;
v_body_x3f_x3f_1771_ = v___x_1817_;
v___y_1772_ = v___y_1782_;
v___y_1773_ = v___y_1783_;
v___y_1774_ = v___y_1784_;
v___y_1775_ = v___y_1785_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v___y_1787_;
goto v___jp_1768_;
}
}
}
else
{
lean_object* v___x_1818_; 
lean_dec(v___x_1791_);
lean_dec(v_decl_1696_);
v___x_1818_ = lean_box(0);
v___y_1748_ = v_rhs_1789_;
v_otherwise_x3f_1749_ = v___x_1818_;
v_body_x3f_x3f_1750_ = v___x_1818_;
v___y_1751_ = v___y_1782_;
v___y_1752_ = v___y_1783_;
v___y_1753_ = v___y_1784_;
v___y_1754_ = v___y_1785_;
v___y_1755_ = v___y_1786_;
v___y_1756_ = v___y_1787_;
goto v___jp_1747_;
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v_x_1842_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1841_ = lean_unsigned_to_nat(0u);
v_x_1842_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1841_);
v___x_1856_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1842_);
v___x_1857_ = l_Lean_Syntax_isOfKind(v_x_1842_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec(v_x_1842_);
v___x_1858_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1859_ = lean_box(0);
v___x_1860_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1859_, v___x_1857_);
v___x_1861_ = l_Std_Format_defWidth;
v___x_1862_ = l_Std_Format_pretty(v___x_1860_, v___x_1861_, v___x_1841_, v___x_1841_);
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1858_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1864_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1866_);
v___x_1868_ = l_Lean_Syntax_isNone(v___x_1867_);
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; 
lean_inc(v___x_1867_);
v___x_1869_ = l_Lean_Syntax_matchesNull(v___x_1867_, v___x_1866_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec(v___x_1867_);
lean_dec(v_x_1842_);
v___x_1870_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1871_ = lean_box(0);
v___x_1872_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1871_, v___x_1869_);
v___x_1873_ = l_Std_Format_defWidth;
v___x_1874_ = l_Std_Format_pretty(v___x_1872_, v___x_1873_, v___x_1841_, v___x_1841_);
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1870_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1876_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = l_Lean_Syntax_getArg(v___x_1867_, v___x_1841_);
lean_dec(v___x_1867_);
v___x_1879_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1880_ = l_Lean_Syntax_isOfKind(v___x_1878_, v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec(v_x_1842_);
v___x_1881_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Lean_Syntax_formatStx(v_decl_1696_, v___x_1882_, v___x_1880_);
v___x_1884_ = l_Std_Format_defWidth;
v___x_1885_ = l_Std_Format_pretty(v___x_1883_, v___x_1884_, v___x_1841_, v___x_1841_);
v___x_1886_ = l_Lean_stringToMessageData(v___x_1885_);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1881_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1887_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1888_;
}
else
{
v___y_1844_ = v_a_1697_;
v___y_1845_ = v_a_1698_;
v___y_1846_ = v_a_1699_;
v___y_1847_ = v_a_1700_;
v___y_1848_ = v_a_1701_;
v___y_1849_ = v_a_1702_;
goto v___jp_1843_;
}
}
}
else
{
lean_dec(v___x_1867_);
v___y_1844_ = v_a_1697_;
v___y_1845_ = v_a_1698_;
v___y_1846_ = v_a_1699_;
v___y_1847_ = v_a_1700_;
v___y_1848_ = v_a_1701_;
v___y_1849_ = v_a_1702_;
goto v___jp_1843_;
}
}
v___jp_1843_:
{
lean_object* v___x_1850_; lean_object* v_rhs_1851_; 
v___x_1850_ = lean_unsigned_to_nat(3u);
v_rhs_1851_ = l_Lean_Syntax_getArg(v_decl_1696_, v___x_1850_);
lean_dec(v_decl_1696_);
if (v_reassignment_1695_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v_x_1842_);
v___x_1852_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1705_ = v___y_1847_;
v___y_1706_ = v___y_1844_;
v___y_1707_ = v___y_1845_;
v___y_1708_ = v___y_1849_;
v___y_1709_ = v___y_1846_;
v___y_1710_ = v___y_1848_;
v___y_1711_ = v_rhs_1851_;
v___y_1712_ = v___x_1852_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_mk_empty_array_with_capacity(v___x_1853_);
v___x_1855_ = lean_array_push(v___x_1854_, v_x_1842_);
v___y_1705_ = v___y_1847_;
v___y_1706_ = v___y_1844_;
v___y_1707_ = v___y_1845_;
v___y_1708_ = v___y_1849_;
v___y_1709_ = v___y_1846_;
v___y_1710_ = v___y_1848_;
v___y_1711_ = v_rhs_1851_;
v___y_1712_ = v___x_1855_;
goto v___jp_1704_;
}
}
}
v___jp_1704_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___y_1711_);
v___x_1714_ = lean_box(0);
v___x_1715_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1712_, v___x_1713_, v___x_1714_, v___x_1714_, v___y_1706_, v___y_1707_, v___y_1709_, v___y_1705_, v___y_1710_, v___y_1708_);
return v___x_1715_;
}
v___jp_1716_:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___y_1718_);
if (lean_obj_tag(v___y_1717_) == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1720_, v___x_1727_, v___y_1719_, v___x_1728_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1729_;
}
else
{
lean_object* v_val_1730_; lean_object* v___x_1731_; 
v_val_1730_ = lean_ctor_get(v___y_1717_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___y_1717_, 1);
v___x_1731_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1720_, v___x_1727_, v___y_1719_, v_val_1730_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_b_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_b_2017_);
return v___x_2026_;
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_array_uget_borrowed(v_as_2014_, v_i_2016_);
lean_inc(v_a_2027_);
v___x_2028_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_2027_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; size_t v___x_2031_; size_t v___x_2032_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2029_, v_b_2017_);
v___x_2031_ = ((size_t)1ULL);
v___x_2032_ = lean_usize_add(v_i_2016_, v___x_2031_);
v_i_2016_ = v___x_2032_;
v_b_2017_ = v___x_2030_;
goto _start;
}
else
{
lean_dec_ref(v_b_2017_);
return v___x_2028_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2063_, lean_object* v_as_2064_, size_t v_sz_2065_, size_t v_i_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_a_2076_; uint8_t v___x_2080_; 
v___x_2080_ = lean_usize_dec_lt(v_i_2066_, v_sz_2065_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_b_2067_);
return v___x_2081_;
}
else
{
lean_object* v___x_2082_; lean_object* v_a_2083_; uint8_t v___x_2084_; 
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2083_ = lean_array_uget_borrowed(v_as_2064_, v_i_2066_);
lean_inc(v_a_2083_);
v___x_2084_ = l_Lean_Syntax_isOfKind(v_a_2083_, v___x_2082_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_dec_ref_known(v___x_2085_, 1);
v_a_2076_ = v_b_2067_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_b_2067_);
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___y_2096_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2094_ = lean_unsigned_to_nat(3u);
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = l_Lean_Syntax_getArg(v_a_2083_, v___x_2113_);
v___x_2115_ = l_Lean_Syntax_getArgs(v___x_2114_);
lean_dec(v___x_2114_);
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2118_ = lean_array_get_size(v___x_2115_);
v___x_2119_ = lean_nat_dec_lt(v___x_2116_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_dec_ref(v___x_2115_);
v___y_2096_ = v___x_2117_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; lean_object* v_snd_2125_; 
v___x_2120_ = lean_box(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v___x_2117_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2118_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2084_, v___x_2063_, v___x_2115_, v___x_2122_, v___x_2123_, v___x_2121_);
lean_dec_ref(v___x_2115_);
v_snd_2125_ = lean_ctor_get(v___x_2124_, 1);
lean_inc(v_snd_2125_);
lean_dec_ref(v___x_2124_);
v___y_2096_ = v_snd_2125_;
goto v___jp_2095_;
}
v___jp_2095_:
{
size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_sz_2097_ = lean_array_size(v___y_2096_);
v___x_2098_ = ((size_t)0ULL);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2097_, v___x_2098_, v___y_2096_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref_known(v___x_2100_, 1);
v_a_2076_ = v_b_2067_;
goto v___jp_2075_;
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_b_2067_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec_ref_known(v___x_2099_, 1);
v___x_2109_ = l_Lean_Syntax_getArg(v_a_2083_, v___x_2094_);
v___x_2110_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2109_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2067_, v_a_2111_);
v_a_2076_ = v___x_2112_;
goto v___jp_2075_;
}
else
{
lean_dec_ref(v_b_2067_);
return v___x_2110_;
}
}
}
}
}
v___jp_2075_:
{
size_t v___x_2077_; size_t v___x_2078_; 
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_add(v_i_2066_, v___x_2077_);
v_i_2066_ = v___x_2078_;
v_b_2067_ = v_a_2076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2126_, size_t v_sz_2127_, size_t v_i_2128_, lean_object* v_b_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_a_2138_; uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_lt(v_i_2128_, v_sz_2127_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_b_2129_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; lean_object* v_a_2145_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v_a_2145_ = lean_array_uget_borrowed(v_as_2126_, v_i_2128_);
v___x_2158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2145_);
v___x_2159_ = l_Lean_Syntax_isOfKind(v_a_2145_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2145_);
v___x_2161_ = l_Lean_Syntax_isOfKind(v_a_2145_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2163_ = lean_box(0);
lean_inc(v_a_2145_);
v___x_2164_ = l_Lean_Syntax_formatStx(v_a_2145_, v___x_2163_, v___x_2161_);
v___x_2165_ = l_Std_Format_defWidth;
v___x_2166_ = l_Std_Format_pretty(v___x_2164_, v___x_2165_, v___x_2144_, v___x_2144_);
v___x_2167_ = l_Lean_stringToMessageData(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2162_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2168_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_dec_ref_known(v___x_2169_, 1);
v_a_2138_ = v_b_2129_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_b_2129_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = l_Lean_Syntax_getArg(v_a_2145_, v___x_2178_);
v___x_2180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2179_);
v___x_2181_ = l_Lean_Syntax_isOfKind(v___x_2179_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v___x_2179_);
v___x_2182_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2183_ = lean_box(0);
lean_inc(v_a_2145_);
v___x_2184_ = l_Lean_Syntax_formatStx(v_a_2145_, v___x_2183_, v___x_2181_);
v___x_2185_ = l_Std_Format_defWidth;
v___x_2186_ = l_Std_Format_pretty(v___x_2184_, v___x_2185_, v___x_2144_, v___x_2144_);
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2182_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2188_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
v_a_2138_ = v_b_2129_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_b_2129_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; size_t v_sz_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2198_ = l_Lean_Syntax_getArg(v___x_2179_, v___x_2144_);
lean_dec(v___x_2179_);
v___x_2199_ = l_Lean_Syntax_getArgs(v___x_2198_);
lean_dec(v___x_2198_);
v_sz_2200_ = lean_array_size(v___x_2199_);
v___x_2201_ = ((size_t)0ULL);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2159_, v___x_2199_, v_sz_2200_, v___x_2201_, v_b_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec_ref(v___x_2199_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v_a_2138_ = v_a_2203_;
goto v___jp_2137_;
}
else
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2204_ = lean_unsigned_to_nat(2u);
v___x_2205_ = l_Lean_Syntax_getArg(v_a_2145_, v___x_2204_);
v___x_2206_ = l_Lean_Syntax_isNone(v___x_2205_);
if (v___x_2206_ == 0)
{
uint8_t v___x_2207_; 
v___x_2207_ = l_Lean_Syntax_matchesNull(v___x_2205_, v___x_2204_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2209_ = lean_box(0);
lean_inc(v_a_2145_);
v___x_2210_ = l_Lean_Syntax_formatStx(v_a_2145_, v___x_2209_, v___x_2207_);
v___x_2211_ = l_Std_Format_defWidth;
v___x_2212_ = l_Std_Format_pretty(v___x_2210_, v___x_2211_, v___x_2144_, v___x_2144_);
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2208_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2214_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_dec_ref_known(v___x_2215_, 1);
v_a_2138_ = v_b_2129_;
goto v___jp_2137_;
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v_b_2129_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
v___y_2147_ = v___y_2130_;
v___y_2148_ = v___y_2131_;
v___y_2149_ = v___y_2132_;
v___y_2150_ = v___y_2133_;
v___y_2151_ = v___y_2134_;
v___y_2152_ = v___y_2135_;
goto v___jp_2146_;
}
}
else
{
lean_dec(v___x_2205_);
v___y_2147_ = v___y_2130_;
v___y_2148_ = v___y_2131_;
v___y_2149_ = v___y_2132_;
v___y_2150_ = v___y_2133_;
v___y_2151_ = v___y_2134_;
v___y_2152_ = v___y_2135_;
goto v___jp_2146_;
}
}
v___jp_2146_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(4u);
v___x_2154_ = l_Lean_Syntax_getArg(v_a_2145_, v___x_2153_);
v___x_2155_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2154_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2156_, v_b_2129_);
v_a_2138_ = v___x_2157_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v_b_2129_);
return v___x_2155_;
}
}
}
v___jp_2137_:
{
size_t v___x_2139_; size_t v___x_2140_; 
v___x_2139_ = ((size_t)1ULL);
v___x_2140_ = lean_usize_add(v_i_2128_, v___x_2139_);
v_i_2128_ = v___x_2140_;
v_b_2129_ = v_a_2138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2224_) == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
else
{
lean_object* v_val_2234_; lean_object* v___x_2235_; 
v_val_2234_ = lean_ctor_get(v_stx_x3f_2224_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v_stx_x3f_2224_, 1);
v___x_2235_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2234_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2254_, lean_object* v_as_2255_, size_t v_sz_2256_, size_t v_i_2257_, lean_object* v_b_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_a_2267_; uint8_t v___x_2271_; 
v___x_2271_ = lean_usize_dec_lt(v_i_2257_, v_sz_2256_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_b_2258_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; lean_object* v_a_2274_; uint8_t v___x_2275_; 
v___x_2273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2274_ = lean_array_uget_borrowed(v_as_2255_, v_i_2257_);
lean_inc(v_a_2274_);
v___x_2275_ = l_Lean_Syntax_isOfKind(v_a_2274_, v___x_2273_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec_ref_known(v___x_2276_, 1);
v_a_2267_ = v_b_2258_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_b_2258_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v___x_2285_; lean_object* v___y_2287_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2285_ = lean_unsigned_to_nat(3u);
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = l_Lean_Syntax_getArg(v_a_2274_, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_getArgs(v___x_2305_);
lean_dec(v___x_2305_);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2309_ = lean_array_get_size(v___x_2306_);
v___x_2310_ = lean_nat_dec_lt(v___x_2307_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec_ref(v___x_2306_);
v___y_2287_ = v___x_2308_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; lean_object* v___x_2315_; lean_object* v_snd_2316_; 
v___x_2311_ = lean_box(v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2308_);
v___x_2313_ = ((size_t)0ULL);
v___x_2314_ = lean_usize_of_nat(v___x_2309_);
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2275_, v___x_2254_, v___x_2306_, v___x_2313_, v___x_2314_, v___x_2312_);
lean_dec_ref(v___x_2306_);
v_snd_2316_ = lean_ctor_get(v___x_2315_, 1);
lean_inc(v_snd_2316_);
lean_dec_ref(v___x_2315_);
v___y_2287_ = v_snd_2316_;
goto v___jp_2286_;
}
v___jp_2286_:
{
size_t v_sz_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v_sz_2288_ = lean_array_size(v___y_2287_);
v___x_2289_ = ((size_t)0ULL);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2288_, v___x_2289_, v___y_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_dec_ref_known(v___x_2291_, 1);
v_a_2267_ = v_b_2258_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_b_2258_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref_known(v___x_2290_, 1);
v___x_2300_ = l_Lean_Syntax_getArg(v_a_2274_, v___x_2285_);
v___x_2301_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2300_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2258_, v_a_2302_);
v_a_2267_ = v___x_2303_;
goto v___jp_2266_;
}
else
{
lean_dec_ref(v_b_2258_);
return v___x_2301_;
}
}
}
}
}
v___jp_2266_:
{
size_t v___x_2268_; size_t v___x_2269_; 
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2257_, v___x_2268_);
v_i_2257_ = v___x_2269_;
v_b_2258_ = v_a_2267_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; 
v___x_2365_ = l_Lean_NameSet_empty;
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = 0;
v___x_2368_ = 1;
v___x_2369_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2369_, 0, v___x_2366_);
lean_ctor_set(v___x_2369_, 1, v___x_2365_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2, v___x_2368_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2 + 1, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2 + 2, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2 + 3, v___x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___y_2379_; lean_object* v_bodyInfo_2380_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2424_; lean_object* v_bodyInfo_2425_; lean_object* v___x_2428_; lean_object* v_env_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = lean_st_ref_get(v_a_2376_);
v_env_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc_ref(v_env_2429_);
lean_dec(v___x_2428_);
lean_inc(v_stx_2370_);
v___x_2430_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2430_, 0, v_env_2429_);
lean_closure_set(v___x_2430_, 1, v_stx_2370_);
v___x_2431_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2430_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_5142_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_5142_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_5142_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
if (lean_obj_tag(v_a_2432_) == 1)
{
lean_object* v_val_2444_; lean_object* v_snd_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_del_object(v___x_2434_);
lean_dec(v_stx_2370_);
v_val_2444_ = lean_ctor_get(v_a_2432_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v_a_2432_, 1);
v_snd_2445_ = lean_ctor_get(v_val_2444_, 1);
lean_inc(v_snd_2445_);
lean_dec(v_val_2444_);
v___x_2446_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2446_, 0, lean_box(0));
lean_closure_set(v___x_2446_, 1, v_snd_2445_);
v___x_2447_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2446_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v_stx_2370_ = v_a_2448_;
goto _start;
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2447_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2447_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v___x_2458_; uint8_t v___x_2459_; uint8_t v___x_2460_; 
lean_dec(v_a_2432_);
v___x_2458_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
lean_inc(v_stx_2370_);
v___x_2459_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2458_);
v___x_2460_ = 1;
if (v___x_2459_ == 0)
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3));
lean_inc(v_stx_2370_);
v___x_2462_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5));
lean_inc(v_stx_2370_);
v___x_2464_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7));
lean_inc(v_stx_2370_);
v___x_2466_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; 
v___x_2467_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9));
lean_inc(v_stx_2370_);
v___x_2468_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2370_);
v___x_2584_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2370_);
v___x_2637_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; 
v___x_2638_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2370_);
v___x_2639_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2697_; uint8_t v___x_2698_; lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; 
lean_del_object(v___x_2434_);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2370_);
v___x_2698_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2370_);
v___x_2767_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2370_);
v___x_2769_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2370_);
v___x_2771_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2370_);
v___x_2773_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2370_);
v___x_2775_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2776_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2370_);
v___x_2777_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2370_);
v___x_2779_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; uint8_t v___x_2781_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; 
v___x_2780_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2370_);
v___x_2781_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2370_);
v___x_2790_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2370_);
v___x_2792_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2370_);
v___x_2794_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2370_);
v___x_2796_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2370_);
v___x_2798_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2370_);
v___x_2800_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2801_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2370_);
v___x_2802_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2370_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2370_);
v___x_2806_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2370_);
v___x_2808_ = l_Lean_Syntax_isOfKind(v_stx_2370_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v_env_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2809_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2810_ = lean_st_ref_get(v_a_2376_);
v_env_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc_ref(v_env_2811_);
lean_dec(v___x_2810_);
v___x_2812_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2813_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2812_, v_env_2811_, v___x_2809_);
v___x_2814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2815_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2813_, v___x_2814_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_2813_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2846_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2846_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2846_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_fst_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2844_; 
v_fst_2820_ = lean_ctor_get(v_a_2816_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_a_2816_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v_a_2816_, 1);
lean_dec(v_unused_2845_);
v___x_2822_ = v_a_2816_;
v_isShared_2823_ = v_isSharedCheck_2844_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_fst_2820_);
lean_dec(v_a_2816_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2844_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
if (lean_obj_tag(v_fst_2820_) == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_del_object(v___x_2818_);
v___x_2824_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2825_ = l_Lean_MessageData_ofName(v___x_2809_);
lean_inc_ref(v___x_2825_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 7);
lean_ctor_set(v___x_2822_, 1, v___x_2825_);
lean_ctor_set(v___x_2822_, 0, v___x_2824_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2828_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2831_ = l_Lean_indentD(v___x_2830_);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2829_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2825_);
v___x_2836_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2837_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2838_;
}
}
else
{
lean_object* v_val_2840_; lean_object* v___x_2842_; 
lean_del_object(v___x_2822_);
lean_dec(v___x_2809_);
lean_dec(v_stx_2370_);
v_val_2840_ = lean_ctor_get(v_fst_2820_, 0);
lean_inc(v_val_2840_);
lean_dec_ref_known(v_fst_2820_, 1);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_val_2840_);
v___x_2842_ = v___x_2818_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_val_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v___x_2809_);
lean_dec(v_stx_2370_);
v_a_2847_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2815_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2815_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___y_2859_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_unsigned_to_nat(5u);
v___x_2857_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2856_);
v___x_2868_ = lean_unsigned_to_nat(6u);
v___x_2869_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2868_);
lean_dec(v_stx_2370_);
v___x_2870_ = l_Lean_Syntax_getOptional_x3f(v___x_2869_);
lean_dec(v___x_2869_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_box(0);
v___y_2859_ = v___x_2871_;
goto v___jp_2858_;
}
else
{
lean_object* v_val_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_val_2872_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2870_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_val_2872_);
lean_dec(v___x_2870_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_val_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
v___y_2859_ = v___x_2877_;
goto v___jp_2858_;
}
}
}
v___jp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2857_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2860_) == 0)
{
if (lean_obj_tag(v___y_2859_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = l_Lean_NameSet_empty;
v___x_2863_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2863_, 0, v___x_2855_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*2, v___x_2806_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*2 + 1, v___x_2806_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*2 + 2, v___x_2806_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*2 + 3, v___x_2806_);
v___y_2379_ = v_a_2861_;
v_bodyInfo_2380_ = v___x_2863_;
goto v___jp_2378_;
}
else
{
lean_object* v_a_2864_; lean_object* v_val_2865_; lean_object* v___x_2866_; 
v_a_2864_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2860_, 1);
v_val_2865_ = lean_ctor_get(v___y_2859_, 0);
lean_inc(v_val_2865_);
lean_dec_ref_known(v___y_2859_, 1);
v___x_2866_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2865_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v___y_2379_ = v_a_2864_;
v_bodyInfo_2380_ = v_a_2867_;
goto v___jp_2378_;
}
else
{
lean_dec(v_a_2864_);
return v___x_2866_;
}
}
}
else
{
lean_dec(v___y_2859_);
return v___x_2860_;
}
}
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___y_2884_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2880_ = lean_unsigned_to_nat(1u);
v___x_2881_ = lean_unsigned_to_nat(5u);
v___x_2882_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2881_);
v___x_2893_ = lean_unsigned_to_nat(6u);
v___x_2894_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2893_);
lean_dec(v_stx_2370_);
v___x_2895_ = l_Lean_Syntax_getOptional_x3f(v___x_2894_);
lean_dec(v___x_2894_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_box(0);
v___y_2884_ = v___x_2896_;
goto v___jp_2883_;
}
else
{
lean_object* v_val_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_val_2897_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2895_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_val_2897_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_val_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
v___y_2884_ = v___x_2902_;
goto v___jp_2883_;
}
}
}
v___jp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2882_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2885_) == 0)
{
if (lean_obj_tag(v___y_2884_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = l_Lean_NameSet_empty;
v___x_2888_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2888_, 0, v___x_2880_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*2, v___x_2804_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*2 + 1, v___x_2804_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*2 + 2, v___x_2804_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*2 + 3, v___x_2804_);
v___y_2424_ = v_a_2886_;
v_bodyInfo_2425_ = v___x_2888_;
goto v___jp_2423_;
}
else
{
lean_object* v_a_2889_; lean_object* v_val_2890_; lean_object* v___x_2891_; 
v_a_2889_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2885_, 1);
v_val_2890_ = lean_ctor_get(v___y_2884_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v___y_2884_, 1);
v___x_2891_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2890_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___y_2424_ = v_a_2889_;
v_bodyInfo_2425_ = v_a_2892_;
goto v___jp_2423_;
}
else
{
lean_dec(v_a_2889_);
return v___x_2891_;
}
}
}
else
{
lean_dec(v___y_2884_);
return v___x_2885_;
}
}
}
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_unsigned_to_nat(1u);
v___x_3120_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2906_);
v___x_3121_ = l_Lean_Syntax_isNone(v___x_3120_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = lean_unsigned_to_nat(5u);
v___x_3123_ = l_Lean_Syntax_matchesNull(v___x_3120_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_env_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3124_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3125_ = lean_st_ref_get(v_a_2376_);
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc_ref(v_env_3126_);
lean_dec(v___x_3125_);
v___x_3127_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3128_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3127_, v_env_3126_, v___x_3124_);
v___x_3129_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3130_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3128_, v___x_3129_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3128_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3161_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3161_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3161_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v_fst_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3159_; 
v_fst_3135_ = lean_ctor_get(v_a_3131_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_a_3131_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v_a_3131_, 1);
lean_dec(v_unused_3160_);
v___x_3137_ = v_a_3131_;
v_isShared_3138_ = v_isSharedCheck_3159_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_fst_3135_);
lean_dec(v_a_3131_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3159_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
if (lean_obj_tag(v_fst_3135_) == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_del_object(v___x_3133_);
v___x_3139_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3140_ = l_Lean_MessageData_ofName(v___x_3124_);
lean_inc_ref(v___x_3140_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set_tag(v___x_3137_, 7);
lean_ctor_set(v___x_3137_, 1, v___x_3140_);
lean_ctor_set(v___x_3137_, 0, v___x_3139_);
v___x_3142_ = v___x_3137_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3143_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3146_ = l_Lean_indentD(v___x_3145_);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3144_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___x_3140_);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3152_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3153_;
}
}
else
{
lean_object* v_val_3155_; lean_object* v___x_3157_; 
lean_del_object(v___x_3137_);
lean_dec(v___x_3124_);
lean_dec(v_stx_2370_);
v_val_3155_ = lean_ctor_get(v_fst_3135_, 0);
lean_inc(v_val_3155_);
lean_dec_ref_known(v_fst_3135_, 1);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_val_3155_);
v___x_3157_ = v___x_3133_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_val_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v___x_3124_);
lean_dec(v_stx_2370_);
v_a_3162_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3130_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3130_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
v___y_2908_ = v_a_2371_;
v___y_2909_ = v_a_2372_;
v___y_2910_ = v_a_2373_;
v___y_2911_ = v_a_2374_;
v___y_2912_ = v_a_2375_;
v___y_2913_ = v_a_2376_;
goto v___jp_2907_;
}
}
else
{
lean_dec(v___x_3120_);
v___y_2908_ = v_a_2371_;
v___y_2909_ = v_a_2372_;
v___y_2910_ = v_a_2373_;
v___y_2911_ = v_a_2374_;
v___y_2912_ = v_a_2375_;
v___y_2913_ = v_a_2376_;
goto v___jp_2907_;
}
v___jp_2907_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2914_ = lean_unsigned_to_nat(4u);
v___x_2915_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2914_);
v___x_2916_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2915_);
v___x_2917_ = l_Lean_Syntax_isOfKind(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v_env_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec(v___x_2915_);
lean_inc_n(v_stx_2370_, 2);
v___x_2918_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2919_ = lean_st_ref_get(v___y_2913_);
v_env_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc_ref(v_env_2920_);
lean_dec(v___x_2919_);
v___x_2921_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2922_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2921_, v_env_2920_, v___x_2918_);
v___x_2923_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2924_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2922_, v___x_2923_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___x_2922_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2955_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2955_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2955_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v_fst_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2953_; 
v_fst_2929_ = lean_ctor_get(v_a_2925_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_a_2925_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v_a_2925_, 1);
lean_dec(v_unused_2954_);
v___x_2931_ = v_a_2925_;
v_isShared_2932_ = v_isSharedCheck_2953_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_fst_2929_);
lean_dec(v_a_2925_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2953_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
if (lean_obj_tag(v_fst_2929_) == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
lean_del_object(v___x_2927_);
v___x_2933_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2934_ = l_Lean_MessageData_ofName(v___x_2918_);
lean_inc_ref(v___x_2934_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 7);
lean_ctor_set(v___x_2931_, 1, v___x_2934_);
lean_ctor_set(v___x_2931_, 0, v___x_2933_);
v___x_2936_ = v___x_2931_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2937_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2940_ = l_Lean_indentD(v___x_2939_);
v___x_2941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2938_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
lean_ctor_set(v___x_2944_, 1, v___x_2934_);
v___x_2945_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2946_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2947_;
}
}
else
{
lean_object* v_val_2949_; lean_object* v___x_2951_; 
lean_del_object(v___x_2931_);
lean_dec(v___x_2918_);
lean_dec(v_stx_2370_);
v_val_2949_ = lean_ctor_get(v_fst_2929_, 0);
lean_inc(v_val_2949_);
lean_dec_ref_known(v_fst_2929_, 1);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v_val_2949_);
v___x_2951_ = v___x_2927_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_val_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v___x_2918_);
lean_dec(v_stx_2370_);
v_a_2956_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2924_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2924_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; size_t v_sz_2966_; size_t v___x_2967_; lean_object* v___x_2968_; 
v___x_2964_ = l_Lean_Syntax_getArg(v___x_2915_, v___x_2905_);
v___x_2965_ = l_Lean_Syntax_getArgs(v___x_2964_);
lean_dec(v___x_2964_);
v_sz_2966_ = lean_array_size(v___x_2965_);
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_2802_, v_sz_2966_, v___x_2967_, v___x_2965_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_env_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___x_2915_);
lean_inc_n(v_stx_2370_, 2);
v___x_2969_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2970_ = lean_st_ref_get(v___y_2913_);
v_env_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc_ref(v_env_2971_);
lean_dec(v___x_2970_);
v___x_2972_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2973_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2972_, v_env_2971_, v___x_2969_);
v___x_2974_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2975_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2973_, v___x_2974_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___x_2973_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3006_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3006_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3006_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_fst_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3004_; 
v_fst_2980_ = lean_ctor_get(v_a_2976_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_a_2976_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v_a_2976_, 1);
lean_dec(v_unused_3005_);
v___x_2982_ = v_a_2976_;
v_isShared_2983_ = v_isSharedCheck_3004_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_fst_2980_);
lean_dec(v_a_2976_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3004_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
if (lean_obj_tag(v_fst_2980_) == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_del_object(v___x_2978_);
v___x_2984_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2985_ = l_Lean_MessageData_ofName(v___x_2969_);
lean_inc_ref(v___x_2985_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 7);
lean_ctor_set(v___x_2982_, 1, v___x_2985_);
lean_ctor_set(v___x_2982_, 0, v___x_2984_);
v___x_2987_ = v___x_2982_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2988_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2991_ = l_Lean_indentD(v___x_2990_);
v___x_2992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2989_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2992_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v___x_2985_);
v___x_2996_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
v___x_2998_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2997_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2998_;
}
}
else
{
lean_object* v_val_3000_; lean_object* v___x_3002_; 
lean_del_object(v___x_2982_);
lean_dec(v___x_2969_);
lean_dec(v_stx_2370_);
v_val_3000_ = lean_ctor_get(v_fst_2980_, 0);
lean_inc(v_val_3000_);
lean_dec_ref_known(v_fst_2980_, 1);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v_val_3000_);
v___x_3002_ = v___x_2978_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_val_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v___x_2969_);
lean_dec(v_stx_2370_);
v_a_3007_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2975_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2975_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_val_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_val_3015_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_val_3015_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_3016_ = l_Lean_Syntax_getArg(v___x_2915_, v___x_2906_);
lean_dec(v___x_2915_);
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_3016_);
v___x_3018_ = l_Lean_Syntax_isOfKind(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_env_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_dec(v___x_3016_);
lean_dec(v_val_3015_);
lean_inc_n(v_stx_2370_, 2);
v___x_3019_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3020_ = lean_st_ref_get(v___y_2913_);
v_env_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref(v_env_3021_);
lean_dec(v___x_3020_);
v___x_3022_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3023_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3022_, v_env_3021_, v___x_3019_);
v___x_3024_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3025_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3023_, v___x_3024_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___x_3023_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3056_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3056_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3056_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_fst_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3054_; 
v_fst_3030_ = lean_ctor_get(v_a_3026_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_a_3026_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; 
v_unused_3055_ = lean_ctor_get(v_a_3026_, 1);
lean_dec(v_unused_3055_);
v___x_3032_ = v_a_3026_;
v_isShared_3033_ = v_isSharedCheck_3054_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_fst_3030_);
lean_dec(v_a_3026_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3054_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
if (lean_obj_tag(v_fst_3030_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
lean_del_object(v___x_3028_);
v___x_3034_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3035_ = l_Lean_MessageData_ofName(v___x_3019_);
lean_inc_ref(v___x_3035_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 7);
lean_ctor_set(v___x_3032_, 1, v___x_3035_);
lean_ctor_set(v___x_3032_, 0, v___x_3034_);
v___x_3037_ = v___x_3032_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3034_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3038_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3041_ = l_Lean_indentD(v___x_3040_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3039_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3035_);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3047_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_3048_;
}
}
else
{
lean_object* v_val_3050_; lean_object* v___x_3052_; 
lean_del_object(v___x_3032_);
lean_dec(v___x_3019_);
lean_dec(v_stx_2370_);
v_val_3050_ = lean_ctor_get(v_fst_3030_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v_fst_3030_, 1);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v_val_3050_);
v___x_3052_ = v___x_3028_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_val_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec(v___x_3019_);
lean_dec(v_stx_2370_);
v_a_3057_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3025_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3025_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3065_ = l_Lean_Syntax_getArg(v___x_3016_, v___x_2906_);
v___x_3066_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3067_ = l_Lean_Syntax_isOfKind(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_env_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v___x_3016_);
lean_dec(v_val_3015_);
lean_inc_n(v_stx_2370_, 2);
v___x_3068_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3069_ = lean_st_ref_get(v___y_2913_);
v_env_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc_ref(v_env_3070_);
lean_dec(v___x_3069_);
v___x_3071_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3072_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3071_, v_env_3070_, v___x_3068_);
v___x_3073_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3074_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3072_, v___x_3073_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___x_3072_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3105_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3105_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3105_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_fst_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3103_; 
v_fst_3079_ = lean_ctor_get(v_a_3075_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3075_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v_a_3075_, 1);
lean_dec(v_unused_3104_);
v___x_3081_ = v_a_3075_;
v_isShared_3082_ = v_isSharedCheck_3103_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_fst_3079_);
lean_dec(v_a_3075_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3103_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
if (lean_obj_tag(v_fst_3079_) == 0)
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3086_; 
lean_del_object(v___x_3077_);
v___x_3083_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3084_ = l_Lean_MessageData_ofName(v___x_3068_);
lean_inc_ref(v___x_3084_);
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 7);
lean_ctor_set(v___x_3081_, 1, v___x_3084_);
lean_ctor_set(v___x_3081_, 0, v___x_3083_);
v___x_3086_ = v___x_3081_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3087_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3086_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3090_ = l_Lean_indentD(v___x_3089_);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3088_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3084_);
v___x_3095_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3096_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_3097_;
}
}
else
{
lean_object* v_val_3099_; lean_object* v___x_3101_; 
lean_del_object(v___x_3081_);
lean_dec(v___x_3068_);
lean_dec(v_stx_2370_);
v_val_3099_ = lean_ctor_get(v_fst_3079_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v_fst_3079_, 1);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v_val_3099_);
v___x_3101_ = v___x_3077_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_val_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v___x_3068_);
lean_dec(v_stx_2370_);
v_a_3106_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3074_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3074_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v_stx_2370_);
v___x_3114_ = lean_unsigned_to_nat(3u);
v___x_3115_ = l_Lean_Syntax_getArg(v___x_3016_, v___x_3114_);
lean_dec(v___x_3016_);
v___x_3116_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3115_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; size_t v_sz_3118_; lean_object* v___x_3119_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_sz_3118_ = lean_array_size(v_val_3015_);
v___x_3119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_3015_, v_sz_3118_, v___x_2967_, v_a_3117_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v_val_3015_);
return v___x_3119_;
}
else
{
lean_dec(v_val_3015_);
return v___x_3116_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
lean_dec(v_stx_2370_);
v___x_3170_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
return v___x_3171_;
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v_stx_2370_);
v___x_3172_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_dec(v_stx_2370_);
v___x_3174_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec(v_stx_2370_);
v___x_3176_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v_stx_2370_);
v___x_3178_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
return v___x_3179_;
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; size_t v_sz_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3180_ = lean_unsigned_to_nat(2u);
v___x_3181_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3180_);
v___x_3182_ = l_Lean_Syntax_getArgs(v___x_3181_);
lean_dec(v___x_3181_);
v_sz_3183_ = lean_array_size(v___x_3182_);
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3183_, v___x_3184_, v___x_3182_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v_env_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3186_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3187_ = lean_st_ref_get(v_a_2376_);
v_env_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_ref(v_env_3188_);
lean_dec(v___x_3187_);
v___x_3189_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3190_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3189_, v_env_3188_, v___x_3186_);
v___x_3191_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3192_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3190_, v___x_3191_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3190_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3223_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3223_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_fst_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3221_; 
v_fst_3197_ = lean_ctor_get(v_a_3193_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_a_3193_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_a_3193_, 1);
lean_dec(v_unused_3222_);
v___x_3199_ = v_a_3193_;
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_fst_3197_);
lean_dec(v_a_3193_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3221_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
if (lean_obj_tag(v_fst_3197_) == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_del_object(v___x_3195_);
v___x_3201_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3202_ = l_Lean_MessageData_ofName(v___x_3186_);
lean_inc_ref(v___x_3202_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 7);
lean_ctor_set(v___x_3199_, 1, v___x_3202_);
lean_ctor_set(v___x_3199_, 0, v___x_3201_);
v___x_3204_ = v___x_3199_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3205_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3208_ = l_Lean_indentD(v___x_3207_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3206_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3202_);
v___x_3213_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3214_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3215_;
}
}
else
{
lean_object* v_val_3217_; lean_object* v___x_3219_; 
lean_del_object(v___x_3199_);
lean_dec(v___x_3186_);
lean_dec(v_stx_2370_);
v_val_3217_ = lean_ctor_get(v_fst_3197_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_fst_3197_, 1);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_val_3217_);
v___x_3219_ = v___x_3195_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_val_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v___x_3186_);
lean_dec(v_stx_2370_);
v_a_3224_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3192_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3192_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_val_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3366_; 
v_val_3232_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3234_ = v___x_3185_;
v_isShared_3235_ = v_isSharedCheck_3366_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_val_3232_);
lean_dec(v___x_3185_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3366_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_finSeq_x3f_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3236_);
v___x_3261_ = lean_unsigned_to_nat(3u);
v___x_3262_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3261_);
v___x_3263_ = l_Lean_Syntax_isNone(v___x_3262_);
if (v___x_3263_ == 0)
{
uint8_t v___x_3264_; 
lean_inc(v___x_3262_);
v___x_3264_ = l_Lean_Syntax_matchesNull(v___x_3262_, v___x_3236_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_env_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec(v___x_3262_);
lean_dec(v___x_3237_);
lean_del_object(v___x_3234_);
lean_dec(v_val_3232_);
lean_inc_n(v_stx_2370_, 2);
v___x_3265_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3266_ = lean_st_ref_get(v_a_2376_);
v_env_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3267_);
lean_dec(v___x_3266_);
v___x_3268_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3269_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3268_, v_env_3267_, v___x_3265_);
v___x_3270_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3271_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3269_, v___x_3270_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3269_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3302_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3302_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3302_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_fst_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3300_; 
v_fst_3276_ = lean_ctor_get(v_a_3272_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_a_3272_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v_a_3272_, 1);
lean_dec(v_unused_3301_);
v___x_3278_ = v_a_3272_;
v_isShared_3279_ = v_isSharedCheck_3300_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_fst_3276_);
lean_dec(v_a_3272_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3300_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
if (lean_obj_tag(v_fst_3276_) == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_del_object(v___x_3274_);
v___x_3280_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3281_ = l_Lean_MessageData_ofName(v___x_3265_);
lean_inc_ref(v___x_3281_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set_tag(v___x_3278_, 7);
lean_ctor_set(v___x_3278_, 1, v___x_3281_);
lean_ctor_set(v___x_3278_, 0, v___x_3280_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3284_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3287_ = l_Lean_indentD(v___x_3286_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3285_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
lean_ctor_set(v___x_3291_, 1, v___x_3281_);
v___x_3292_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3293_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3294_;
}
}
else
{
lean_object* v_val_3296_; lean_object* v___x_3298_; 
lean_del_object(v___x_3278_);
lean_dec(v___x_3265_);
lean_dec(v_stx_2370_);
v_val_3296_ = lean_ctor_get(v_fst_3276_, 0);
lean_inc(v_val_3296_);
lean_dec_ref_known(v_fst_3276_, 1);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v_val_3296_);
v___x_3298_ = v___x_3274_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_val_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec(v___x_3265_);
lean_dec(v_stx_2370_);
v_a_3303_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3271_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3271_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3311_);
lean_dec(v___x_3262_);
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3312_);
v___x_3314_ = l_Lean_Syntax_isOfKind(v___x_3312_, v___x_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v_env_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_dec(v___x_3312_);
lean_dec(v___x_3237_);
lean_del_object(v___x_3234_);
lean_dec(v_val_3232_);
lean_inc_n(v_stx_2370_, 2);
v___x_3315_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3316_ = lean_st_ref_get(v_a_2376_);
v_env_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_ref(v_env_3317_);
lean_dec(v___x_3316_);
v___x_3318_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3319_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3318_, v_env_3317_, v___x_3315_);
v___x_3320_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3321_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3319_, v___x_3320_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3319_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3352_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3352_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3352_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_fst_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3350_; 
v_fst_3326_ = lean_ctor_get(v_a_3322_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_a_3322_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; 
v_unused_3351_ = lean_ctor_get(v_a_3322_, 1);
lean_dec(v_unused_3351_);
v___x_3328_ = v_a_3322_;
v_isShared_3329_ = v_isSharedCheck_3350_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_fst_3326_);
lean_dec(v_a_3322_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3350_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
if (lean_obj_tag(v_fst_3326_) == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3333_; 
lean_del_object(v___x_3324_);
v___x_3330_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3331_ = l_Lean_MessageData_ofName(v___x_3315_);
lean_inc_ref(v___x_3331_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set_tag(v___x_3328_, 7);
lean_ctor_set(v___x_3328_, 1, v___x_3331_);
lean_ctor_set(v___x_3328_, 0, v___x_3330_);
v___x_3333_ = v___x_3328_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3334_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3337_ = l_Lean_indentD(v___x_3336_);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3335_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v___x_3331_);
v___x_3342_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3343_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3344_;
}
}
else
{
lean_object* v_val_3346_; lean_object* v___x_3348_; 
lean_del_object(v___x_3328_);
lean_dec(v___x_3315_);
lean_dec(v_stx_2370_);
v_val_3346_ = lean_ctor_get(v_fst_3326_, 0);
lean_inc(v_val_3346_);
lean_dec_ref_known(v_fst_3326_, 1);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v_val_3346_);
v___x_3348_ = v___x_3324_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_val_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v___x_3315_);
lean_dec(v_stx_2370_);
v_a_3353_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3321_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3321_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
lean_dec(v_stx_2370_);
v___x_3361_ = l_Lean_Syntax_getArg(v___x_3312_, v___x_3236_);
lean_dec(v___x_3312_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3361_);
v___x_3363_ = v___x_3234_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
v_finSeq_x3f_3239_ = v___x_3363_;
v___y_3240_ = v_a_2371_;
v___y_3241_ = v_a_2372_;
v___y_3242_ = v_a_2373_;
v___y_3243_ = v_a_2374_;
v___y_3244_ = v_a_2375_;
v___y_3245_ = v_a_2376_;
goto v___jp_3238_;
}
}
}
}
else
{
lean_object* v___x_3365_; 
lean_dec(v___x_3262_);
lean_del_object(v___x_3234_);
lean_dec(v_stx_2370_);
v___x_3365_ = lean_box(0);
v_finSeq_x3f_3239_ = v___x_3365_;
v___y_3240_ = v_a_2371_;
v___y_3241_ = v_a_2372_;
v___y_3242_ = v_a_2373_;
v___y_3243_ = v_a_2374_;
v___y_3244_ = v_a_2375_;
v___y_3245_ = v_a_2376_;
goto v___jp_3238_;
}
v___jp_3238_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3237_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; size_t v_sz_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_sz_3248_ = lean_array_size(v_val_3232_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3232_, v_sz_3248_, v___x_3184_, v_a_3247_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v_val_3232_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3251_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3260_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3254_ = v___x_3251_;
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3251_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3260_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3250_, v_a_3252_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3256_);
v___x_3258_ = v___x_3254_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
else
{
lean_dec(v_a_3250_);
return v___x_3251_;
}
}
else
{
lean_dec(v_finSeq_x3f_3239_);
return v___x_3249_;
}
}
else
{
lean_dec(v_finSeq_x3f_3239_);
lean_dec(v_val_3232_);
return v___x_3246_;
}
}
}
}
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_unsigned_to_nat(1u);
v___x_3491_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3368_);
v___x_3492_ = l_Lean_Syntax_isNone(v___x_3491_);
if (v___x_3492_ == 0)
{
uint8_t v___x_3493_; 
lean_inc(v___x_3491_);
v___x_3493_ = l_Lean_Syntax_matchesNull(v___x_3491_, v___x_3368_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v_env_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec(v___x_3491_);
lean_inc_n(v_stx_2370_, 2);
v___x_3494_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3495_ = lean_st_ref_get(v_a_2376_);
v_env_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_env_3496_);
lean_dec(v___x_3495_);
v___x_3497_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3498_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3497_, v_env_3496_, v___x_3494_);
v___x_3499_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3500_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3498_, v___x_3499_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3498_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3531_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3531_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_fst_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3529_; 
v_fst_3505_ = lean_ctor_get(v_a_3501_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v_a_3501_, 1);
lean_dec(v_unused_3530_);
v___x_3507_ = v_a_3501_;
v_isShared_3508_ = v_isSharedCheck_3529_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_fst_3505_);
lean_dec(v_a_3501_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3529_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
if (lean_obj_tag(v_fst_3505_) == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
lean_del_object(v___x_3503_);
v___x_3509_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3510_ = l_Lean_MessageData_ofName(v___x_3494_);
lean_inc_ref(v___x_3510_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set_tag(v___x_3507_, 7);
lean_ctor_set(v___x_3507_, 1, v___x_3510_);
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3512_ = v___x_3507_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3513_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3516_ = l_Lean_indentD(v___x_3515_);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3514_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3510_);
v___x_3521_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3522_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3523_;
}
}
else
{
lean_object* v_val_3525_; lean_object* v___x_3527_; 
lean_del_object(v___x_3507_);
lean_dec(v___x_3494_);
lean_dec(v_stx_2370_);
v_val_3525_ = lean_ctor_get(v_fst_3505_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_fst_3505_, 1);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v_val_3525_);
v___x_3527_ = v___x_3503_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_val_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v___x_3494_);
lean_dec(v_stx_2370_);
v_a_3532_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3500_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3500_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
if (v___x_3492_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3540_ = l_Lean_Syntax_getArg(v___x_3491_, v___x_3367_);
lean_dec(v___x_3491_);
v___x_3541_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3542_ = l_Lean_Syntax_isOfKind(v___x_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v_env_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3543_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3544_ = lean_st_ref_get(v_a_2376_);
v_env_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc_ref(v_env_3545_);
lean_dec(v___x_3544_);
v___x_3546_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3547_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3546_, v_env_3545_, v___x_3543_);
v___x_3548_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3549_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3547_, v___x_3548_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3547_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3580_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3552_ = v___x_3549_;
v_isShared_3553_ = v_isSharedCheck_3580_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3549_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3580_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v_fst_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3578_; 
v_fst_3554_ = lean_ctor_get(v_a_3550_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_a_3550_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v_a_3550_, 1);
lean_dec(v_unused_3579_);
v___x_3556_ = v_a_3550_;
v_isShared_3557_ = v_isSharedCheck_3578_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_fst_3554_);
lean_dec(v_a_3550_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3578_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
if (lean_obj_tag(v_fst_3554_) == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
lean_del_object(v___x_3552_);
v___x_3558_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3559_ = l_Lean_MessageData_ofName(v___x_3543_);
lean_inc_ref(v___x_3559_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set_tag(v___x_3556_, 7);
lean_ctor_set(v___x_3556_, 1, v___x_3559_);
lean_ctor_set(v___x_3556_, 0, v___x_3558_);
v___x_3561_ = v___x_3556_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3562_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3565_ = l_Lean_indentD(v___x_3564_);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3563_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set(v___x_3569_, 1, v___x_3559_);
v___x_3570_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3571_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3572_;
}
}
else
{
lean_object* v_val_3574_; lean_object* v___x_3576_; 
lean_del_object(v___x_3556_);
lean_dec(v___x_3543_);
lean_dec(v_stx_2370_);
v_val_3574_ = lean_ctor_get(v_fst_3554_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v_fst_3554_, 1);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v_val_3574_);
v___x_3576_ = v___x_3552_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_val_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___x_3543_);
lean_dec(v_stx_2370_);
v_a_3581_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3549_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3549_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
v___y_3386_ = v_a_2371_;
v___y_3387_ = v_a_2372_;
v___y_3388_ = v_a_2373_;
v___y_3389_ = v_a_2374_;
v___y_3390_ = v_a_2375_;
v___y_3391_ = v_a_2376_;
goto v___jp_3385_;
}
}
else
{
lean_dec(v___x_3491_);
v___y_3386_ = v_a_2371_;
v___y_3387_ = v_a_2372_;
v___y_3388_ = v_a_2373_;
v___y_3389_ = v_a_2374_;
v___y_3390_ = v_a_2375_;
v___y_3391_ = v_a_2376_;
goto v___jp_3385_;
}
}
}
else
{
lean_dec(v___x_3491_);
v___y_3386_ = v_a_2371_;
v___y_3387_ = v_a_2372_;
v___y_3388_ = v_a_2373_;
v___y_3389_ = v_a_2374_;
v___y_3390_ = v_a_2375_;
v___y_3391_ = v_a_2376_;
goto v___jp_3385_;
}
v___jp_3369_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = lean_unsigned_to_nat(3u);
v___x_3377_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3376_);
lean_dec(v_stx_2370_);
v___x_3378_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3377_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; uint8_t v_breaks_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v_breaks_3380_ = lean_ctor_get_uint8(v_a_3379_, sizeof(void*)*2);
if (v_breaks_3380_ == 0)
{
uint8_t v_returnsEarly_3381_; lean_object* v_reassigns_3382_; 
v_returnsEarly_3381_ = lean_ctor_get_uint8(v_a_3379_, sizeof(void*)*2 + 2);
v_reassigns_3382_ = lean_ctor_get(v_a_3379_, 1);
lean_inc(v_reassigns_3382_);
lean_dec(v_a_3379_);
v___y_2783_ = v_returnsEarly_3381_;
v___y_2784_ = v_reassigns_3382_;
v___y_2785_ = v___x_3367_;
v___y_2786_ = v___x_2790_;
goto v___jp_2782_;
}
else
{
uint8_t v_returnsEarly_3383_; lean_object* v_reassigns_3384_; 
v_returnsEarly_3383_ = lean_ctor_get_uint8(v_a_3379_, sizeof(void*)*2 + 2);
v_reassigns_3384_ = lean_ctor_get(v_a_3379_, 1);
lean_inc(v_reassigns_3384_);
lean_dec(v_a_3379_);
v___y_2783_ = v_returnsEarly_3383_;
v___y_2784_ = v_reassigns_3384_;
v___y_2785_ = v___x_3368_;
v___y_2786_ = v___x_2781_;
goto v___jp_2782_;
}
}
else
{
return v___x_3378_;
}
}
v___jp_3385_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3392_ = lean_unsigned_to_nat(2u);
v___x_3393_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3392_);
v___x_3394_ = l_Lean_Syntax_isNone(v___x_3393_);
if (v___x_3394_ == 0)
{
uint8_t v___x_3395_; 
lean_inc(v___x_3393_);
v___x_3395_ = l_Lean_Syntax_matchesNull(v___x_3393_, v___x_3368_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_env_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_dec(v___x_3393_);
lean_inc_n(v_stx_2370_, 2);
v___x_3396_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3397_ = lean_st_ref_get(v___y_3391_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc_ref(v_env_3398_);
lean_dec(v___x_3397_);
v___x_3399_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3400_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3399_, v_env_3398_, v___x_3396_);
v___x_3401_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3402_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3400_, v___x_3401_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___x_3400_);
if (lean_obj_tag(v___x_3402_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3433_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3433_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3433_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_fst_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3431_; 
v_fst_3407_ = lean_ctor_get(v_a_3403_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_a_3403_);
if (v_isSharedCheck_3431_ == 0)
{
lean_object* v_unused_3432_; 
v_unused_3432_ = lean_ctor_get(v_a_3403_, 1);
lean_dec(v_unused_3432_);
v___x_3409_ = v_a_3403_;
v_isShared_3410_ = v_isSharedCheck_3431_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_fst_3407_);
lean_dec(v_a_3403_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3431_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
if (lean_obj_tag(v_fst_3407_) == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_del_object(v___x_3405_);
v___x_3411_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3412_ = l_Lean_MessageData_ofName(v___x_3396_);
lean_inc_ref(v___x_3412_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set_tag(v___x_3409_, 7);
lean_ctor_set(v___x_3409_, 1, v___x_3412_);
lean_ctor_set(v___x_3409_, 0, v___x_3411_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3415_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3418_ = l_Lean_indentD(v___x_3417_);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3416_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3412_);
v___x_3423_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3424_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
return v___x_3425_;
}
}
else
{
lean_object* v_val_3427_; lean_object* v___x_3429_; 
lean_del_object(v___x_3409_);
lean_dec(v___x_3396_);
lean_dec(v_stx_2370_);
v_val_3427_ = lean_ctor_get(v_fst_3407_, 0);
lean_inc(v_val_3427_);
lean_dec_ref_known(v_fst_3407_, 1);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 0, v_val_3427_);
v___x_3429_ = v___x_3405_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_val_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v___x_3396_);
lean_dec(v_stx_2370_);
v_a_3434_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3402_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3402_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
if (v___x_3394_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3442_ = l_Lean_Syntax_getArg(v___x_3393_, v___x_3367_);
lean_dec(v___x_3393_);
v___x_3443_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3444_ = l_Lean_Syntax_isOfKind(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v_env_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3445_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3446_ = lean_st_ref_get(v___y_3391_);
v_env_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc_ref(v_env_3447_);
lean_dec(v___x_3446_);
v___x_3448_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3449_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3448_, v_env_3447_, v___x_3445_);
v___x_3450_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3451_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3449_, v___x_3450_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___x_3449_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3482_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3482_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3482_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v_fst_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3480_; 
v_fst_3456_ = lean_ctor_get(v_a_3452_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; 
v_unused_3481_ = lean_ctor_get(v_a_3452_, 1);
lean_dec(v_unused_3481_);
v___x_3458_ = v_a_3452_;
v_isShared_3459_ = v_isSharedCheck_3480_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_fst_3456_);
lean_dec(v_a_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3480_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
if (lean_obj_tag(v_fst_3456_) == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
lean_del_object(v___x_3454_);
v___x_3460_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3461_ = l_Lean_MessageData_ofName(v___x_3445_);
lean_inc_ref(v___x_3461_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 7);
lean_ctor_set(v___x_3458_, 1, v___x_3461_);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3463_ = v___x_3458_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3464_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3467_ = l_Lean_indentD(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3465_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v___x_3461_);
v___x_3472_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3473_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
return v___x_3474_;
}
}
else
{
lean_object* v_val_3476_; lean_object* v___x_3478_; 
lean_del_object(v___x_3458_);
lean_dec(v___x_3445_);
lean_dec(v_stx_2370_);
v_val_3476_ = lean_ctor_get(v_fst_3456_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v_fst_3456_, 1);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v_val_3476_);
v___x_3478_ = v___x_3454_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_val_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v___x_3445_);
lean_dec(v_stx_2370_);
v_a_3483_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3451_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3451_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
v___y_3370_ = v___y_3386_;
v___y_3371_ = v___y_3387_;
v___y_3372_ = v___y_3388_;
v___y_3373_ = v___y_3389_;
v___y_3374_ = v___y_3390_;
v___y_3375_ = v___y_3391_;
goto v___jp_3369_;
}
}
else
{
lean_dec(v___x_3393_);
v___y_3370_ = v___y_3386_;
v___y_3371_ = v___y_3387_;
v___y_3372_ = v___y_3388_;
v___y_3373_ = v___y_3389_;
v___y_3374_ = v___y_3390_;
v___y_3375_ = v___y_3391_;
goto v___jp_3369_;
}
}
}
else
{
lean_dec(v___x_3393_);
v___y_3370_ = v___y_3386_;
v___y_3371_ = v___y_3387_;
v___y_3372_ = v___y_3388_;
v___y_3373_ = v___y_3389_;
v___y_3374_ = v___y_3390_;
v___y_3375_ = v___y_3391_;
goto v___jp_3369_;
}
}
}
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3726_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = lean_unsigned_to_nat(1u);
v___x_3875_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3590_);
v___x_3876_ = l_Lean_Syntax_getArgs(v___x_3875_);
lean_dec(v___x_3875_);
v___x_3877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3878_ = lean_array_get_size(v___x_3876_);
v___x_3879_ = lean_nat_dec_lt(v___x_3589_, v___x_3878_);
if (v___x_3879_ == 0)
{
lean_dec_ref(v___x_3876_);
v___y_3726_ = v___x_3877_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; size_t v___x_3882_; size_t v___x_3883_; lean_object* v___x_3884_; lean_object* v_snd_3885_; 
v___x_3880_ = lean_box(v___x_3879_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
lean_ctor_set(v___x_3881_, 1, v___x_3877_);
v___x_3882_ = ((size_t)0ULL);
v___x_3883_ = lean_usize_of_nat(v___x_3878_);
v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2781_, v___x_2779_, v___x_3876_, v___x_3882_, v___x_3883_, v___x_3881_);
lean_dec_ref(v___x_3876_);
v_snd_3885_ = lean_ctor_get(v___x_3884_, 1);
lean_inc(v_snd_3885_);
lean_dec_ref(v___x_3884_);
v___y_3726_ = v_snd_3885_;
goto v___jp_3725_;
}
v___jp_3591_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = lean_unsigned_to_nat(5u);
v___x_3599_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3598_);
lean_dec(v_stx_2370_);
v___x_3600_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3599_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3618_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3618_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3618_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
uint8_t v_returnsEarly_3605_; lean_object* v_reassigns_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3616_; 
v_returnsEarly_3605_ = lean_ctor_get_uint8(v_a_3601_, sizeof(void*)*2 + 2);
v_reassigns_3606_ = lean_ctor_get(v_a_3601_, 1);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_a_3601_, 0);
lean_dec(v_unused_3617_);
v___x_3608_ = v_a_3601_;
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_reassigns_3606_);
lean_dec(v_a_3601_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3616_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3590_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_reassigns_3606_);
lean_ctor_set_uint8(v_reuseFailAlloc_3615_, sizeof(void*)*2 + 2, v_returnsEarly_3605_);
v___x_3611_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; 
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*2, v___x_2779_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*2 + 1, v___x_2779_);
lean_ctor_set_uint8(v___x_3611_, sizeof(void*)*2 + 3, v___x_2779_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3611_);
v___x_3613_ = v___x_3603_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
else
{
return v___x_3600_;
}
}
v___jp_3619_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3626_ = lean_unsigned_to_nat(3u);
v___x_3627_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3626_);
v___x_3628_ = l_Lean_Syntax_isNone(v___x_3627_);
if (v___x_3628_ == 0)
{
uint8_t v___x_3629_; 
lean_inc(v___x_3627_);
v___x_3629_ = l_Lean_Syntax_matchesNull(v___x_3627_, v___x_3590_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_env_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v___x_3627_);
lean_inc_n(v_stx_2370_, 2);
v___x_3630_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3631_ = lean_st_ref_get(v___y_3625_);
v_env_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc_ref(v_env_3632_);
lean_dec(v___x_3631_);
v___x_3633_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3634_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3633_, v_env_3632_, v___x_3630_);
v___x_3635_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3636_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3634_, v___x_3635_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___x_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3667_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3667_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3667_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_fst_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3665_; 
v_fst_3641_ = lean_ctor_get(v_a_3637_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3637_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_a_3637_, 1);
lean_dec(v_unused_3666_);
v___x_3643_ = v_a_3637_;
v_isShared_3644_ = v_isSharedCheck_3665_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_fst_3641_);
lean_dec(v_a_3637_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3665_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
if (lean_obj_tag(v_fst_3641_) == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
lean_del_object(v___x_3639_);
v___x_3645_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3646_ = l_Lean_MessageData_ofName(v___x_3630_);
lean_inc_ref(v___x_3646_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 7);
lean_ctor_set(v___x_3643_, 1, v___x_3646_);
lean_ctor_set(v___x_3643_, 0, v___x_3645_);
v___x_3648_ = v___x_3643_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3649_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3652_ = l_Lean_indentD(v___x_3651_);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3650_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
lean_ctor_set(v___x_3656_, 1, v___x_3646_);
v___x_3657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3658_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
return v___x_3659_;
}
}
else
{
lean_object* v_val_3661_; lean_object* v___x_3663_; 
lean_del_object(v___x_3643_);
lean_dec(v___x_3630_);
lean_dec(v_stx_2370_);
v_val_3661_ = lean_ctor_get(v_fst_3641_, 0);
lean_inc(v_val_3661_);
lean_dec_ref_known(v_fst_3641_, 1);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v_val_3661_);
v___x_3663_ = v___x_3639_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_val_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v___x_3630_);
lean_dec(v_stx_2370_);
v_a_3668_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3636_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3636_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
if (v___x_3628_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3676_ = l_Lean_Syntax_getArg(v___x_3627_, v___x_3589_);
lean_dec(v___x_3627_);
v___x_3677_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3678_ = l_Lean_Syntax_isOfKind(v___x_3676_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_env_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3679_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3680_ = lean_st_ref_get(v___y_3625_);
v_env_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc_ref(v_env_3681_);
lean_dec(v___x_3680_);
v___x_3682_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3683_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3682_, v_env_3681_, v___x_3679_);
v___x_3684_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3685_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3683_, v___x_3684_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___x_3683_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3716_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3716_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3716_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v_fst_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3714_; 
v_fst_3690_ = lean_ctor_get(v_a_3686_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_a_3686_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; 
v_unused_3715_ = lean_ctor_get(v_a_3686_, 1);
lean_dec(v_unused_3715_);
v___x_3692_ = v_a_3686_;
v_isShared_3693_ = v_isSharedCheck_3714_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_fst_3690_);
lean_dec(v_a_3686_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3714_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
if (lean_obj_tag(v_fst_3690_) == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
lean_del_object(v___x_3688_);
v___x_3694_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3695_ = l_Lean_MessageData_ofName(v___x_3679_);
lean_inc_ref(v___x_3695_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 7);
lean_ctor_set(v___x_3692_, 1, v___x_3695_);
lean_ctor_set(v___x_3692_, 0, v___x_3694_);
v___x_3697_ = v___x_3692_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3698_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v___x_3700_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3701_ = l_Lean_indentD(v___x_3700_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3699_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v___x_3695_);
v___x_3706_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3707_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
return v___x_3708_;
}
}
else
{
lean_object* v_val_3710_; lean_object* v___x_3712_; 
lean_del_object(v___x_3692_);
lean_dec(v___x_3679_);
lean_dec(v_stx_2370_);
v_val_3710_ = lean_ctor_get(v_fst_3690_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v_fst_3690_, 1);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v_val_3710_);
v___x_3712_ = v___x_3688_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_val_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v___x_3679_);
lean_dec(v_stx_2370_);
v_a_3717_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3685_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3685_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
else
{
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v___y_3622_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___y_3624_;
v___y_3597_ = v___y_3625_;
goto v___jp_3591_;
}
}
else
{
lean_dec(v___x_3627_);
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v___y_3622_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___y_3624_;
v___y_3597_ = v___y_3625_;
goto v___jp_3591_;
}
}
}
else
{
lean_dec(v___x_3627_);
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v___y_3622_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___y_3624_;
v___y_3597_ = v___y_3625_;
goto v___jp_3591_;
}
}
v___jp_3725_:
{
size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v_sz_3727_ = lean_array_size(v___y_3726_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3727_, v___x_3728_, v___y_3726_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v_env_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3730_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3731_ = lean_st_ref_get(v_a_2376_);
v_env_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc_ref(v_env_3732_);
lean_dec(v___x_3731_);
v___x_3733_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3734_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3733_, v_env_3732_, v___x_3730_);
v___x_3735_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3736_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3734_, v___x_3735_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3734_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3767_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3767_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3767_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_fst_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3765_; 
v_fst_3741_ = lean_ctor_get(v_a_3737_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_a_3737_);
if (v_isSharedCheck_3765_ == 0)
{
lean_object* v_unused_3766_; 
v_unused_3766_ = lean_ctor_get(v_a_3737_, 1);
lean_dec(v_unused_3766_);
v___x_3743_ = v_a_3737_;
v_isShared_3744_ = v_isSharedCheck_3765_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_fst_3741_);
lean_dec(v_a_3737_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3765_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
if (lean_obj_tag(v_fst_3741_) == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
lean_del_object(v___x_3739_);
v___x_3745_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3746_ = l_Lean_MessageData_ofName(v___x_3730_);
lean_inc_ref(v___x_3746_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 7);
lean_ctor_set(v___x_3743_, 1, v___x_3746_);
lean_ctor_set(v___x_3743_, 0, v___x_3745_);
v___x_3748_ = v___x_3743_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3749_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3752_ = l_Lean_indentD(v___x_3751_);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3750_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set(v___x_3756_, 1, v___x_3746_);
v___x_3757_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3758_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3759_;
}
}
else
{
lean_object* v_val_3761_; lean_object* v___x_3763_; 
lean_del_object(v___x_3743_);
lean_dec(v___x_3730_);
lean_dec(v_stx_2370_);
v_val_3761_ = lean_ctor_get(v_fst_3741_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v_fst_3741_, 1);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_val_3761_);
v___x_3763_ = v___x_3739_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_val_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v___x_3730_);
lean_dec(v_stx_2370_);
v_a_3768_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3736_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3736_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
lean_dec_ref_known(v___x_3729_, 1);
v___x_3776_ = lean_unsigned_to_nat(2u);
v___x_3777_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3776_);
v___x_3778_ = l_Lean_Syntax_isNone(v___x_3777_);
if (v___x_3778_ == 0)
{
uint8_t v___x_3779_; 
lean_inc(v___x_3777_);
v___x_3779_ = l_Lean_Syntax_matchesNull(v___x_3777_, v___x_3590_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v_env_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec(v___x_3777_);
lean_inc_n(v_stx_2370_, 2);
v___x_3780_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3781_ = lean_st_ref_get(v_a_2376_);
v_env_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc_ref(v_env_3782_);
lean_dec(v___x_3781_);
v___x_3783_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3784_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3783_, v_env_3782_, v___x_3780_);
v___x_3785_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3786_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3784_, v___x_3785_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3784_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3817_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3817_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3817_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_fst_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3815_; 
v_fst_3791_ = lean_ctor_get(v_a_3787_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_a_3787_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_a_3787_, 1);
lean_dec(v_unused_3816_);
v___x_3793_ = v_a_3787_;
v_isShared_3794_ = v_isSharedCheck_3815_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_fst_3791_);
lean_dec(v_a_3787_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3815_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
if (lean_obj_tag(v_fst_3791_) == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
lean_del_object(v___x_3789_);
v___x_3795_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3796_ = l_Lean_MessageData_ofName(v___x_3780_);
lean_inc_ref(v___x_3796_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 7);
lean_ctor_set(v___x_3793_, 1, v___x_3796_);
lean_ctor_set(v___x_3793_, 0, v___x_3795_);
v___x_3798_ = v___x_3793_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3799_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3802_ = l_Lean_indentD(v___x_3801_);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3800_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3796_);
v___x_3807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3808_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3809_;
}
}
else
{
lean_object* v_val_3811_; lean_object* v___x_3813_; 
lean_del_object(v___x_3793_);
lean_dec(v___x_3780_);
lean_dec(v_stx_2370_);
v_val_3811_ = lean_ctor_get(v_fst_3791_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v_fst_3791_, 1);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v_val_3811_);
v___x_3813_ = v___x_3789_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_val_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v___x_3780_);
lean_dec(v_stx_2370_);
v_a_3818_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3786_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3786_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
if (v___x_3778_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3826_ = l_Lean_Syntax_getArg(v___x_3777_, v___x_3589_);
lean_dec(v___x_3777_);
v___x_3827_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3828_ = l_Lean_Syntax_isOfKind(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v_env_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3829_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3830_ = lean_st_ref_get(v_a_2376_);
v_env_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc_ref(v_env_3831_);
lean_dec(v___x_3830_);
v___x_3832_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3833_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3832_, v_env_3831_, v___x_3829_);
v___x_3834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3835_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3833_, v___x_3834_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3833_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3866_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3838_ = v___x_3835_;
v_isShared_3839_ = v_isSharedCheck_3866_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3835_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3866_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v_fst_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3864_; 
v_fst_3840_ = lean_ctor_get(v_a_3836_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_a_3836_);
if (v_isSharedCheck_3864_ == 0)
{
lean_object* v_unused_3865_; 
v_unused_3865_ = lean_ctor_get(v_a_3836_, 1);
lean_dec(v_unused_3865_);
v___x_3842_ = v_a_3836_;
v_isShared_3843_ = v_isSharedCheck_3864_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_fst_3840_);
lean_dec(v_a_3836_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3864_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
if (lean_obj_tag(v_fst_3840_) == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
lean_del_object(v___x_3838_);
v___x_3844_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3845_ = l_Lean_MessageData_ofName(v___x_3829_);
lean_inc_ref(v___x_3845_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set_tag(v___x_3842_, 7);
lean_ctor_set(v___x_3842_, 1, v___x_3845_);
lean_ctor_set(v___x_3842_, 0, v___x_3844_);
v___x_3847_ = v___x_3842_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3848_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3851_ = l_Lean_indentD(v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v___x_3845_);
v___x_3856_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3857_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3858_;
}
}
else
{
lean_object* v_val_3860_; lean_object* v___x_3862_; 
lean_del_object(v___x_3842_);
lean_dec(v___x_3829_);
lean_dec(v_stx_2370_);
v_val_3860_ = lean_ctor_get(v_fst_3840_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v_fst_3840_, 1);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v_val_3860_);
v___x_3862_ = v___x_3838_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_val_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec(v___x_3829_);
lean_dec(v_stx_2370_);
v_a_3867_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3835_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3835_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
v___y_3620_ = v_a_2371_;
v___y_3621_ = v_a_2372_;
v___y_3622_ = v_a_2373_;
v___y_3623_ = v_a_2374_;
v___y_3624_ = v_a_2375_;
v___y_3625_ = v_a_2376_;
goto v___jp_3619_;
}
}
else
{
lean_dec(v___x_3777_);
v___y_3620_ = v_a_2371_;
v___y_3621_ = v_a_2372_;
v___y_3622_ = v_a_2373_;
v___y_3623_ = v_a_2374_;
v___y_3624_ = v_a_2375_;
v___y_3625_ = v_a_2376_;
goto v___jp_3619_;
}
}
}
else
{
lean_dec(v___x_3777_);
v___y_3620_ = v_a_2371_;
v___y_3621_ = v_a_2372_;
v___y_3622_ = v_a_2373_;
v___y_3623_ = v_a_2374_;
v___y_3624_ = v_a_2375_;
v___y_3625_ = v_a_2376_;
goto v___jp_3619_;
}
}
}
}
v___jp_2782_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2787_, 0, v___y_2785_);
lean_ctor_set(v___x_2787_, 1, v___y_2784_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2, v___x_2781_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2 + 1, v___x_2781_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2 + 2, v___y_2783_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*2 + 3, v___y_2786_);
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3886_ = lean_unsigned_to_nat(1u);
v___x_3887_ = lean_unsigned_to_nat(3u);
v___x_3888_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3887_);
lean_dec(v_stx_2370_);
v___x_3889_ = l_Lean_NameSet_empty;
v___x_3890_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3890_, 0, v___x_3886_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
lean_ctor_set_uint8(v___x_3890_, sizeof(void*)*2, v___x_2777_);
lean_ctor_set_uint8(v___x_3890_, sizeof(void*)*2 + 1, v___x_2777_);
lean_ctor_set_uint8(v___x_3890_, sizeof(void*)*2 + 2, v___x_2777_);
lean_ctor_set_uint8(v___x_3890_, sizeof(void*)*2 + 3, v___x_2777_);
v___x_3891_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3888_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3900_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3890_, v_a_3892_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3896_);
v___x_3898_ = v___x_3894_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
else
{
lean_dec_ref_known(v___x_3890_, 2);
return v___x_3891_;
}
}
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; size_t v_sz_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v___x_3901_ = lean_unsigned_to_nat(4u);
v___x_3902_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3901_);
v___x_3903_ = l_Lean_Syntax_getArgs(v___x_3902_);
lean_dec(v___x_3902_);
v_sz_3904_ = lean_array_size(v___x_3903_);
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3904_, v___x_3905_, v___x_3903_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v_env_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_inc_n(v_stx_2370_, 2);
v___x_3907_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3908_ = lean_st_ref_get(v_a_2376_);
v_env_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc_ref(v_env_3909_);
lean_dec(v___x_3908_);
v___x_3910_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3911_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3910_, v_env_3909_, v___x_3907_);
v___x_3912_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3913_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3911_, v___x_3912_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3911_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3944_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3944_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3944_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v_fst_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3942_; 
v_fst_3918_ = lean_ctor_get(v_a_3914_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3914_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v_a_3914_, 1);
lean_dec(v_unused_3943_);
v___x_3920_ = v_a_3914_;
v_isShared_3921_ = v_isSharedCheck_3942_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_fst_3918_);
lean_dec(v_a_3914_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3942_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_fst_3918_) == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_del_object(v___x_3916_);
v___x_3922_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3923_ = l_Lean_MessageData_ofName(v___x_3907_);
lean_inc_ref(v___x_3923_);
if (v_isShared_3921_ == 0)
{
lean_ctor_set_tag(v___x_3920_, 7);
lean_ctor_set(v___x_3920_, 1, v___x_3923_);
lean_ctor_set(v___x_3920_, 0, v___x_3922_);
v___x_3925_ = v___x_3920_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3926_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3925_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_3929_ = l_Lean_indentD(v___x_3928_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3927_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3923_);
v___x_3934_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3933_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3935_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_3936_;
}
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3940_; 
lean_del_object(v___x_3920_);
lean_dec(v___x_3907_);
lean_dec(v_stx_2370_);
v_val_3938_ = lean_ctor_get(v_fst_3918_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v_fst_3918_, 1);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v_val_3938_);
v___x_3940_ = v___x_3916_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_val_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v___x_3907_);
lean_dec(v_stx_2370_);
v_a_3945_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3913_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3913_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_object* v_val_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_4040_; 
v_val_3953_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_3955_ = v___x_3906_;
v_isShared_3956_ = v_isSharedCheck_4040_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_val_3953_);
lean_dec(v___x_3906_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_4040_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v_elseSeq_x3f_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3957_ = lean_unsigned_to_nat(3u);
v___x_3958_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3957_);
v___x_3983_ = lean_unsigned_to_nat(5u);
v___x_3984_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_3983_);
v___x_3985_ = l_Lean_Syntax_isNone(v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; uint8_t v___x_3987_; 
v___x_3986_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3984_);
v___x_3987_ = l_Lean_Syntax_matchesNull(v___x_3984_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v_env_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_dec(v___x_3984_);
lean_dec(v___x_3958_);
lean_del_object(v___x_3955_);
lean_dec(v_val_3953_);
lean_inc_n(v_stx_2370_, 2);
v___x_3988_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_3989_ = lean_st_ref_get(v_a_2376_);
v_env_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_3990_);
lean_dec(v___x_3989_);
v___x_3991_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3992_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3991_, v_env_3990_, v___x_3988_);
v___x_3993_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3994_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_3992_, v___x_3993_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_3992_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4025_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4025_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4025_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_fst_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4023_; 
v_fst_3999_ = lean_ctor_get(v_a_3995_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_a_3995_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v_a_3995_, 1);
lean_dec(v_unused_4024_);
v___x_4001_ = v_a_3995_;
v_isShared_4002_ = v_isSharedCheck_4023_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_fst_3999_);
lean_dec(v_a_3995_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4023_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
if (lean_obj_tag(v_fst_3999_) == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
lean_del_object(v___x_3997_);
v___x_4003_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4004_ = l_Lean_MessageData_ofName(v___x_3988_);
lean_inc_ref(v___x_4004_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set_tag(v___x_4001_, 7);
lean_ctor_set(v___x_4001_, 1, v___x_4004_);
lean_ctor_set(v___x_4001_, 0, v___x_4003_);
v___x_4006_ = v___x_4001_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4006_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v___x_4009_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4010_ = l_Lean_indentD(v___x_4009_);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4008_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
lean_ctor_set(v___x_4014_, 1, v___x_4004_);
v___x_4015_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4016_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4017_;
}
}
else
{
lean_object* v_val_4019_; lean_object* v___x_4021_; 
lean_del_object(v___x_4001_);
lean_dec(v___x_3988_);
lean_dec(v_stx_2370_);
v_val_4019_ = lean_ctor_get(v_fst_3999_, 0);
lean_inc(v_val_4019_);
lean_dec_ref_known(v_fst_3999_, 1);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 0, v_val_4019_);
v___x_4021_ = v___x_3997_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec(v___x_3988_);
lean_dec(v_stx_2370_);
v_a_4026_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3994_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3994_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4037_; 
lean_dec(v_stx_2370_);
v___x_4034_ = lean_unsigned_to_nat(1u);
v___x_4035_ = l_Lean_Syntax_getArg(v___x_3984_, v___x_4034_);
lean_dec(v___x_3984_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_4035_);
v___x_4037_ = v___x_3955_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
v_elseSeq_x3f_3960_ = v___x_4037_;
v___y_3961_ = v_a_2371_;
v___y_3962_ = v_a_2372_;
v___y_3963_ = v_a_2373_;
v___y_3964_ = v_a_2374_;
v___y_3965_ = v_a_2375_;
v___y_3966_ = v_a_2376_;
goto v___jp_3959_;
}
}
}
else
{
lean_object* v___x_4039_; 
lean_dec(v___x_3984_);
lean_del_object(v___x_3955_);
lean_dec(v_stx_2370_);
v___x_4039_ = lean_box(0);
v_elseSeq_x3f_3960_ = v___x_4039_;
v___y_3961_ = v_a_2371_;
v___y_3962_ = v_a_2372_;
v___y_3963_ = v_a_2373_;
v___y_3964_ = v_a_2374_;
v___y_3965_ = v_a_2375_;
v___y_3966_ = v_a_2376_;
goto v___jp_3959_;
}
v___jp_3959_:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3969_; size_t v_sz_3970_; lean_object* v___x_3971_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v___x_3969_ = l_Array_reverse___redArg(v_val_3953_);
v_sz_3970_ = lean_array_size(v___x_3969_);
v___x_3971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3969_, v_sz_3970_, v___x_3905_, v_a_3968_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec_ref(v___x_3969_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3973_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3958_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3982_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3982_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3982_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3978_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3974_, v_a_3972_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_3978_);
v___x_3980_ = v___x_3976_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
else
{
lean_dec(v_a_3972_);
return v___x_3973_;
}
}
else
{
lean_dec(v___x_3958_);
return v___x_3971_;
}
}
else
{
lean_dec(v___x_3958_);
lean_dec(v_val_3953_);
return v___x_3967_;
}
}
}
}
}
}
else
{
lean_object* v___x_4041_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___x_4105_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4041_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_unsigned_to_nat(1u);
v___x_4212_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4105_);
v___x_4213_ = l_Lean_Syntax_isNone(v___x_4212_);
if (v___x_4213_ == 0)
{
uint8_t v___x_4214_; 
lean_inc(v___x_4212_);
v___x_4214_ = l_Lean_Syntax_matchesNull(v___x_4212_, v___x_4105_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v_env_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_dec(v___x_4212_);
lean_inc_n(v_stx_2370_, 2);
v___x_4215_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4216_ = lean_st_ref_get(v_a_2376_);
v_env_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc_ref(v_env_4217_);
lean_dec(v___x_4216_);
v___x_4218_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4219_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4218_, v_env_4217_, v___x_4215_);
v___x_4220_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4221_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4219_, v___x_4220_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4219_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4252_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4252_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4252_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_fst_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4250_; 
v_fst_4226_ = lean_ctor_get(v_a_4222_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_a_4222_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v_a_4222_, 1);
lean_dec(v_unused_4251_);
v___x_4228_ = v_a_4222_;
v_isShared_4229_ = v_isSharedCheck_4250_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_fst_4226_);
lean_dec(v_a_4222_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4250_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
if (lean_obj_tag(v_fst_4226_) == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4233_; 
lean_del_object(v___x_4224_);
v___x_4230_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4231_ = l_Lean_MessageData_ofName(v___x_4215_);
lean_inc_ref(v___x_4231_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set_tag(v___x_4228_, 7);
lean_ctor_set(v___x_4228_, 1, v___x_4231_);
lean_ctor_set(v___x_4228_, 0, v___x_4230_);
v___x_4233_ = v___x_4228_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4230_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4234_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4233_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4237_ = l_Lean_indentD(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4235_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4238_);
lean_ctor_set(v___x_4240_, 1, v___x_4239_);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
lean_ctor_set(v___x_4241_, 1, v___x_4231_);
v___x_4242_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4243_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4244_;
}
}
else
{
lean_object* v_val_4246_; lean_object* v___x_4248_; 
lean_del_object(v___x_4228_);
lean_dec(v___x_4215_);
lean_dec(v_stx_2370_);
v_val_4246_ = lean_ctor_get(v_fst_4226_, 0);
lean_inc(v_val_4246_);
lean_dec_ref_known(v_fst_4226_, 1);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v_val_4246_);
v___x_4248_ = v___x_4224_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_val_4246_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v___x_4215_);
lean_dec(v_stx_2370_);
v_a_4253_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4221_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4221_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; 
v___x_4261_ = l_Lean_Syntax_getArg(v___x_4212_, v___x_4041_);
lean_dec(v___x_4212_);
v___x_4262_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4263_ = l_Lean_Syntax_isOfKind(v___x_4261_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_env_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4264_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4265_ = lean_st_ref_get(v_a_2376_);
v_env_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc_ref(v_env_4266_);
lean_dec(v___x_4265_);
v___x_4267_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4268_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4267_, v_env_4266_, v___x_4264_);
v___x_4269_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4270_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4268_, v___x_4269_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4268_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4301_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4301_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4301_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v_fst_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4299_; 
v_fst_4275_ = lean_ctor_get(v_a_4271_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_a_4271_);
if (v_isSharedCheck_4299_ == 0)
{
lean_object* v_unused_4300_; 
v_unused_4300_ = lean_ctor_get(v_a_4271_, 1);
lean_dec(v_unused_4300_);
v___x_4277_ = v_a_4271_;
v_isShared_4278_ = v_isSharedCheck_4299_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_fst_4275_);
lean_dec(v_a_4271_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4299_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
if (lean_obj_tag(v_fst_4275_) == 0)
{
lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4282_; 
lean_del_object(v___x_4273_);
v___x_4279_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4280_ = l_Lean_MessageData_ofName(v___x_4264_);
lean_inc_ref(v___x_4280_);
if (v_isShared_4278_ == 0)
{
lean_ctor_set_tag(v___x_4277_, 7);
lean_ctor_set(v___x_4277_, 1, v___x_4280_);
lean_ctor_set(v___x_4277_, 0, v___x_4279_);
v___x_4282_ = v___x_4277_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4279_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4283_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4286_ = l_Lean_indentD(v___x_4285_);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4284_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
lean_ctor_set(v___x_4290_, 1, v___x_4280_);
v___x_4291_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4292_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4293_;
}
}
else
{
lean_object* v_val_4295_; lean_object* v___x_4297_; 
lean_del_object(v___x_4277_);
lean_dec(v___x_4264_);
lean_dec(v_stx_2370_);
v_val_4295_ = lean_ctor_get(v_fst_4275_, 0);
lean_inc(v_val_4295_);
lean_dec_ref_known(v_fst_4275_, 1);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v_val_4295_);
v___x_4297_ = v___x_4273_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_val_4295_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec(v___x_4264_);
lean_dec(v_stx_2370_);
v_a_4302_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4270_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4270_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
else
{
v___y_4107_ = v_a_2371_;
v___y_4108_ = v_a_2372_;
v___y_4109_ = v_a_2373_;
v___y_4110_ = v_a_2374_;
v___y_4111_ = v_a_2375_;
v___y_4112_ = v_a_2376_;
goto v___jp_4106_;
}
}
}
else
{
lean_dec(v___x_4212_);
v___y_4107_ = v_a_2371_;
v___y_4108_ = v_a_2372_;
v___y_4109_ = v_a_2373_;
v___y_4110_ = v_a_2374_;
v___y_4111_ = v_a_2375_;
v___y_4112_ = v_a_2376_;
goto v___jp_4106_;
}
v___jp_4042_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4049_ = lean_unsigned_to_nat(6u);
v___x_4050_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4049_);
v___x_4051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_4050_);
v___x_4052_ = l_Lean_Syntax_isOfKind(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_env_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec(v___x_4050_);
lean_inc_n(v_stx_2370_, 2);
v___x_4053_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4054_ = lean_st_ref_get(v___y_4048_);
v_env_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc_ref(v_env_4055_);
lean_dec(v___x_4054_);
v___x_4056_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4057_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4056_, v_env_4055_, v___x_4053_);
v___x_4058_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4059_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4057_, v___x_4058_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___x_4057_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4090_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4090_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4090_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v_fst_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4088_; 
v_fst_4064_ = lean_ctor_get(v_a_4060_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_a_4060_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v_a_4060_, 1);
lean_dec(v_unused_4089_);
v___x_4066_ = v_a_4060_;
v_isShared_4067_ = v_isSharedCheck_4088_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_fst_4064_);
lean_dec(v_a_4060_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4088_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
if (lean_obj_tag(v_fst_4064_) == 0)
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4071_; 
lean_del_object(v___x_4062_);
v___x_4068_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4069_ = l_Lean_MessageData_ofName(v___x_4053_);
lean_inc_ref(v___x_4069_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set_tag(v___x_4066_, 7);
lean_ctor_set(v___x_4066_, 1, v___x_4069_);
lean_ctor_set(v___x_4066_, 0, v___x_4068_);
v___x_4071_ = v___x_4066_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4072_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set(v___x_4073_, 1, v___x_4072_);
v___x_4074_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4075_ = l_Lean_indentD(v___x_4074_);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4073_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v___x_4069_);
v___x_4080_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4081_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4082_;
}
}
else
{
lean_object* v_val_4084_; lean_object* v___x_4086_; 
lean_del_object(v___x_4066_);
lean_dec(v___x_4053_);
lean_dec(v_stx_2370_);
v_val_4084_ = lean_ctor_get(v_fst_4064_, 0);
lean_inc(v_val_4084_);
lean_dec_ref_known(v_fst_4064_, 1);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 0, v_val_4084_);
v___x_4086_ = v___x_4062_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_val_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v___x_4053_);
lean_dec(v_stx_2370_);
v_a_4091_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4059_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4059_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; size_t v_sz_4102_; size_t v___x_4103_; lean_object* v___x_4104_; 
lean_dec(v_stx_2370_);
v___x_4099_ = l_Lean_Syntax_getArg(v___x_4050_, v___x_4041_);
lean_dec(v___x_4050_);
v___x_4100_ = l_Lean_Syntax_getArgs(v___x_4099_);
lean_dec(v___x_4099_);
v___x_4101_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4102_ = lean_array_size(v___x_4100_);
v___x_4103_ = ((size_t)0ULL);
v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2773_, v___x_4100_, v_sz_4102_, v___x_4103_, v___x_4101_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec_ref(v___x_4100_);
return v___x_4104_;
}
}
v___jp_4106_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
v___x_4113_ = lean_unsigned_to_nat(2u);
v___x_4114_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4113_);
v___x_4115_ = l_Lean_Syntax_isNone(v___x_4114_);
if (v___x_4115_ == 0)
{
uint8_t v___x_4116_; 
lean_inc(v___x_4114_);
v___x_4116_ = l_Lean_Syntax_matchesNull(v___x_4114_, v___x_4105_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_env_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec(v___x_4114_);
lean_inc_n(v_stx_2370_, 2);
v___x_4117_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4118_ = lean_st_ref_get(v___y_4112_);
v_env_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc_ref(v_env_4119_);
lean_dec(v___x_4118_);
v___x_4120_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4121_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4120_, v_env_4119_, v___x_4117_);
v___x_4122_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4123_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4121_, v___x_4122_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___x_4121_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4154_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4126_ = v___x_4123_;
v_isShared_4127_ = v_isSharedCheck_4154_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4123_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4154_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v_fst_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4152_; 
v_fst_4128_ = lean_ctor_get(v_a_4124_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_a_4124_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v_a_4124_, 1);
lean_dec(v_unused_4153_);
v___x_4130_ = v_a_4124_;
v_isShared_4131_ = v_isSharedCheck_4152_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_fst_4128_);
lean_dec(v_a_4124_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4152_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
if (lean_obj_tag(v_fst_4128_) == 0)
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
lean_del_object(v___x_4126_);
v___x_4132_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4133_ = l_Lean_MessageData_ofName(v___x_4117_);
lean_inc_ref(v___x_4133_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 7);
lean_ctor_set(v___x_4130_, 1, v___x_4133_);
lean_ctor_set(v___x_4130_, 0, v___x_4132_);
v___x_4135_ = v___x_4130_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4136_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4135_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4139_ = l_Lean_indentD(v___x_4138_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4137_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
lean_ctor_set(v___x_4143_, 1, v___x_4133_);
v___x_4144_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4145_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4146_;
}
}
else
{
lean_object* v_val_4148_; lean_object* v___x_4150_; 
lean_del_object(v___x_4130_);
lean_dec(v___x_4117_);
lean_dec(v_stx_2370_);
v_val_4148_ = lean_ctor_get(v_fst_4128_, 0);
lean_inc(v_val_4148_);
lean_dec_ref_known(v_fst_4128_, 1);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v_val_4148_);
v___x_4150_ = v___x_4126_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_val_4148_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec(v___x_4117_);
lean_dec(v_stx_2370_);
v_a_4155_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4123_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4123_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4163_ = l_Lean_Syntax_getArg(v___x_4114_, v___x_4041_);
lean_dec(v___x_4114_);
v___x_4164_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4165_ = l_Lean_Syntax_isOfKind(v___x_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_env_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4166_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4167_ = lean_st_ref_get(v___y_4112_);
v_env_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_ref(v_env_4168_);
lean_dec(v___x_4167_);
v___x_4169_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4170_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4169_, v_env_4168_, v___x_4166_);
v___x_4171_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4172_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4170_, v___x_4171_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___x_4170_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4203_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4203_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4203_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v_fst_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4201_; 
v_fst_4177_ = lean_ctor_get(v_a_4173_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_a_4173_);
if (v_isSharedCheck_4201_ == 0)
{
lean_object* v_unused_4202_; 
v_unused_4202_ = lean_ctor_get(v_a_4173_, 1);
lean_dec(v_unused_4202_);
v___x_4179_ = v_a_4173_;
v_isShared_4180_ = v_isSharedCheck_4201_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_fst_4177_);
lean_dec(v_a_4173_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4201_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
if (lean_obj_tag(v_fst_4177_) == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4184_; 
lean_del_object(v___x_4175_);
v___x_4181_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4182_ = l_Lean_MessageData_ofName(v___x_4166_);
lean_inc_ref(v___x_4182_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set_tag(v___x_4179_, 7);
lean_ctor_set(v___x_4179_, 1, v___x_4182_);
lean_ctor_set(v___x_4179_, 0, v___x_4181_);
v___x_4184_ = v___x_4179_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4185_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4184_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4188_ = l_Lean_indentD(v___x_4187_);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4186_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4182_);
v___x_4193_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4194_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4195_;
}
}
else
{
lean_object* v_val_4197_; lean_object* v___x_4199_; 
lean_del_object(v___x_4179_);
lean_dec(v___x_4166_);
lean_dec(v_stx_2370_);
v_val_4197_ = lean_ctor_get(v_fst_4177_, 0);
lean_inc(v_val_4197_);
lean_dec_ref_known(v_fst_4177_, 1);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v_val_4197_);
v___x_4199_ = v___x_4175_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_val_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec(v___x_4166_);
lean_dec(v_stx_2370_);
v_a_4204_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4172_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4172_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
v___y_4043_ = v___y_4107_;
v___y_4044_ = v___y_4108_;
v___y_4045_ = v___y_4109_;
v___y_4046_ = v___y_4110_;
v___y_4047_ = v___y_4111_;
v___y_4048_ = v___y_4112_;
goto v___jp_4042_;
}
}
}
else
{
lean_dec(v___x_4114_);
v___y_4043_ = v___y_4107_;
v___y_4044_ = v___y_4108_;
v___y_4045_ = v___y_4109_;
v___y_4046_ = v___y_4110_;
v___y_4047_ = v___y_4111_;
v___y_4048_ = v___y_4112_;
goto v___jp_4042_;
}
}
}
}
else
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4310_);
if (v___x_2771_ == 0)
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4312_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4311_);
v___x_4313_ = l_Lean_Syntax_isOfKind(v___x_4311_, v___x_4312_);
if (v___x_4313_ == 0)
{
if (v___x_2771_ == 0)
{
lean_object* v___x_4314_; uint8_t v___x_4315_; 
v___x_4314_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4311_);
v___x_4315_ = l_Lean_Syntax_isOfKind(v___x_4311_, v___x_4314_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v_env_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
lean_dec(v___x_4311_);
lean_inc_n(v_stx_2370_, 2);
v___x_4316_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4317_ = lean_st_ref_get(v_a_2376_);
v_env_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc_ref(v_env_4318_);
lean_dec(v___x_4317_);
v___x_4319_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4320_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4319_, v_env_4318_, v___x_4316_);
v___x_4321_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4322_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4320_, v___x_4321_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4320_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4353_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4353_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4353_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v_fst_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4351_; 
v_fst_4327_ = lean_ctor_get(v_a_4323_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_a_4323_);
if (v_isSharedCheck_4351_ == 0)
{
lean_object* v_unused_4352_; 
v_unused_4352_ = lean_ctor_get(v_a_4323_, 1);
lean_dec(v_unused_4352_);
v___x_4329_ = v_a_4323_;
v_isShared_4330_ = v_isSharedCheck_4351_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_fst_4327_);
lean_dec(v_a_4323_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4351_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
if (lean_obj_tag(v_fst_4327_) == 0)
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; 
lean_del_object(v___x_4325_);
v___x_4331_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4332_ = l_Lean_MessageData_ofName(v___x_4316_);
lean_inc_ref(v___x_4332_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set_tag(v___x_4329_, 7);
lean_ctor_set(v___x_4329_, 1, v___x_4332_);
lean_ctor_set(v___x_4329_, 0, v___x_4331_);
v___x_4334_ = v___x_4329_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4331_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4335_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4338_ = l_Lean_indentD(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4336_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
lean_ctor_set(v___x_4342_, 1, v___x_4332_);
v___x_4343_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4344_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4345_;
}
}
else
{
lean_object* v_val_4347_; lean_object* v___x_4349_; 
lean_del_object(v___x_4329_);
lean_dec(v___x_4316_);
lean_dec(v_stx_2370_);
v_val_4347_ = lean_ctor_get(v_fst_4327_, 0);
lean_inc(v_val_4347_);
lean_dec_ref_known(v_fst_4327_, 1);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v_val_4347_);
v___x_4349_ = v___x_4325_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_val_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec(v___x_4316_);
lean_dec(v_stx_2370_);
v_a_4354_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4322_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4322_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v___x_4362_; 
lean_dec(v_stx_2370_);
v___x_4362_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2460_, v___x_4311_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4362_;
}
}
else
{
lean_object* v___x_4363_; 
lean_dec(v_stx_2370_);
v___x_4363_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2460_, v___x_4311_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4363_;
}
}
else
{
lean_object* v___x_4364_; 
lean_dec(v_stx_2370_);
v___x_4364_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2460_, v___x_4311_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4364_;
}
}
else
{
lean_object* v___x_4365_; 
lean_dec(v_stx_2370_);
v___x_4365_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2460_, v___x_4311_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4365_;
}
}
}
else
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4366_);
if (v___x_2769_ == 0)
{
lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4394_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4367_);
v___x_4395_ = l_Lean_Syntax_isOfKind(v___x_4367_, v___x_4394_);
if (v___x_4395_ == 0)
{
if (v___x_2769_ == 0)
{
lean_object* v___x_4396_; uint8_t v___x_4397_; 
v___x_4396_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4367_);
v___x_4397_ = l_Lean_Syntax_isOfKind(v___x_4367_, v___x_4396_);
if (v___x_4397_ == 0)
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v_env_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_dec(v___x_4367_);
lean_inc_n(v_stx_2370_, 2);
v___x_4398_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4399_ = lean_st_ref_get(v_a_2376_);
v_env_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc_ref(v_env_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4402_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4401_, v_env_4400_, v___x_4398_);
v___x_4403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4404_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4402_, v___x_4403_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4402_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4435_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4435_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4435_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v_fst_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4433_; 
v_fst_4409_ = lean_ctor_get(v_a_4405_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_a_4405_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v_a_4405_, 1);
lean_dec(v_unused_4434_);
v___x_4411_ = v_a_4405_;
v_isShared_4412_ = v_isSharedCheck_4433_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_fst_4409_);
lean_dec(v_a_4405_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4433_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
if (lean_obj_tag(v_fst_4409_) == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
lean_del_object(v___x_4407_);
v___x_4413_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4414_ = l_Lean_MessageData_ofName(v___x_4398_);
lean_inc_ref(v___x_4414_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 7);
lean_ctor_set(v___x_4411_, 1, v___x_4414_);
lean_ctor_set(v___x_4411_, 0, v___x_4413_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4417_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4420_ = l_Lean_indentD(v___x_4419_);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4418_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4424_, 0, v___x_4423_);
lean_ctor_set(v___x_4424_, 1, v___x_4414_);
v___x_4425_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4424_);
lean_ctor_set(v___x_4426_, 1, v___x_4425_);
v___x_4427_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4426_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4427_;
}
}
else
{
lean_object* v_val_4429_; lean_object* v___x_4431_; 
lean_del_object(v___x_4411_);
lean_dec(v___x_4398_);
lean_dec(v_stx_2370_);
v_val_4429_ = lean_ctor_get(v_fst_4409_, 0);
lean_inc(v_val_4429_);
lean_dec_ref_known(v_fst_4409_, 1);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v_val_4429_);
v___x_4431_ = v___x_4407_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_val_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v___x_4398_);
lean_dec(v_stx_2370_);
v_a_4436_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4404_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4404_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_4368_;
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_4368_;
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_4381_;
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_4381_;
}
v___jp_4368_:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4367_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4367_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = lean_box(0);
v___x_4372_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4370_, v___x_4371_, v___x_4371_, v___x_4371_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4372_;
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
v_a_4373_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4369_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4369_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
v___jp_4381_:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4367_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4367_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
v___x_4384_ = lean_box(0);
v___x_4385_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4383_, v___x_4384_, v___x_4384_, v___x_4384_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4385_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4382_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4382_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
}
else
{
lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4444_ = lean_unsigned_to_nat(0u);
v___x_4445_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4444_);
v___x_4446_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4445_);
v___x_4447_ = l_Lean_Syntax_isOfKind(v___x_4445_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v_env_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_dec(v___x_4445_);
lean_inc_n(v_stx_2370_, 2);
v___x_4448_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4449_ = lean_st_ref_get(v_a_2376_);
v_env_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc_ref(v_env_4450_);
lean_dec(v___x_4449_);
v___x_4451_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4452_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4451_, v_env_4450_, v___x_4448_);
v___x_4453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4454_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4452_, v___x_4453_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4452_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4485_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4485_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4485_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_fst_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4483_; 
v_fst_4459_ = lean_ctor_get(v_a_4455_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_a_4455_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; 
v_unused_4484_ = lean_ctor_get(v_a_4455_, 1);
lean_dec(v_unused_4484_);
v___x_4461_ = v_a_4455_;
v_isShared_4462_ = v_isSharedCheck_4483_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_fst_4459_);
lean_dec(v_a_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4483_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
if (lean_obj_tag(v_fst_4459_) == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
lean_del_object(v___x_4457_);
v___x_4463_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4464_ = l_Lean_MessageData_ofName(v___x_4448_);
lean_inc_ref(v___x_4464_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set_tag(v___x_4461_, 7);
lean_ctor_set(v___x_4461_, 1, v___x_4464_);
lean_ctor_set(v___x_4461_, 0, v___x_4463_);
v___x_4466_ = v___x_4461_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v___x_4463_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4467_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4466_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4470_ = l_Lean_indentD(v___x_4469_);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4468_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
lean_ctor_set(v___x_4474_, 1, v___x_4464_);
v___x_4475_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4474_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4476_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4477_;
}
}
else
{
lean_object* v_val_4479_; lean_object* v___x_4481_; 
lean_del_object(v___x_4461_);
lean_dec(v___x_4448_);
lean_dec(v_stx_2370_);
v_val_4479_ = lean_ctor_get(v_fst_4459_, 0);
lean_inc(v_val_4479_);
lean_dec_ref_known(v_fst_4459_, 1);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 0, v_val_4479_);
v___x_4481_ = v___x_4457_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_val_4479_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v___x_4448_);
lean_dec(v_stx_2370_);
v_a_4486_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4454_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4454_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v___x_4494_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4600_ = l_Lean_Syntax_getArg(v___x_4445_, v___x_4494_);
lean_dec(v___x_4445_);
v___x_4601_ = l_Lean_Syntax_isNone(v___x_4600_);
if (v___x_4601_ == 0)
{
uint8_t v___x_4602_; 
v___x_4602_ = l_Lean_Syntax_matchesNull(v___x_4600_, v___x_4494_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v_env_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4603_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4604_ = lean_st_ref_get(v_a_2376_);
v_env_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc_ref(v_env_4605_);
lean_dec(v___x_4604_);
v___x_4606_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4607_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4606_, v_env_4605_, v___x_4603_);
v___x_4608_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4609_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4607_, v___x_4608_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4607_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4640_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4640_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4640_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v_fst_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4638_; 
v_fst_4614_ = lean_ctor_get(v_a_4610_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_a_4610_);
if (v_isSharedCheck_4638_ == 0)
{
lean_object* v_unused_4639_; 
v_unused_4639_ = lean_ctor_get(v_a_4610_, 1);
lean_dec(v_unused_4639_);
v___x_4616_ = v_a_4610_;
v_isShared_4617_ = v_isSharedCheck_4638_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_fst_4614_);
lean_dec(v_a_4610_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4638_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
if (lean_obj_tag(v_fst_4614_) == 0)
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
lean_del_object(v___x_4612_);
v___x_4618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4619_ = l_Lean_MessageData_ofName(v___x_4603_);
lean_inc_ref(v___x_4619_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set_tag(v___x_4616_, 7);
lean_ctor_set(v___x_4616_, 1, v___x_4619_);
lean_ctor_set(v___x_4616_, 0, v___x_4618_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4622_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4621_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4625_ = l_Lean_indentD(v___x_4624_);
v___x_4626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4623_);
lean_ctor_set(v___x_4626_, 1, v___x_4625_);
v___x_4627_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4626_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
lean_ctor_set(v___x_4629_, 1, v___x_4619_);
v___x_4630_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
v___x_4632_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4631_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4632_;
}
}
else
{
lean_object* v_val_4634_; lean_object* v___x_4636_; 
lean_del_object(v___x_4616_);
lean_dec(v___x_4603_);
lean_dec(v_stx_2370_);
v_val_4634_ = lean_ctor_get(v_fst_4614_, 0);
lean_inc(v_val_4634_);
lean_dec_ref_known(v_fst_4614_, 1);
if (v_isShared_4613_ == 0)
{
lean_ctor_set(v___x_4612_, 0, v_val_4634_);
v___x_4636_ = v___x_4612_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_val_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4648_; 
lean_dec(v___x_4603_);
lean_dec(v_stx_2370_);
v_a_4641_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4648_ == 0)
{
v___x_4643_ = v___x_4609_;
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4609_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4648_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4646_; 
if (v_isShared_4644_ == 0)
{
v___x_4646_ = v___x_4643_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_a_4641_);
v___x_4646_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
return v___x_4646_;
}
}
}
}
else
{
v___y_4496_ = v_a_2371_;
v___y_4497_ = v_a_2372_;
v___y_4498_ = v_a_2373_;
v___y_4499_ = v_a_2374_;
v___y_4500_ = v_a_2375_;
v___y_4501_ = v_a_2376_;
goto v___jp_4495_;
}
}
else
{
lean_dec(v___x_4600_);
v___y_4496_ = v_a_2371_;
v___y_4497_ = v_a_2372_;
v___y_4498_ = v_a_2373_;
v___y_4499_ = v_a_2374_;
v___y_4500_ = v_a_2375_;
v___y_4501_ = v_a_2376_;
goto v___jp_4495_;
}
v___jp_4495_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4502_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4494_);
v___x_4503_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4502_);
v___x_4504_ = l_Lean_Syntax_isOfKind(v___x_4502_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v_env_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec(v___x_4502_);
lean_inc_n(v_stx_2370_, 2);
v___x_4505_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4506_ = lean_st_ref_get(v___y_4501_);
v_env_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc_ref(v_env_4507_);
lean_dec(v___x_4506_);
v___x_4508_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4509_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4508_, v_env_4507_, v___x_4505_);
v___x_4510_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4511_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4509_, v___x_4510_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___x_4509_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4542_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4542_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4542_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v_fst_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4540_; 
v_fst_4516_ = lean_ctor_get(v_a_4512_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_a_4512_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; 
v_unused_4541_ = lean_ctor_get(v_a_4512_, 1);
lean_dec(v_unused_4541_);
v___x_4518_ = v_a_4512_;
v_isShared_4519_ = v_isSharedCheck_4540_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_fst_4516_);
lean_dec(v_a_4512_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4540_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
if (lean_obj_tag(v_fst_4516_) == 0)
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
lean_del_object(v___x_4514_);
v___x_4520_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4521_ = l_Lean_MessageData_ofName(v___x_4505_);
lean_inc_ref(v___x_4521_);
if (v_isShared_4519_ == 0)
{
lean_ctor_set_tag(v___x_4518_, 7);
lean_ctor_set(v___x_4518_, 1, v___x_4521_);
lean_ctor_set(v___x_4518_, 0, v___x_4520_);
v___x_4523_ = v___x_4518_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4535_, 1, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4524_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4523_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4527_ = l_Lean_indentD(v___x_4526_);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4525_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
lean_ctor_set(v___x_4531_, 1, v___x_4521_);
v___x_4532_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4533_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4534_;
}
}
else
{
lean_object* v_val_4536_; lean_object* v___x_4538_; 
lean_del_object(v___x_4518_);
lean_dec(v___x_4505_);
lean_dec(v_stx_2370_);
v_val_4536_ = lean_ctor_get(v_fst_4516_, 0);
lean_inc(v_val_4536_);
lean_dec_ref_known(v_fst_4516_, 1);
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v_val_4536_);
v___x_4538_ = v___x_4514_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_val_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v___x_4505_);
lean_dec(v_stx_2370_);
v_a_4543_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4511_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4511_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v___x_4551_; uint8_t v___x_4552_; 
v___x_4551_ = l_Lean_Syntax_getArg(v___x_4502_, v___x_4494_);
lean_dec(v___x_4502_);
v___x_4552_ = l_Lean_Syntax_isNone(v___x_4551_);
if (v___x_4552_ == 0)
{
uint8_t v___x_4553_; 
v___x_4553_ = l_Lean_Syntax_matchesNull(v___x_4551_, v___x_4494_);
if (v___x_4553_ == 0)
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v_env_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4554_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4555_ = lean_st_ref_get(v___y_4501_);
v_env_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc_ref(v_env_4556_);
lean_dec(v___x_4555_);
v___x_4557_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4558_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4557_, v_env_4556_, v___x_4554_);
v___x_4559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4560_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4558_, v___x_4559_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___x_4558_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4591_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4591_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4591_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v_fst_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4589_; 
v_fst_4565_ = lean_ctor_get(v_a_4561_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_a_4561_);
if (v_isSharedCheck_4589_ == 0)
{
lean_object* v_unused_4590_; 
v_unused_4590_ = lean_ctor_get(v_a_4561_, 1);
lean_dec(v_unused_4590_);
v___x_4567_ = v_a_4561_;
v_isShared_4568_ = v_isSharedCheck_4589_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_fst_4565_);
lean_dec(v_a_4561_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4589_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
if (lean_obj_tag(v_fst_4565_) == 0)
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_del_object(v___x_4563_);
v___x_4569_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4570_ = l_Lean_MessageData_ofName(v___x_4554_);
lean_inc_ref(v___x_4570_);
if (v_isShared_4568_ == 0)
{
lean_ctor_set_tag(v___x_4567_, 7);
lean_ctor_set(v___x_4567_, 1, v___x_4570_);
lean_ctor_set(v___x_4567_, 0, v___x_4569_);
v___x_4572_ = v___x_4567_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4569_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4573_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
v___x_4575_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4576_ = l_Lean_indentD(v___x_4575_);
v___x_4577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4574_);
lean_ctor_set(v___x_4577_, 1, v___x_4576_);
v___x_4578_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4577_);
lean_ctor_set(v___x_4579_, 1, v___x_4578_);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
lean_ctor_set(v___x_4580_, 1, v___x_4570_);
v___x_4581_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4580_);
lean_ctor_set(v___x_4582_, 1, v___x_4581_);
v___x_4583_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4582_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4583_;
}
}
else
{
lean_object* v_val_4585_; lean_object* v___x_4587_; 
lean_del_object(v___x_4567_);
lean_dec(v___x_4554_);
lean_dec(v_stx_2370_);
v_val_4585_ = lean_ctor_get(v_fst_4565_, 0);
lean_inc(v_val_4585_);
lean_dec_ref_known(v_fst_4565_, 1);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v_val_4585_);
v___x_4587_ = v___x_4563_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_val_4585_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec(v___x_4554_);
lean_dec(v_stx_2370_);
v_a_4592_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4560_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4560_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2420_;
}
}
else
{
lean_dec(v___x_4551_);
lean_dec(v_stx_2370_);
goto v___jp_2420_;
}
}
}
}
}
}
else
{
lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v___x_4649_ = lean_unsigned_to_nat(1u);
v___x_4650_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4649_);
v___x_4651_ = l_Lean_Syntax_isNone(v___x_4650_);
if (v___x_4651_ == 0)
{
uint8_t v___x_4652_; 
v___x_4652_ = l_Lean_Syntax_matchesNull(v___x_4650_, v___x_4649_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v_env_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4653_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4654_ = lean_st_ref_get(v_a_2376_);
v_env_4655_ = lean_ctor_get(v___x_4654_, 0);
lean_inc_ref(v_env_4655_);
lean_dec(v___x_4654_);
v___x_4656_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4657_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4656_, v_env_4655_, v___x_4653_);
v___x_4658_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4659_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4657_, v___x_4658_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4657_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4690_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4690_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4690_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_fst_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4688_; 
v_fst_4664_ = lean_ctor_get(v_a_4660_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_a_4660_);
if (v_isSharedCheck_4688_ == 0)
{
lean_object* v_unused_4689_; 
v_unused_4689_ = lean_ctor_get(v_a_4660_, 1);
lean_dec(v_unused_4689_);
v___x_4666_ = v_a_4660_;
v_isShared_4667_ = v_isSharedCheck_4688_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_fst_4664_);
lean_dec(v_a_4660_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4688_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
if (lean_obj_tag(v_fst_4664_) == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4671_; 
lean_del_object(v___x_4662_);
v___x_4668_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4669_ = l_Lean_MessageData_ofName(v___x_4653_);
lean_inc_ref(v___x_4669_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set_tag(v___x_4666_, 7);
lean_ctor_set(v___x_4666_, 1, v___x_4669_);
lean_ctor_set(v___x_4666_, 0, v___x_4668_);
v___x_4671_ = v___x_4666_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4668_);
lean_ctor_set(v_reuseFailAlloc_4683_, 1, v___x_4669_);
v___x_4671_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4672_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
v___x_4674_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4675_ = l_Lean_indentD(v___x_4674_);
v___x_4676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4673_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
v___x_4677_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4676_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
v___x_4679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
lean_ctor_set(v___x_4679_, 1, v___x_4669_);
v___x_4680_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4679_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
v___x_4682_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4681_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4682_;
}
}
else
{
lean_object* v_val_4684_; lean_object* v___x_4686_; 
lean_del_object(v___x_4666_);
lean_dec(v___x_4653_);
lean_dec(v_stx_2370_);
v_val_4684_ = lean_ctor_get(v_fst_4664_, 0);
lean_inc(v_val_4684_);
lean_dec_ref_known(v_fst_4664_, 1);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v_val_4684_);
v___x_4686_ = v___x_4662_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_val_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec(v___x_4653_);
lean_dec(v_stx_2370_);
v_a_4691_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4659_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4659_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
else
{
v___y_2710_ = v_a_2371_;
v___y_2711_ = v_a_2372_;
v___y_2712_ = v_a_2373_;
v___y_2713_ = v_a_2374_;
v___y_2714_ = v_a_2375_;
v___y_2715_ = v_a_2376_;
goto v___jp_2709_;
}
}
else
{
lean_dec(v___x_4650_);
v___y_2710_ = v_a_2371_;
v___y_2711_ = v_a_2372_;
v___y_2712_ = v_a_2373_;
v___y_2713_ = v_a_2374_;
v___y_2714_ = v_a_2375_;
v___y_2715_ = v_a_2376_;
goto v___jp_2709_;
}
}
}
else
{
lean_object* v___x_4699_; lean_object* v___x_4700_; uint8_t v___x_4701_; 
v___x_4699_ = lean_unsigned_to_nat(1u);
v___x_4700_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4699_);
v___x_4701_ = l_Lean_Syntax_isNone(v___x_4700_);
if (v___x_4701_ == 0)
{
uint8_t v___x_4702_; 
v___x_4702_ = l_Lean_Syntax_matchesNull(v___x_4700_, v___x_4699_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v_env_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4703_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4704_ = lean_st_ref_get(v_a_2376_);
v_env_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_env_4705_);
lean_dec(v___x_4704_);
v___x_4706_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4707_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4706_, v_env_4705_, v___x_4703_);
v___x_4708_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4709_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4707_, v___x_4708_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4707_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4740_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4712_ = v___x_4709_;
v_isShared_4713_ = v_isSharedCheck_4740_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4740_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v_fst_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4738_; 
v_fst_4714_ = lean_ctor_get(v_a_4710_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v_a_4710_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; 
v_unused_4739_ = lean_ctor_get(v_a_4710_, 1);
lean_dec(v_unused_4739_);
v___x_4716_ = v_a_4710_;
v_isShared_4717_ = v_isSharedCheck_4738_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_fst_4714_);
lean_dec(v_a_4710_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4738_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
if (lean_obj_tag(v_fst_4714_) == 0)
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
lean_del_object(v___x_4712_);
v___x_4718_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4719_ = l_Lean_MessageData_ofName(v___x_4703_);
lean_inc_ref(v___x_4719_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set_tag(v___x_4716_, 7);
lean_ctor_set(v___x_4716_, 1, v___x_4719_);
lean_ctor_set(v___x_4716_, 0, v___x_4718_);
v___x_4721_ = v___x_4716_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4733_, 1, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4722_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4721_);
lean_ctor_set(v___x_4723_, 1, v___x_4722_);
v___x_4724_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4725_ = l_Lean_indentD(v___x_4724_);
v___x_4726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4723_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
v___x_4727_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4726_);
lean_ctor_set(v___x_4728_, 1, v___x_4727_);
v___x_4729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
lean_ctor_set(v___x_4729_, 1, v___x_4719_);
v___x_4730_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4729_);
lean_ctor_set(v___x_4731_, 1, v___x_4730_);
v___x_4732_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4731_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4732_;
}
}
else
{
lean_object* v_val_4734_; lean_object* v___x_4736_; 
lean_del_object(v___x_4716_);
lean_dec(v___x_4703_);
lean_dec(v_stx_2370_);
v_val_4734_ = lean_ctor_get(v_fst_4714_, 0);
lean_inc(v_val_4734_);
lean_dec_ref_known(v_fst_4714_, 1);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 0, v_val_4734_);
v___x_4736_ = v___x_4712_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_val_4734_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec(v___x_4703_);
lean_dec(v_stx_2370_);
v_a_4741_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4709_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4709_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
else
{
v___y_2641_ = v_a_2371_;
v___y_2642_ = v_a_2372_;
v___y_2643_ = v_a_2373_;
v___y_2644_ = v_a_2374_;
v___y_2645_ = v_a_2375_;
v___y_2646_ = v_a_2376_;
goto v___jp_2640_;
}
}
else
{
lean_dec(v___x_4700_);
v___y_2641_ = v_a_2371_;
v___y_2642_ = v_a_2372_;
v___y_2643_ = v_a_2373_;
v___y_2644_ = v_a_2374_;
v___y_2645_ = v_a_2375_;
v___y_2646_ = v_a_2376_;
goto v___jp_2640_;
}
}
v___jp_2699_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_unsigned_to_nat(3u);
v___x_2707_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2706_);
lean_dec(v_stx_2370_);
v___x_2708_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2698_, v___x_2707_, v___y_2701_, v___y_2705_, v___y_2703_, v___y_2704_, v___y_2702_, v___y_2700_);
return v___x_2708_;
}
v___jp_2709_:
{
if (v___x_2698_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2716_ = lean_unsigned_to_nat(2u);
v___x_2717_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2716_);
v___x_2718_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2719_ = l_Lean_Syntax_isOfKind(v___x_2717_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v_env_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2720_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2721_ = lean_st_ref_get(v___y_2715_);
v_env_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_ref(v_env_2722_);
lean_dec(v___x_2721_);
v___x_2723_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2724_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2723_, v_env_2722_, v___x_2720_);
v___x_2725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2726_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2724_, v___x_2725_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___x_2724_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2757_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2757_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2757_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_fst_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2755_; 
v_fst_2731_ = lean_ctor_get(v_a_2727_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2727_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_a_2727_, 1);
lean_dec(v_unused_2756_);
v___x_2733_ = v_a_2727_;
v_isShared_2734_ = v_isSharedCheck_2755_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_fst_2731_);
lean_dec(v_a_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2755_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
if (lean_obj_tag(v_fst_2731_) == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_del_object(v___x_2729_);
v___x_2735_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2736_ = l_Lean_MessageData_ofName(v___x_2720_);
lean_inc_ref(v___x_2736_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 7);
lean_ctor_set(v___x_2733_, 1, v___x_2736_);
lean_ctor_set(v___x_2733_, 0, v___x_2735_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2739_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2742_ = l_Lean_indentD(v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2740_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
lean_ctor_set(v___x_2746_, 1, v___x_2736_);
v___x_2747_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2748_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2749_;
}
}
else
{
lean_object* v_val_2751_; lean_object* v___x_2753_; 
lean_del_object(v___x_2733_);
lean_dec(v___x_2720_);
lean_dec(v_stx_2370_);
v_val_2751_ = lean_ctor_get(v_fst_2731_, 0);
lean_inc(v_val_2751_);
lean_dec_ref_known(v_fst_2731_, 1);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v_val_2751_);
v___x_2753_ = v___x_2729_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_val_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v___x_2720_);
lean_dec(v_stx_2370_);
v_a_2758_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2726_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2726_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
else
{
v___y_2700_ = v___y_2715_;
v___y_2701_ = v___y_2710_;
v___y_2702_ = v___y_2714_;
v___y_2703_ = v___y_2712_;
v___y_2704_ = v___y_2713_;
v___y_2705_ = v___y_2711_;
goto v___jp_2699_;
}
}
else
{
v___y_2700_ = v___y_2715_;
v___y_2701_ = v___y_2710_;
v___y_2702_ = v___y_2714_;
v___y_2703_ = v___y_2712_;
v___y_2704_ = v___y_2713_;
v___y_2705_ = v___y_2711_;
goto v___jp_2699_;
}
}
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; 
v___x_4749_ = lean_unsigned_to_nat(0u);
v___x_4750_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4749_);
v___x_4751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4752_ = l_Lean_Syntax_isOfKind(v___x_4750_, v___x_4751_);
if (v___x_4752_ == 0)
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v_env_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_del_object(v___x_2434_);
lean_inc_n(v_stx_2370_, 2);
v___x_4753_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4754_ = lean_st_ref_get(v_a_2376_);
v_env_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc_ref(v_env_4755_);
lean_dec(v___x_4754_);
v___x_4756_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4757_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4756_, v_env_4755_, v___x_4753_);
v___x_4758_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4759_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4757_, v___x_4758_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4757_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4790_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4790_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4790_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v_fst_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4788_; 
v_fst_4764_ = lean_ctor_get(v_a_4760_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_a_4760_);
if (v_isSharedCheck_4788_ == 0)
{
lean_object* v_unused_4789_; 
v_unused_4789_ = lean_ctor_get(v_a_4760_, 1);
lean_dec(v_unused_4789_);
v___x_4766_ = v_a_4760_;
v_isShared_4767_ = v_isSharedCheck_4788_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_fst_4764_);
lean_dec(v_a_4760_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4788_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
if (lean_obj_tag(v_fst_4764_) == 0)
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4771_; 
lean_del_object(v___x_4762_);
v___x_4768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4769_ = l_Lean_MessageData_ofName(v___x_4753_);
lean_inc_ref(v___x_4769_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set_tag(v___x_4766_, 7);
lean_ctor_set(v___x_4766_, 1, v___x_4769_);
lean_ctor_set(v___x_4766_, 0, v___x_4768_);
v___x_4771_ = v___x_4766_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v___x_4768_);
lean_ctor_set(v_reuseFailAlloc_4783_, 1, v___x_4769_);
v___x_4771_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4772_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4775_ = l_Lean_indentD(v___x_4774_);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4773_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
lean_ctor_set(v___x_4779_, 1, v___x_4769_);
v___x_4780_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4779_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
v___x_4782_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4781_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4782_;
}
}
else
{
lean_object* v_val_4784_; lean_object* v___x_4786_; 
lean_del_object(v___x_4766_);
lean_dec(v___x_4753_);
lean_dec(v_stx_2370_);
v_val_4784_ = lean_ctor_get(v_fst_4764_, 0);
lean_inc(v_val_4784_);
lean_dec_ref_known(v_fst_4764_, 1);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v_val_4784_);
v___x_4786_ = v___x_4762_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_val_4784_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec(v___x_4753_);
lean_dec(v_stx_2370_);
v_a_4791_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4759_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4759_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; 
v___x_4799_ = lean_unsigned_to_nat(1u);
v___x_4800_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4799_);
v___x_4801_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4800_);
v___x_4802_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4801_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v_env_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
lean_dec(v___x_4800_);
lean_del_object(v___x_2434_);
lean_inc_n(v_stx_2370_, 2);
v___x_4803_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4804_ = lean_st_ref_get(v_a_2376_);
v_env_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc_ref(v_env_4805_);
lean_dec(v___x_4804_);
v___x_4806_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4807_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4806_, v_env_4805_, v___x_4803_);
v___x_4808_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4809_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4807_, v___x_4808_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4840_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4840_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4840_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v_fst_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4838_; 
v_fst_4814_ = lean_ctor_get(v_a_4810_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v_a_4810_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v_a_4810_, 1);
lean_dec(v_unused_4839_);
v___x_4816_ = v_a_4810_;
v_isShared_4817_ = v_isSharedCheck_4838_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_fst_4814_);
lean_dec(v_a_4810_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4838_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
if (lean_obj_tag(v_fst_4814_) == 0)
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
lean_del_object(v___x_4812_);
v___x_4818_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4819_ = l_Lean_MessageData_ofName(v___x_4803_);
lean_inc_ref(v___x_4819_);
if (v_isShared_4817_ == 0)
{
lean_ctor_set_tag(v___x_4816_, 7);
lean_ctor_set(v___x_4816_, 1, v___x_4819_);
lean_ctor_set(v___x_4816_, 0, v___x_4818_);
v___x_4821_ = v___x_4816_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4822_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4821_);
lean_ctor_set(v___x_4823_, 1, v___x_4822_);
v___x_4824_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4825_ = l_Lean_indentD(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4823_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
lean_ctor_set(v___x_4829_, 1, v___x_4819_);
v___x_4830_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4831_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4832_;
}
}
else
{
lean_object* v_val_4834_; lean_object* v___x_4836_; 
lean_del_object(v___x_4816_);
lean_dec(v___x_4803_);
lean_dec(v_stx_2370_);
v_val_4834_ = lean_ctor_get(v_fst_4814_, 0);
lean_inc(v_val_4834_);
lean_dec_ref_known(v_fst_4814_, 1);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v_val_4834_);
v___x_4836_ = v___x_4812_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_val_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec(v___x_4803_);
lean_dec(v_stx_2370_);
v_a_4841_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4809_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4809_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4849_ = l_Lean_Syntax_getArg(v___x_4800_, v___x_4749_);
lean_dec(v___x_4800_);
lean_inc(v___x_4849_);
v___x_4850_ = l_Lean_Syntax_matchesNull(v___x_4849_, v___x_4799_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v_env_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec(v___x_4849_);
lean_del_object(v___x_2434_);
lean_inc_n(v_stx_2370_, 2);
v___x_4851_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4852_ = lean_st_ref_get(v_a_2376_);
v_env_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc_ref(v_env_4853_);
lean_dec(v___x_4852_);
v___x_4854_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4855_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4854_, v_env_4853_, v___x_4851_);
v___x_4856_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4857_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4855_, v___x_4856_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4855_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4888_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4860_ = v___x_4857_;
v_isShared_4861_ = v_isSharedCheck_4888_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4857_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4888_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v_fst_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4886_; 
v_fst_4862_ = lean_ctor_get(v_a_4858_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v_a_4858_);
if (v_isSharedCheck_4886_ == 0)
{
lean_object* v_unused_4887_; 
v_unused_4887_ = lean_ctor_get(v_a_4858_, 1);
lean_dec(v_unused_4887_);
v___x_4864_ = v_a_4858_;
v_isShared_4865_ = v_isSharedCheck_4886_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_fst_4862_);
lean_dec(v_a_4858_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4886_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
if (lean_obj_tag(v_fst_4862_) == 0)
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4869_; 
lean_del_object(v___x_4860_);
v___x_4866_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4867_ = l_Lean_MessageData_ofName(v___x_4851_);
lean_inc_ref(v___x_4867_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set_tag(v___x_4864_, 7);
lean_ctor_set(v___x_4864_, 1, v___x_4867_);
lean_ctor_set(v___x_4864_, 0, v___x_4866_);
v___x_4869_ = v___x_4864_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v___x_4867_);
v___x_4869_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4870_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4869_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4873_ = l_Lean_indentD(v___x_4872_);
v___x_4874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4871_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___x_4875_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4874_);
lean_ctor_set(v___x_4876_, 1, v___x_4875_);
v___x_4877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4876_);
lean_ctor_set(v___x_4877_, 1, v___x_4867_);
v___x_4878_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4879_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4880_;
}
}
else
{
lean_object* v_val_4882_; lean_object* v___x_4884_; 
lean_del_object(v___x_4864_);
lean_dec(v___x_4851_);
lean_dec(v_stx_2370_);
v_val_4882_ = lean_ctor_get(v_fst_4862_, 0);
lean_inc(v_val_4882_);
lean_dec_ref_known(v_fst_4862_, 1);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v_val_4882_);
v___x_4884_ = v___x_4860_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_val_4882_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_dec(v___x_4851_);
lean_dec(v_stx_2370_);
v_a_4889_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4857_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4857_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
else
{
if (v___x_2637_ == 0)
{
lean_object* v___x_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
v___x_4897_ = l_Lean_Syntax_getArg(v___x_4849_, v___x_4749_);
lean_dec(v___x_4849_);
v___x_4898_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4899_ = l_Lean_Syntax_isOfKind(v___x_4897_, v___x_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v_env_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
lean_del_object(v___x_2434_);
lean_inc_n(v_stx_2370_, 2);
v___x_4900_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4901_ = lean_st_ref_get(v_a_2376_);
v_env_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc_ref(v_env_4902_);
lean_dec(v___x_4901_);
v___x_4903_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4904_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4903_, v_env_4902_, v___x_4900_);
v___x_4905_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4906_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4904_, v___x_4905_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4904_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4937_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4909_ = v___x_4906_;
v_isShared_4910_ = v_isSharedCheck_4937_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4937_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v_fst_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4935_; 
v_fst_4911_ = lean_ctor_get(v_a_4907_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_a_4907_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; 
v_unused_4936_ = lean_ctor_get(v_a_4907_, 1);
lean_dec(v_unused_4936_);
v___x_4913_ = v_a_4907_;
v_isShared_4914_ = v_isSharedCheck_4935_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_fst_4911_);
lean_dec(v_a_4907_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4935_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
if (lean_obj_tag(v_fst_4911_) == 0)
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; 
lean_del_object(v___x_4909_);
v___x_4915_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4916_ = l_Lean_MessageData_ofName(v___x_4900_);
lean_inc_ref(v___x_4916_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set_tag(v___x_4913_, 7);
lean_ctor_set(v___x_4913_, 1, v___x_4916_);
lean_ctor_set(v___x_4913_, 0, v___x_4915_);
v___x_4918_ = v___x_4913_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4915_);
lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4919_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4918_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4922_ = l_Lean_indentD(v___x_4921_);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4920_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
v___x_4924_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
lean_ctor_set(v___x_4926_, 1, v___x_4916_);
v___x_4927_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4926_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
v___x_4929_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4928_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4929_;
}
}
else
{
lean_object* v_val_4931_; lean_object* v___x_4933_; 
lean_del_object(v___x_4913_);
lean_dec(v___x_4900_);
lean_dec(v_stx_2370_);
v_val_4931_ = lean_ctor_get(v_fst_4911_, 0);
lean_inc(v_val_4931_);
lean_dec_ref_known(v_fst_4911_, 1);
if (v_isShared_4910_ == 0)
{
lean_ctor_set(v___x_4909_, 0, v_val_4931_);
v___x_4933_ = v___x_4909_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_val_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v___x_4900_);
lean_dec(v_stx_2370_);
v_a_4938_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4906_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4906_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2436_;
}
}
else
{
lean_dec(v___x_4849_);
lean_dec(v_stx_2370_);
goto v___jp_2436_;
}
}
}
}
}
v___jp_2640_:
{
if (v___x_2639_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2647_ = lean_unsigned_to_nat(2u);
v___x_2648_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2647_);
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2650_ = l_Lean_Syntax_isOfKind(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v_env_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2651_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2652_ = lean_st_ref_get(v___y_2646_);
v_env_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc_ref(v_env_2653_);
lean_dec(v___x_2652_);
v___x_2654_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2655_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2654_, v_env_2653_, v___x_2651_);
v___x_2656_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2657_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2655_, v___x_2656_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___x_2655_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2688_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2688_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2688_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_fst_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2686_; 
v_fst_2662_ = lean_ctor_get(v_a_2658_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_a_2658_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v_a_2658_, 1);
lean_dec(v_unused_2687_);
v___x_2664_ = v_a_2658_;
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_fst_2662_);
lean_dec(v_a_2658_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_fst_2662_) == 0)
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_del_object(v___x_2660_);
v___x_2666_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2667_ = l_Lean_MessageData_ofName(v___x_2651_);
lean_inc_ref(v___x_2667_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 7);
lean_ctor_set(v___x_2664_, 1, v___x_2667_);
lean_ctor_set(v___x_2664_, 0, v___x_2666_);
v___x_2669_ = v___x_2664_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2670_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2673_ = l_Lean_indentD(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2667_);
v___x_2678_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2679_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2680_;
}
}
else
{
lean_object* v_val_2682_; lean_object* v___x_2684_; 
lean_del_object(v___x_2664_);
lean_dec(v___x_2651_);
lean_dec(v_stx_2370_);
v_val_2682_ = lean_ctor_get(v_fst_2662_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v_fst_2662_, 1);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v_val_2682_);
v___x_2684_ = v___x_2660_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_val_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v___x_2651_);
lean_dec(v_stx_2370_);
v_a_2689_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2657_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2657_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
else
{
v___y_2397_ = v___y_2644_;
v___y_2398_ = v___y_2645_;
v___y_2399_ = v___y_2641_;
v___y_2400_ = v___y_2646_;
v___y_2401_ = v___y_2642_;
v___y_2402_ = v___y_2643_;
goto v___jp_2396_;
}
}
else
{
v___y_2397_ = v___y_2644_;
v___y_2398_ = v___y_2645_;
v___y_2399_ = v___y_2641_;
v___y_2400_ = v___y_2646_;
v___y_2401_ = v___y_2642_;
v___y_2402_ = v___y_2643_;
goto v___jp_2396_;
}
}
}
else
{
lean_del_object(v___x_2434_);
if (v___x_2584_ == 0)
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v___x_4946_ = lean_unsigned_to_nat(1u);
v___x_4947_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4946_);
v___x_4948_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_4949_ = l_Lean_Syntax_isOfKind(v___x_4947_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v_env_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_inc_n(v_stx_2370_, 2);
v___x_4950_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_4951_ = lean_st_ref_get(v_a_2376_);
v_env_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc_ref(v_env_4952_);
lean_dec(v___x_4951_);
v___x_4953_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4954_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4953_, v_env_4952_, v___x_4950_);
v___x_4955_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4956_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_4954_, v___x_4955_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_4954_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4987_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4959_ = v___x_4956_;
v_isShared_4960_ = v_isSharedCheck_4987_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4956_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4987_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v_fst_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4985_; 
v_fst_4961_ = lean_ctor_get(v_a_4957_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v_a_4957_);
if (v_isSharedCheck_4985_ == 0)
{
lean_object* v_unused_4986_; 
v_unused_4986_ = lean_ctor_get(v_a_4957_, 1);
lean_dec(v_unused_4986_);
v___x_4963_ = v_a_4957_;
v_isShared_4964_ = v_isSharedCheck_4985_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_fst_4961_);
lean_dec(v_a_4957_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4985_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
if (lean_obj_tag(v_fst_4961_) == 0)
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; 
lean_del_object(v___x_4959_);
v___x_4965_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4966_ = l_Lean_MessageData_ofName(v___x_4950_);
lean_inc_ref(v___x_4966_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set_tag(v___x_4963_, 7);
lean_ctor_set(v___x_4963_, 1, v___x_4966_);
lean_ctor_set(v___x_4963_, 0, v___x_4965_);
v___x_4968_ = v___x_4963_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4965_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4969_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4968_);
lean_ctor_set(v___x_4970_, 1, v___x_4969_);
v___x_4971_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_4972_ = l_Lean_indentD(v___x_4971_);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4970_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4973_);
lean_ctor_set(v___x_4975_, 1, v___x_4974_);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
lean_ctor_set(v___x_4976_, 1, v___x_4966_);
v___x_4977_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4978_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_4979_;
}
}
else
{
lean_object* v_val_4981_; lean_object* v___x_4983_; 
lean_del_object(v___x_4963_);
lean_dec(v___x_4950_);
lean_dec(v_stx_2370_);
v_val_4981_ = lean_ctor_get(v_fst_4961_, 0);
lean_inc(v_val_4981_);
lean_dec_ref_known(v_fst_4961_, 1);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v_val_4981_);
v___x_4983_ = v___x_4959_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_val_4981_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_dec(v___x_4950_);
lean_dec(v_stx_2370_);
v_a_4988_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4956_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4956_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
else
{
goto v___jp_2585_;
}
}
else
{
goto v___jp_2585_;
}
}
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
lean_del_object(v___x_2434_);
v___x_4996_ = lean_unsigned_to_nat(1u);
v___x_4997_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_4996_);
v___x_4998_ = l_Lean_Syntax_isNone(v___x_4997_);
if (v___x_4998_ == 0)
{
uint8_t v___x_4999_; 
v___x_4999_ = l_Lean_Syntax_matchesNull(v___x_4997_, v___x_4996_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v_env_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_inc_n(v_stx_2370_, 2);
v___x_5000_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_5001_ = lean_st_ref_get(v_a_2376_);
v_env_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc_ref(v_env_5002_);
lean_dec(v___x_5001_);
v___x_5003_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5004_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5003_, v_env_5002_, v___x_5000_);
v___x_5005_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5006_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_5004_, v___x_5005_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_5004_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5037_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5009_ = v___x_5006_;
v_isShared_5010_ = v_isSharedCheck_5037_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_5006_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5037_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v_fst_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5035_; 
v_fst_5011_ = lean_ctor_get(v_a_5007_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v_a_5007_);
if (v_isSharedCheck_5035_ == 0)
{
lean_object* v_unused_5036_; 
v_unused_5036_ = lean_ctor_get(v_a_5007_, 1);
lean_dec(v_unused_5036_);
v___x_5013_ = v_a_5007_;
v_isShared_5014_ = v_isSharedCheck_5035_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_fst_5011_);
lean_dec(v_a_5007_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5035_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
if (lean_obj_tag(v_fst_5011_) == 0)
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5018_; 
lean_del_object(v___x_5009_);
v___x_5015_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5016_ = l_Lean_MessageData_ofName(v___x_5000_);
lean_inc_ref(v___x_5016_);
if (v_isShared_5014_ == 0)
{
lean_ctor_set_tag(v___x_5013_, 7);
lean_ctor_set(v___x_5013_, 1, v___x_5016_);
lean_ctor_set(v___x_5013_, 0, v___x_5015_);
v___x_5018_ = v___x_5013_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5015_);
lean_ctor_set(v_reuseFailAlloc_5030_, 1, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5019_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5018_);
lean_ctor_set(v___x_5020_, 1, v___x_5019_);
v___x_5021_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_5022_ = l_Lean_indentD(v___x_5021_);
v___x_5023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5020_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
v___x_5024_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5023_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
lean_ctor_set(v___x_5026_, 1, v___x_5016_);
v___x_5027_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5028_, 0, v___x_5026_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
v___x_5029_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5028_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_5029_;
}
}
else
{
lean_object* v_val_5031_; lean_object* v___x_5033_; 
lean_del_object(v___x_5013_);
lean_dec(v___x_5000_);
lean_dec(v_stx_2370_);
v_val_5031_ = lean_ctor_get(v_fst_5011_, 0);
lean_inc(v_val_5031_);
lean_dec_ref_known(v_fst_5011_, 1);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v_val_5031_);
v___x_5033_ = v___x_5009_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_val_5031_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; uint8_t v_isShared_5041_; uint8_t v_isSharedCheck_5045_; 
lean_dec(v___x_5000_);
lean_dec(v_stx_2370_);
v_a_5038_ = lean_ctor_get(v___x_5006_, 0);
v_isSharedCheck_5045_ = !lean_is_exclusive(v___x_5006_);
if (v_isSharedCheck_5045_ == 0)
{
v___x_5040_ = v___x_5006_;
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
else
{
lean_inc(v_a_5038_);
lean_dec(v___x_5006_);
v___x_5040_ = lean_box(0);
v_isShared_5041_ = v_isSharedCheck_5045_;
goto v_resetjp_5039_;
}
v_resetjp_5039_:
{
lean_object* v___x_5043_; 
if (v_isShared_5041_ == 0)
{
v___x_5043_ = v___x_5040_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_a_5038_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
}
}
else
{
v___y_2527_ = v_a_2371_;
v___y_2528_ = v_a_2372_;
v___y_2529_ = v_a_2373_;
v___y_2530_ = v_a_2374_;
v___y_2531_ = v_a_2375_;
v___y_2532_ = v_a_2376_;
goto v___jp_2526_;
}
}
else
{
lean_dec(v___x_4997_);
v___y_2527_ = v_a_2371_;
v___y_2528_ = v_a_2372_;
v___y_2529_ = v_a_2373_;
v___y_2530_ = v_a_2374_;
v___y_2531_ = v_a_2375_;
v___y_2532_ = v_a_2376_;
goto v___jp_2526_;
}
}
v___jp_2585_:
{
if (v___x_2584_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2586_ = lean_unsigned_to_nat(2u);
v___x_2587_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2589_ = l_Lean_Syntax_isOfKind(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v_env_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2590_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2591_ = lean_st_ref_get(v_a_2376_);
v_env_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref(v_env_2592_);
lean_dec(v___x_2591_);
v___x_2593_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2594_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2593_, v_env_2592_, v___x_2590_);
v___x_2595_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2596_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2594_, v___x_2595_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_2594_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2627_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2627_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2627_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_fst_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2625_; 
v_fst_2601_ = lean_ctor_get(v_a_2597_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_a_2597_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_a_2597_, 1);
lean_dec(v_unused_2626_);
v___x_2603_ = v_a_2597_;
v_isShared_2604_ = v_isSharedCheck_2625_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_fst_2601_);
lean_dec(v_a_2597_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2625_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
if (lean_obj_tag(v_fst_2601_) == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_del_object(v___x_2599_);
v___x_2605_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2606_ = l_Lean_MessageData_ofName(v___x_2590_);
lean_inc_ref(v___x_2606_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 7);
lean_ctor_set(v___x_2603_, 1, v___x_2606_);
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2608_ = v___x_2603_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2609_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2612_ = l_Lean_indentD(v___x_2611_);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2610_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2606_);
v___x_2617_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2618_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2619_;
}
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2623_; 
lean_del_object(v___x_2603_);
lean_dec(v___x_2590_);
lean_dec(v_stx_2370_);
v_val_2621_ = lean_ctor_get(v_fst_2601_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v_fst_2601_, 1);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v_val_2621_);
v___x_2623_ = v___x_2599_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_val_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec(v___x_2590_);
lean_dec(v_stx_2370_);
v_a_2628_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2596_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2596_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2441_;
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2441_;
}
}
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_del_object(v___x_2434_);
v___x_5046_ = lean_unsigned_to_nat(1u);
v___x_5047_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_5046_);
lean_dec(v_stx_2370_);
v___x_5048_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5047_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_5048_;
}
v___jp_2469_:
{
if (v___x_2468_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2476_ = lean_unsigned_to_nat(3u);
v___x_2477_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2476_);
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2479_ = l_Lean_Syntax_isOfKind(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_env_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2480_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2481_ = lean_st_ref_get(v___y_2475_);
v_env_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc_ref(v_env_2482_);
lean_dec(v___x_2481_);
v___x_2483_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2484_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2483_, v_env_2482_, v___x_2480_);
v___x_2485_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2486_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2484_, v___x_2485_, v___y_2473_, v___y_2474_, v___y_2472_, v___y_2471_, v___y_2470_, v___y_2475_);
lean_dec(v___x_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2517_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2517_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2517_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_fst_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2515_; 
v_fst_2491_ = lean_ctor_get(v_a_2487_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v_a_2487_, 1);
lean_dec(v_unused_2516_);
v___x_2493_ = v_a_2487_;
v_isShared_2494_ = v_isSharedCheck_2515_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_fst_2491_);
lean_dec(v_a_2487_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2515_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
if (lean_obj_tag(v_fst_2491_) == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
lean_del_object(v___x_2489_);
v___x_2495_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2496_ = l_Lean_MessageData_ofName(v___x_2480_);
lean_inc_ref(v___x_2496_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 7);
lean_ctor_set(v___x_2493_, 1, v___x_2496_);
lean_ctor_set(v___x_2493_, 0, v___x_2495_);
v___x_2498_ = v___x_2493_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2499_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2502_ = l_Lean_indentD(v___x_2501_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2500_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2496_);
v___x_2507_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2508_, v___y_2473_, v___y_2474_, v___y_2472_, v___y_2471_, v___y_2470_, v___y_2475_);
return v___x_2509_;
}
}
else
{
lean_object* v_val_2511_; lean_object* v___x_2513_; 
lean_del_object(v___x_2493_);
lean_dec(v___x_2480_);
lean_dec(v_stx_2370_);
v_val_2511_ = lean_ctor_get(v_fst_2491_, 0);
lean_inc(v_val_2511_);
lean_dec_ref_known(v_fst_2491_, 1);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v_val_2511_);
v___x_2513_ = v___x_2489_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_val_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v___x_2480_);
lean_dec(v_stx_2370_);
v_a_2518_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2486_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2486_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2417_;
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_2417_;
}
}
v___jp_2526_:
{
if (v___x_2468_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2533_ = lean_unsigned_to_nat(2u);
v___x_2534_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2533_);
v___x_2535_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2536_ = l_Lean_Syntax_isOfKind(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_env_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_inc_n(v_stx_2370_, 2);
v___x_2537_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_2538_ = lean_st_ref_get(v___y_2532_);
v_env_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_ref(v_env_2539_);
lean_dec(v___x_2538_);
v___x_2540_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2541_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2540_, v_env_2539_, v___x_2537_);
v___x_2542_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2543_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_2541_, v___x_2542_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___x_2541_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2574_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2574_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2574_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_fst_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2572_; 
v_fst_2548_ = lean_ctor_get(v_a_2544_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_a_2544_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; 
v_unused_2573_ = lean_ctor_get(v_a_2544_, 1);
lean_dec(v_unused_2573_);
v___x_2550_ = v_a_2544_;
v_isShared_2551_ = v_isSharedCheck_2572_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_fst_2548_);
lean_dec(v_a_2544_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2572_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (lean_obj_tag(v_fst_2548_) == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_del_object(v___x_2546_);
v___x_2552_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2553_ = l_Lean_MessageData_ofName(v___x_2537_);
lean_inc_ref(v___x_2553_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 7);
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2556_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_2559_ = l_Lean_indentD(v___x_2558_);
v___x_2560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2557_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
lean_ctor_set(v___x_2563_, 1, v___x_2553_);
v___x_2564_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2565_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
return v___x_2566_;
}
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2570_; 
lean_del_object(v___x_2550_);
lean_dec(v___x_2537_);
lean_dec(v_stx_2370_);
v_val_2568_ = lean_ctor_get(v_fst_2548_, 0);
lean_inc(v_val_2568_);
lean_dec_ref_known(v_fst_2548_, 1);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v_val_2568_);
v___x_2570_ = v___x_2546_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_val_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec(v___x_2537_);
lean_dec(v_stx_2370_);
v_a_2575_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2543_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2543_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
v___y_2470_ = v___y_2531_;
v___y_2471_ = v___y_2530_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2527_;
v___y_2474_ = v___y_2528_;
v___y_2475_ = v___y_2532_;
goto v___jp_2469_;
}
}
else
{
v___y_2470_ = v___y_2531_;
v___y_2471_ = v___y_2530_;
v___y_2472_ = v___y_2529_;
v___y_2473_ = v___y_2527_;
v___y_2474_ = v___y_2528_;
v___y_2475_ = v___y_2532_;
goto v___jp_2469_;
}
}
}
else
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
lean_del_object(v___x_2434_);
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_5049_);
lean_dec(v_stx_2370_);
v___x_5051_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5050_);
if (lean_obj_tag(v___x_5051_) == 1)
{
lean_object* v_val_5052_; lean_object* v_snd_5053_; lean_object* v_body_5054_; lean_object* v___x_5055_; 
v_val_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_val_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v_snd_5053_ = lean_ctor_get(v_val_5052_, 1);
lean_inc(v_snd_5053_);
lean_dec(v_val_5052_);
v_body_5054_ = lean_ctor_get(v_snd_5053_, 1);
lean_inc(v_body_5054_);
lean_dec(v_snd_5053_);
v___x_5055_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5054_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5076_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5058_ = v___x_5055_;
v_isShared_5059_ = v_isSharedCheck_5076_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5055_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5076_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
uint8_t v_breaks_5060_; uint8_t v_continues_5061_; uint8_t v_returnsEarly_5062_; lean_object* v_reassigns_5063_; lean_object* v___x_5065_; uint8_t v_isShared_5066_; uint8_t v_isSharedCheck_5074_; 
v_breaks_5060_ = lean_ctor_get_uint8(v_a_5056_, sizeof(void*)*2);
v_continues_5061_ = lean_ctor_get_uint8(v_a_5056_, sizeof(void*)*2 + 1);
v_returnsEarly_5062_ = lean_ctor_get_uint8(v_a_5056_, sizeof(void*)*2 + 2);
v_reassigns_5063_ = lean_ctor_get(v_a_5056_, 1);
v_isSharedCheck_5074_ = !lean_is_exclusive(v_a_5056_);
if (v_isSharedCheck_5074_ == 0)
{
lean_object* v_unused_5075_; 
v_unused_5075_ = lean_ctor_get(v_a_5056_, 0);
lean_dec(v_unused_5075_);
v___x_5065_ = v_a_5056_;
v_isShared_5066_ = v_isSharedCheck_5074_;
goto v_resetjp_5064_;
}
else
{
lean_inc(v_reassigns_5063_);
lean_dec(v_a_5056_);
v___x_5065_ = lean_box(0);
v_isShared_5066_ = v_isSharedCheck_5074_;
goto v_resetjp_5064_;
}
v_resetjp_5064_:
{
lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5067_ = lean_unsigned_to_nat(1u);
if (v_isShared_5066_ == 0)
{
lean_ctor_set(v___x_5065_, 0, v___x_5067_);
v___x_5069_ = v___x_5065_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v___x_5067_);
lean_ctor_set(v_reuseFailAlloc_5073_, 1, v_reassigns_5063_);
lean_ctor_set_uint8(v_reuseFailAlloc_5073_, sizeof(void*)*2, v_breaks_5060_);
lean_ctor_set_uint8(v_reuseFailAlloc_5073_, sizeof(void*)*2 + 1, v_continues_5061_);
lean_ctor_set_uint8(v_reuseFailAlloc_5073_, sizeof(void*)*2 + 2, v_returnsEarly_5062_);
v___x_5069_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5071_; 
lean_ctor_set_uint8(v___x_5069_, sizeof(void*)*2 + 3, v___x_2464_);
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5069_);
v___x_5071_ = v___x_5058_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
else
{
return v___x_5055_;
}
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
lean_dec(v___x_5051_);
v___x_5077_ = lean_unsigned_to_nat(1u);
v___x_5078_ = l_Lean_NameSet_empty;
v___x_5079_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*2, v___x_2464_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*2 + 1, v___x_2464_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*2 + 2, v___x_2464_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*2 + 3, v___x_2464_);
v___x_5080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
return v___x_5080_;
}
}
}
else
{
lean_object* v___x_5081_; lean_object* v___x_5086_; lean_object* v___x_5087_; uint8_t v___x_5088_; 
lean_del_object(v___x_2434_);
v___x_5081_ = lean_unsigned_to_nat(0u);
v___x_5086_ = lean_unsigned_to_nat(1u);
v___x_5087_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_5086_);
v___x_5088_ = l_Lean_Syntax_isNone(v___x_5087_);
if (v___x_5088_ == 0)
{
uint8_t v___x_5089_; 
v___x_5089_ = l_Lean_Syntax_matchesNull(v___x_5087_, v___x_5086_);
if (v___x_5089_ == 0)
{
lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v_env_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_inc_n(v_stx_2370_, 2);
v___x_5090_ = l_Lean_Syntax_getKind(v_stx_2370_);
v___x_5091_ = lean_st_ref_get(v_a_2376_);
v_env_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc_ref(v_env_5092_);
lean_dec(v___x_5091_);
v___x_5093_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5094_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5093_, v_env_5092_, v___x_5090_);
v___x_5095_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5096_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2370_, v___x_5094_, v___x_5095_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v___x_5094_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5127_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5127_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5127_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v_fst_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5125_; 
v_fst_5101_ = lean_ctor_get(v_a_5097_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v_a_5097_);
if (v_isSharedCheck_5125_ == 0)
{
lean_object* v_unused_5126_; 
v_unused_5126_ = lean_ctor_get(v_a_5097_, 1);
lean_dec(v_unused_5126_);
v___x_5103_ = v_a_5097_;
v_isShared_5104_ = v_isSharedCheck_5125_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_fst_5101_);
lean_dec(v_a_5097_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5125_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
if (lean_obj_tag(v_fst_5101_) == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5108_; 
lean_del_object(v___x_5099_);
v___x_5105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5106_ = l_Lean_MessageData_ofName(v___x_5090_);
lean_inc_ref(v___x_5106_);
if (v_isShared_5104_ == 0)
{
lean_ctor_set_tag(v___x_5103_, 7);
lean_ctor_set(v___x_5103_, 1, v___x_5106_);
lean_ctor_set(v___x_5103_, 0, v___x_5105_);
v___x_5108_ = v___x_5103_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v___x_5105_);
lean_ctor_set(v_reuseFailAlloc_5120_, 1, v___x_5106_);
v___x_5108_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5109_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5108_);
lean_ctor_set(v___x_5110_, 1, v___x_5109_);
v___x_5111_ = l_Lean_MessageData_ofSyntax(v_stx_2370_);
v___x_5112_ = l_Lean_indentD(v___x_5111_);
v___x_5113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5113_, 0, v___x_5110_);
lean_ctor_set(v___x_5113_, 1, v___x_5112_);
v___x_5114_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5115_, 0, v___x_5113_);
lean_ctor_set(v___x_5115_, 1, v___x_5114_);
v___x_5116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5115_);
lean_ctor_set(v___x_5116_, 1, v___x_5106_);
v___x_5117_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5118_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_5119_;
}
}
else
{
lean_object* v_val_5121_; lean_object* v___x_5123_; 
lean_del_object(v___x_5103_);
lean_dec(v___x_5090_);
lean_dec(v_stx_2370_);
v_val_5121_ = lean_ctor_get(v_fst_5101_, 0);
lean_inc(v_val_5121_);
lean_dec_ref_known(v_fst_5101_, 1);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v_val_5121_);
v___x_5123_ = v___x_5099_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_val_5121_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
lean_dec(v___x_5090_);
lean_dec(v_stx_2370_);
v_a_5128_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5130_ = v___x_5096_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5096_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
else
{
lean_dec(v_stx_2370_);
goto v___jp_5082_;
}
}
else
{
lean_dec(v___x_5087_);
lean_dec(v_stx_2370_);
goto v___jp_5082_;
}
v___jp_5082_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5083_ = l_Lean_NameSet_empty;
v___x_5084_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5084_, 0, v___x_5081_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
lean_ctor_set_uint8(v___x_5084_, sizeof(void*)*2, v___x_2462_);
lean_ctor_set_uint8(v___x_5084_, sizeof(void*)*2 + 1, v___x_2462_);
lean_ctor_set_uint8(v___x_5084_, sizeof(void*)*2 + 2, v___x_2460_);
lean_ctor_set_uint8(v___x_5084_, sizeof(void*)*2 + 3, v___x_2460_);
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5084_);
return v___x_5085_;
}
}
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
lean_del_object(v___x_2434_);
lean_dec(v_stx_2370_);
v___x_5136_ = lean_unsigned_to_nat(0u);
v___x_5137_ = l_Lean_NameSet_empty;
v___x_5138_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5138_, 0, v___x_5136_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
lean_ctor_set_uint8(v___x_5138_, sizeof(void*)*2, v___x_2459_);
lean_ctor_set_uint8(v___x_5138_, sizeof(void*)*2 + 1, v___x_2460_);
lean_ctor_set_uint8(v___x_5138_, sizeof(void*)*2 + 2, v___x_2459_);
lean_ctor_set_uint8(v___x_5138_, sizeof(void*)*2 + 3, v___x_2460_);
v___x_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5138_);
return v___x_5139_;
}
}
else
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
lean_del_object(v___x_2434_);
lean_dec(v_stx_2370_);
v___x_5140_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
return v___x_5141_;
}
}
v___jp_2436_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2437_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
v___jp_2441_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_stx_2370_);
v_a_5143_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_2431_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_2431_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
v___jp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2379_, v_bodyInfo_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
v___jp_2383_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___y_2385_);
v___x_2395_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2392_, v___x_2393_, v___x_2394_, v___y_2391_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2384_, v___y_2386_, v___y_2387_);
return v___x_2395_;
}
v___jp_2396_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2403_ = lean_unsigned_to_nat(7u);
v___x_2404_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(8u);
v___x_2406_ = l_Lean_Syntax_getArg(v_stx_2370_, v___x_2405_);
lean_dec(v_stx_2370_);
v___x_2407_ = l_Lean_Syntax_getOptional_x3f(v___x_2406_);
lean_dec(v___x_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_box(0);
v___y_2384_ = v___y_2397_;
v___y_2385_ = v___x_2404_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2400_;
v___y_2388_ = v___y_2399_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v___y_2402_;
v___y_2391_ = v___x_2408_;
goto v___jp_2383_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_val_2409_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2407_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v___x_2407_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_val_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
v___y_2384_ = v___y_2397_;
v___y_2385_ = v___x_2404_;
v___y_2386_ = v___y_2398_;
v___y_2387_ = v___y_2400_;
v___y_2388_ = v___y_2399_;
v___y_2389_ = v___y_2401_;
v___y_2390_ = v___y_2402_;
v___y_2391_ = v___x_2414_;
goto v___jp_2383_;
}
}
}
}
v___jp_2417_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
v___jp_2420_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
v___jp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2424_, v_bodyInfo_2425_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5151_, size_t v_sz_5152_, size_t v_i_5153_, lean_object* v_b_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
uint8_t v___x_5162_; 
v___x_5162_ = lean_usize_dec_lt(v_i_5153_, v_sz_5152_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v_b_5154_);
return v___x_5163_;
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5165_; 
v_a_5164_ = lean_array_uget_borrowed(v_as_5151_, v_i_5153_);
lean_inc(v_a_5164_);
v___x_5165_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5164_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; lean_object* v___x_5167_; size_t v___x_5168_; size_t v___x_5169_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
v___x_5167_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5154_, v_a_5166_);
v___x_5168_ = ((size_t)1ULL);
v___x_5169_ = lean_usize_add(v_i_5153_, v___x_5168_);
v_i_5153_ = v___x_5169_;
v_b_5154_ = v___x_5167_;
goto _start;
}
else
{
lean_dec_ref(v_b_5154_);
return v___x_5165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_info_5179_; lean_object* v___x_5180_; size_t v_sz_5181_; size_t v___x_5182_; lean_object* v___x_5183_; 
v_info_5179_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5180_ = l_Lean_Parser_Term_getDoElems(v_stx_5171_);
v_sz_5181_ = lean_array_size(v___x_5180_);
v___x_5182_ = ((size_t)0ULL);
v___x_5183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5180_, v_sz_5181_, v___x_5182_, v_info_5179_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_);
lean_dec_ref(v___x_5180_);
return v___x_5183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_, lean_object* v_a_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5193_, v_a_5194_, v_a_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
lean_dec(v_a_5199_);
lean_dec_ref(v_a_5198_);
lean_dec(v_a_5197_);
lean_dec_ref(v_a_5196_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5202_, lean_object* v_sz_5203_, lean_object* v_i_5204_, lean_object* v_b_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
size_t v_sz_boxed_5213_; size_t v_i_boxed_5214_; lean_object* v_res_5215_; 
v_sz_boxed_5213_ = lean_unbox_usize(v_sz_5203_);
lean_dec(v_sz_5203_);
v_i_boxed_5214_ = lean_unbox_usize(v_i_5204_);
lean_dec(v_i_5204_);
v_res_5215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5202_, v_sz_boxed_5213_, v_i_boxed_5214_, v_b_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec_ref(v_as_5202_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5216_, lean_object* v_sz_5217_, lean_object* v_i_5218_, lean_object* v_b_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
size_t v_sz_boxed_5227_; size_t v_i_boxed_5228_; lean_object* v_res_5229_; 
v_sz_boxed_5227_ = lean_unbox_usize(v_sz_5217_);
lean_dec(v_sz_5217_);
v_i_boxed_5228_ = lean_unbox_usize(v_i_5218_);
lean_dec(v_i_5218_);
v_res_5229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5216_, v_sz_boxed_5227_, v_i_boxed_5228_, v_b_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
lean_dec(v___y_5221_);
lean_dec_ref(v___y_5220_);
lean_dec_ref(v_as_5216_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5230_, lean_object* v_as_5231_, lean_object* v_sz_5232_, lean_object* v_i_5233_, lean_object* v_b_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_){
_start:
{
uint8_t v___x_178583__boxed_5242_; size_t v_sz_boxed_5243_; size_t v_i_boxed_5244_; lean_object* v_res_5245_; 
v___x_178583__boxed_5242_ = lean_unbox(v___x_5230_);
v_sz_boxed_5243_ = lean_unbox_usize(v_sz_5232_);
lean_dec(v_sz_5232_);
v_i_boxed_5244_ = lean_unbox_usize(v_i_5233_);
lean_dec(v_i_5233_);
v_res_5245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_178583__boxed_5242_, v_as_5231_, v_sz_boxed_5243_, v_i_boxed_5244_, v_b_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec_ref(v_as_5231_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5246_, lean_object* v_as_5247_, lean_object* v_sz_5248_, lean_object* v_i_5249_, lean_object* v_b_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
uint8_t v___x_178630__boxed_5258_; size_t v_sz_boxed_5259_; size_t v_i_boxed_5260_; lean_object* v_res_5261_; 
v___x_178630__boxed_5258_ = lean_unbox(v___x_5246_);
v_sz_boxed_5259_ = lean_unbox_usize(v_sz_5248_);
lean_dec(v_sz_5248_);
v_i_boxed_5260_ = lean_unbox_usize(v_i_5249_);
lean_dec(v_i_5249_);
v_res_5261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_178630__boxed_5258_, v_as_5247_, v_sz_boxed_5259_, v_i_boxed_5260_, v_b_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec_ref(v_as_5247_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5262_, lean_object* v_rhs_x3f_5263_, lean_object* v_otherwise_x3f_5264_, lean_object* v_body_x3f_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5262_, v_rhs_x3f_5263_, v_otherwise_x3f_5264_, v_body_x3f_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_);
lean_dec(v_a_5271_);
lean_dec_ref(v_a_5270_);
lean_dec(v_a_5269_);
lean_dec_ref(v_a_5268_);
lean_dec(v_a_5267_);
lean_dec_ref(v_a_5266_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5274_, lean_object* v_sz_5275_, lean_object* v_i_5276_, lean_object* v_b_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
size_t v_sz_boxed_5285_; size_t v_i_boxed_5286_; lean_object* v_res_5287_; 
v_sz_boxed_5285_ = lean_unbox_usize(v_sz_5275_);
lean_dec(v_sz_5275_);
v_i_boxed_5286_ = lean_unbox_usize(v_i_5276_);
lean_dec(v_i_5276_);
v_res_5287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5274_, v_sz_boxed_5285_, v_i_boxed_5286_, v_b_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec_ref(v_as_5274_);
return v_res_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5288_, lean_object* v_decl_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_){
_start:
{
uint8_t v_reassignment_boxed_5297_; lean_object* v_res_5298_; 
v_reassignment_boxed_5297_ = lean_unbox(v_reassignment_5288_);
v_res_5298_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5297_, v_decl_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_);
lean_dec(v_a_5295_);
lean_dec_ref(v_a_5294_);
lean_dec(v_a_5293_);
lean_dec_ref(v_a_5292_);
lean_dec(v_a_5291_);
lean_dec_ref(v_a_5290_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
lean_dec_ref(v_a_5300_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5326_, lean_object* v_ref_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v___x_5335_; 
v___x_5335_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5327_);
return v___x_5335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5336_, lean_object* v_ref_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5336_, v_ref_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5346_, lean_object* v_x_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_){
_start:
{
lean_object* v___x_5355_; 
v___x_5355_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5356_, lean_object* v_x_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5356_, v_x_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5366_, lean_object* v_as_5367_, lean_object* v_as_x27_5368_, lean_object* v_b_5369_, lean_object* v_a_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5366_, v_as_x27_5368_, v_b_5369_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5379_, lean_object* v_as_5380_, lean_object* v_as_x27_5381_, lean_object* v_b_5382_, lean_object* v_a_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5379_, v_as_5380_, v_as_x27_5381_, v_b_5382_, v_a_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v_as_x27_5381_);
lean_dec(v_as_5380_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5392_, lean_object* v_msg_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
lean_object* v___x_5401_; 
v___x_5401_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5402_, lean_object* v_msg_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5402_, v_msg_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_);
lean_dec(v___y_5409_);
lean_dec_ref(v___y_5408_);
lean_dec(v___y_5407_);
lean_dec_ref(v___y_5406_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5412_, lean_object* v_msg_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5412_, v_msg_5413_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5422_, lean_object* v_msg_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5422_, v_msg_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5432_, lean_object* v_as_x27_5433_, lean_object* v_b_5434_, lean_object* v_a_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_){
_start:
{
lean_object* v___x_5443_; 
v___x_5443_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5433_, v_b_5434_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5444_, lean_object* v_as_x27_5445_, lean_object* v_b_5446_, lean_object* v_a_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5444_, v_as_x27_5445_, v_b_5446_, v_a_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_);
lean_dec(v___y_5453_);
lean_dec_ref(v___y_5452_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec(v_as_x27_5445_);
lean_dec(v_as_5444_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5456_, lean_object* v_ref_5457_, lean_object* v_msg_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_){
_start:
{
lean_object* v___x_5466_; 
v___x_5466_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5457_, v_msg_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
return v___x_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5467_, lean_object* v_ref_5468_, lean_object* v_msg_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5467_, v_ref_5468_, v_msg_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v_ref_5468_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5478_, lean_object* v_macroStack_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v___x_5487_; 
v___x_5487_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5478_, v_macroStack_5479_, v___y_5484_);
return v___x_5487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5488_, lean_object* v_macroStack_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
lean_object* v_res_5497_; 
v_res_5497_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5488_, v_macroStack_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
lean_dec(v___y_5493_);
lean_dec_ref(v___y_5492_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5498_, lean_object* v_m_5499_, lean_object* v_a_5500_){
_start:
{
lean_object* v___x_5501_; 
v___x_5501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5499_, v_a_5500_);
return v___x_5501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5502_, lean_object* v_m_5503_, lean_object* v_a_5504_){
_start:
{
lean_object* v_res_5505_; 
v_res_5505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5502_, v_m_5503_, v_a_5504_);
lean_dec(v_a_5504_);
lean_dec_ref(v_m_5503_);
return v_res_5505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5506_, lean_object* v_x_5507_, lean_object* v_x_5508_){
_start:
{
uint8_t v___x_5509_; 
v___x_5509_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5507_, v_x_5508_);
return v___x_5509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5510_, lean_object* v_x_5511_, lean_object* v_x_5512_){
_start:
{
uint8_t v_res_5513_; lean_object* v_r_5514_; 
v_res_5513_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5510_, v_x_5511_, v_x_5512_);
lean_dec_ref(v_x_5512_);
lean_dec_ref(v_x_5511_);
v_r_5514_ = lean_box(v_res_5513_);
return v_r_5514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5515_, lean_object* v_a_5516_, lean_object* v_x_5517_){
_start:
{
lean_object* v___x_5518_; 
v___x_5518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5516_, v_x_5517_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5519_, lean_object* v_a_5520_, lean_object* v_x_5521_){
_start:
{
lean_object* v_res_5522_; 
v_res_5522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5519_, v_a_5520_, v_x_5521_);
lean_dec(v_x_5521_);
lean_dec(v_a_5520_);
return v_res_5522_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5523_, lean_object* v_x_5524_, size_t v_x_5525_, lean_object* v_x_5526_){
_start:
{
uint8_t v___x_5527_; 
v___x_5527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5524_, v_x_5525_, v_x_5526_);
return v___x_5527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5528_, lean_object* v_x_5529_, lean_object* v_x_5530_, lean_object* v_x_5531_){
_start:
{
size_t v_x_185769__boxed_5532_; uint8_t v_res_5533_; lean_object* v_r_5534_; 
v_x_185769__boxed_5532_ = lean_unbox_usize(v_x_5530_);
lean_dec(v_x_5530_);
v_res_5533_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5528_, v_x_5529_, v_x_185769__boxed_5532_, v_x_5531_);
lean_dec_ref(v_x_5531_);
lean_dec_ref(v_x_5529_);
v_r_5534_ = lean_box(v_res_5533_);
return v_r_5534_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5535_, lean_object* v_keys_5536_, lean_object* v_vals_5537_, lean_object* v_heq_5538_, lean_object* v_i_5539_, lean_object* v_k_5540_){
_start:
{
uint8_t v___x_5541_; 
v___x_5541_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5536_, v_i_5539_, v_k_5540_);
return v___x_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5542_, lean_object* v_keys_5543_, lean_object* v_vals_5544_, lean_object* v_heq_5545_, lean_object* v_i_5546_, lean_object* v_k_5547_){
_start:
{
uint8_t v_res_5548_; lean_object* v_r_5549_; 
v_res_5548_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5542_, v_keys_5543_, v_vals_5544_, v_heq_5545_, v_i_5546_, v_k_5547_);
lean_dec_ref(v_k_5547_);
lean_dec_ref(v_vals_5544_);
lean_dec_ref(v_keys_5543_);
v_r_5549_ = lean_box(v_res_5548_);
return v_r_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_){
_start:
{
lean_object* v___x_5558_; 
v___x_5558_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_, v_a_5556_);
return v___x_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_, lean_object* v_a_5563_, lean_object* v_a_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_){
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_);
lean_dec(v_a_5565_);
lean_dec_ref(v_a_5564_);
lean_dec(v_a_5563_);
lean_dec_ref(v_a_5562_);
lean_dec(v_a_5561_);
lean_dec_ref(v_a_5560_);
return v_res_5567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_){
_start:
{
lean_object* v___x_5576_; 
v___x_5576_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_, lean_object* v_a_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_){
_start:
{
lean_object* v_res_5585_; 
v_res_5585_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5577_, v_a_5578_, v_a_5579_, v_a_5580_, v_a_5581_, v_a_5582_, v_a_5583_);
lean_dec(v_a_5583_);
lean_dec_ref(v_a_5582_);
lean_dec(v_a_5581_);
lean_dec_ref(v_a_5580_);
lean_dec(v_a_5579_);
lean_dec_ref(v_a_5578_);
return v_res_5585_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Do_instInhabitedControlInfo_default = _init_l_Lean_Elab_Do_instInhabitedControlInfo_default();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo_default);
l_Lean_Elab_Do_instInhabitedControlInfo = _init_l_Lean_Elab_Do_instInhabitedControlInfo();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo);
l_Lean_Elab_Do_ControlInfo_pure = _init_l_Lean_Elab_Do_ControlInfo_pure();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_pure);
l_Lean_Elab_Do_ControlInfo_empty = _init_l_Lean_Elab_Do_ControlInfo_empty();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_empty);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_1357362724____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_ForwardSyntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_ForwardSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Do_InferControlInfo(builtin);
}
#ifdef __cplusplus
}
#endif
