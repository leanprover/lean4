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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; uint8_t v___y_28_; lean_object* v___y_29_; uint8_t v___y_30_; uint8_t v___y_36_; uint8_t v___y_37_; uint8_t v___y_38_; uint8_t v___y_45_; uint8_t v___y_46_; uint8_t v___y_49_; 
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
v___x_31_ = l_Lean_NameSet_append(v_reassigns_20_, v___y_29_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_31_);
lean_ctor_set(v___x_22_, 0, v___y_26_);
v___x_33_ = v___x_22_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___y_26_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2, v___y_27_);
lean_ctor_set_uint8(v___x_33_, sizeof(void*)*2 + 1, v___y_28_);
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
v___y_26_ = v_numRegularExits_39_;
v___y_27_ = v___y_36_;
v___y_28_ = v___y_37_;
v___y_29_ = v_reassigns_41_;
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
v___y_26_ = v_numRegularExits_42_;
v___y_27_ = v___y_36_;
v___y_28_ = v___y_37_;
v___y_29_ = v_reassigns_43_;
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
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
v___y_38_ = v_returnsEarly_47_;
goto v___jp_35_;
}
else
{
v___y_36_ = v___y_45_;
v___y_37_ = v___y_46_;
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
uint8_t v___y_57_; lean_object* v___y_58_; lean_object* v___y_59_; uint8_t v___y_60_; uint8_t v___y_61_; lean_object* v___y_62_; uint8_t v___y_63_; uint8_t v_breaks_66_; uint8_t v_continues_67_; uint8_t v_returnsEarly_68_; lean_object* v_numRegularExits_69_; uint8_t v_noFallthrough_70_; lean_object* v_reassigns_71_; uint8_t v___y_73_; uint8_t v___y_74_; uint8_t v___y_75_; uint8_t v___y_81_; uint8_t v___y_82_; uint8_t v___y_85_; 
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
v___x_64_ = l_Lean_NameSet_append(v___y_59_, v___y_58_);
v___x_65_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_65_, 0, v___y_62_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2, v___y_61_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 1, v___y_60_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*2 + 2, v___y_57_);
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
v___y_57_ = v___y_75_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v___y_73_;
v___y_61_ = v___y_74_;
v___y_62_ = v___x_79_;
v___y_63_ = v_noFallthrough_70_;
goto v___jp_56_;
}
else
{
v___y_57_ = v___y_75_;
v___y_58_ = v_reassigns_78_;
v___y_59_ = v_reassigns_71_;
v___y_60_ = v___y_73_;
v___y_61_ = v___y_74_;
v___y_62_ = v___x_79_;
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
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_toCold_291_; lean_object* v_mctx_292_; lean_object* v_lctx_293_; lean_object* v_options_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_toCold_291_ = lean_ctor_get(v___y_285_, 0);
v_mctx_292_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_292_);
lean_dec(v___x_290_);
v_lctx_293_ = lean_ctor_get(v___y_283_, 2);
v_options_294_ = lean_ctor_get(v_toCold_291_, 2);
lean_inc_ref(v_options_294_);
lean_inc_ref(v_lctx_293_);
v___x_295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_295_, 0, v_env_289_);
lean_ctor_set(v___x_295_, 1, v_mctx_292_);
lean_ctor_set(v___x_295_, 2, v_lctx_293_);
lean_ctor_set(v___x_295_, 3, v_options_294_);
v___x_296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_msgData_282_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(1);
v___x_306_ = l_Lean_MessageData_ofFormat(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
return v_x_312_;
}
else
{
lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_337_; 
v_head_314_ = lean_ctor_get(v_x_313_, 0);
v_tail_315_ = lean_ctor_get(v_x_313_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_337_ == 0)
{
v___x_317_ = v_x_313_;
v_isShared_318_ = v_isSharedCheck_337_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_head_314_);
lean_dec(v_x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_337_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_before_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_335_; 
v_before_319_ = lean_ctor_get(v_head_314_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_head_314_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_head_314_, 1);
lean_dec(v_unused_336_);
v___x_321_ = v_head_314_;
v_isShared_322_ = v_isSharedCheck_335_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_before_319_);
lean_dec(v_head_314_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_335_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 7);
lean_ctor_set(v___x_321_, 1, v___x_323_);
lean_ctor_set(v___x_321_, 0, v_x_312_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_x_312_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_334_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 7);
lean_ctor_set(v___x_317_, 1, v___x_326_);
lean_ctor_set(v___x_317_, 0, v___x_325_);
v___x_328_ = v___x_317_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_333_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_MessageData_ofSyntax(v_before_319_);
v___x_330_ = l_Lean_indentD(v___x_329_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_x_312_ = v___x_331_;
v_x_313_ = v_tail_315_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_338_, lean_object* v_opt_339_){
_start:
{
lean_object* v_name_340_; lean_object* v_defValue_341_; lean_object* v_map_342_; lean_object* v___x_343_; 
v_name_340_ = lean_ctor_get(v_opt_339_, 0);
v_defValue_341_ = lean_ctor_get(v_opt_339_, 1);
v_map_342_ = lean_ctor_get(v_opts_338_, 0);
v___x_343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_342_, v_name_340_);
if (lean_obj_tag(v___x_343_) == 0)
{
uint8_t v___x_344_; 
v___x_344_ = lean_unbox(v_defValue_341_);
return v___x_344_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v___x_343_, 1);
if (lean_obj_tag(v_val_345_) == 1)
{
uint8_t v_v_346_; 
v_v_346_ = lean_ctor_get_uint8(v_val_345_, 0);
lean_dec_ref_known(v_val_345_, 0);
return v_v_346_;
}
else
{
uint8_t v___x_347_; 
lean_dec(v_val_345_);
v___x_347_ = lean_unbox(v_defValue_341_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_348_, lean_object* v_opt_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_348_, v_opt_349_);
lean_dec_ref(v_opt_349_);
lean_dec_ref(v_opts_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_356_ = l_Lean_MessageData_ofFormat(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_357_, lean_object* v_macroStack_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_toCold_361_; lean_object* v_options_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_toCold_361_ = lean_ctor_get(v___y_359_, 0);
v_options_362_ = lean_ctor_get(v_toCold_361_, 2);
v___x_363_ = l_Lean_Elab_pp_macroStack;
v___x_364_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec(v_macroStack_358_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v_msgData_357_);
return v___x_365_;
}
else
{
if (lean_obj_tag(v_macroStack_358_) == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v_msgData_357_);
return v___x_366_;
}
else
{
lean_object* v_head_367_; lean_object* v_after_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_383_; 
v_head_367_ = lean_ctor_get(v_macroStack_358_, 0);
lean_inc(v_head_367_);
v_after_368_ = lean_ctor_get(v_head_367_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_head_367_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_head_367_, 0);
lean_dec(v_unused_384_);
v___x_370_ = v_head_367_;
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_after_368_);
lean_dec(v_head_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_383_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_371_ == 0)
{
lean_ctor_set_tag(v___x_370_, 7);
lean_ctor_set(v___x_370_, 1, v___x_372_);
lean_ctor_set(v___x_370_, 0, v_msgData_357_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_msgData_357_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v_msgData_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_375_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_MessageData_ofSyntax(v_after_368_);
v___x_378_ = l_Lean_indentD(v___x_377_);
v_msgData_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_379_, 0, v___x_376_);
lean_ctor_set(v_msgData_379_, 1, v___x_378_);
v___x_380_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_379_, v_macroStack_358_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_385_, lean_object* v_macroStack_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_385_, v_macroStack_386_, v___y_387_);
lean_dec_ref(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_ref_398_; lean_object* v_macroStack_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_ref_398_ = lean_ctor_get(v___y_395_, 2);
v_macroStack_399_ = lean_ctor_get(v___y_391_, 1);
v___x_400_ = l_Lean_Elab_getBetterRef(v_ref_398_, v_macroStack_399_);
v___x_401_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_390_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v___x_401_);
lean_inc(v_macroStack_399_);
v___x_403_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_402_, v_macroStack_399_, v___y_395_);
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_400_);
lean_ctor_set(v___x_408_, 1, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_422_, size_t v_i_423_, size_t v_stop_424_, lean_object* v_b_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_eq(v_i_423_, v_stop_424_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; 
v___x_427_ = lean_array_uget_borrowed(v_as_422_, v_i_423_);
lean_inc(v___x_427_);
v___x_428_ = l_Lean_NameSet_insert(v_b_425_, v___x_427_);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_add(v_i_423_, v___x_429_);
v_i_423_ = v___x_430_;
v_b_425_ = v___x_428_;
goto _start;
}
else
{
return v_b_425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_432_, lean_object* v_i_433_, lean_object* v_stop_434_, lean_object* v_b_435_){
_start:
{
size_t v_i_boxed_436_; size_t v_stop_boxed_437_; lean_object* v_res_438_; 
v_i_boxed_436_ = lean_unbox_usize(v_i_433_);
lean_dec(v_i_433_);
v_stop_boxed_437_ = lean_unbox_usize(v_stop_434_);
lean_dec(v_stop_434_);
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_432_, v_i_boxed_436_, v_stop_boxed_437_, v_b_435_);
lean_dec_ref(v_as_432_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
return v_bs_441_;
}
else
{
lean_object* v_v_443_; lean_object* v___x_444_; lean_object* v_bs_x27_445_; lean_object* v___x_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_v_443_ = lean_array_uget(v_bs_441_, v_i_440_);
v___x_444_ = lean_unsigned_to_nat(0u);
v_bs_x27_445_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_444_);
v___x_446_ = l_Lean_TSyntax_getId(v_v_443_);
lean_dec(v_v_443_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_440_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_445_, v_i_440_, v___x_446_);
v_i_440_ = v___x_448_;
v_bs_441_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_bs_453_){
_start:
{
size_t v_sz_boxed_454_; size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_sz_boxed_454_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_454_, v_i_boxed_455_, v_bs_453_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
v___x_458_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_465_, size_t v_i_466_, lean_object* v_bs_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = lean_usize_dec_lt(v_i_466_, v_sz_465_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v_bs_467_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v_bs_x27_471_; lean_object* v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v_bs_x27_471_ = lean_array_uset(v_bs_467_, v_i_466_, v___x_470_);
v___x_472_ = lean_box(0);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_add(v_i_466_, v___x_473_);
v___x_475_ = lean_array_uset(v_bs_x27_471_, v_i_466_, v___x_472_);
v_i_466_ = v___x_474_;
v_bs_467_ = v___x_475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_bs_479_){
_start:
{
size_t v_sz_boxed_480_; size_t v_i_boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_480_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_481_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_480_, v_i_boxed_481_, v_bs_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_483_, uint8_t v___x_484_, lean_object* v_as_485_, size_t v_i_486_, size_t v_stop_487_, lean_object* v_b_488_){
_start:
{
lean_object* v___y_490_; uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_eq(v_i_486_, v_stop_487_);
if (v___x_494_ == 0)
{
lean_object* v_fst_495_; uint8_t v___x_496_; 
v_fst_495_ = lean_ctor_get(v_b_488_, 0);
v___x_496_ = lean_unbox(v_fst_495_);
if (v___x_496_ == 0)
{
lean_object* v_snd_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_snd_497_ = lean_ctor_get(v_b_488_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_b_488_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_b_488_, 0);
lean_dec(v_unused_506_);
v___x_499_ = v_b_488_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_snd_497_);
lean_dec(v_b_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_box(v___x_483_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_snd_497_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v___y_490_ = v___x_503_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_snd_507_ = lean_ctor_get(v_b_488_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_b_488_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_b_488_, 0);
lean_dec(v_unused_518_);
v___x_509_ = v_b_488_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_dec(v_b_488_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_511_ = lean_array_uget_borrowed(v_as_485_, v_i_486_);
lean_inc(v___x_511_);
v___x_512_ = lean_array_push(v_snd_507_, v___x_511_);
v___x_513_ = lean_box(v___x_484_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_512_);
lean_ctor_set(v___x_509_, 0, v___x_513_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_512_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_490_ = v___x_515_;
goto v___jp_489_;
}
}
}
}
else
{
return v_b_488_;
}
v___jp_489_:
{
size_t v___x_491_; size_t v___x_492_; 
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_add(v_i_486_, v___x_491_);
v_i_486_ = v___x_492_;
v_b_488_ = v___y_490_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
uint8_t v___x_175581__boxed_525_; uint8_t v___x_175582__boxed_526_; size_t v_i_boxed_527_; size_t v_stop_boxed_528_; lean_object* v_res_529_; 
v___x_175581__boxed_525_ = lean_unbox(v___x_519_);
v___x_175582__boxed_526_ = lean_unbox(v___x_520_);
v_i_boxed_527_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_528_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_175581__boxed_525_, v___x_175582__boxed_526_, v_as_521_, v_i_boxed_527_, v_stop_boxed_528_, v_b_524_);
lean_dec_ref(v_as_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_530_, lean_object* v_declName_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v___x_534_; lean_object* v_env_535_; lean_object* v___x_536_; uint8_t v___x_537_; uint8_t v___x_538_; 
v___x_534_ = 0;
v_env_535_ = l_Lean_Environment_setExporting(v_env_530_, v___x_534_);
lean_inc(v_declName_531_);
v___x_536_ = l_Lean_mkPrivateName(v_env_535_, v_declName_531_);
v___x_537_ = 1;
lean_inc_ref(v_env_535_);
v___x_538_ = l_Lean_Environment_contains(v_env_535_, v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = l_Lean_privateToUserName(v_declName_531_);
v___x_540_ = l_Lean_Environment_contains(v_env_535_, v___x_539_, v___x_537_);
v___x_541_ = lean_box(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_533_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_env_535_);
lean_dec(v_declName_531_);
v___x_543_ = lean_box(v___x_538_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___y_533_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_545_, lean_object* v_declName_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_545_, v_declName_546_, v___y_547_, v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_549_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = l_Lean_maxRecDepthErrorMessage;
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_558_ = l_Lean_MessageData_ofFormat(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_560_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_561_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_562_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_ref_562_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_x_570_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_572_);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_572_);
lean_ctor_set(v___x_573_, 1, v___y_571_);
return v___x_573_;
}
else
{
lean_object* v_a_574_; lean_object* v___x_575_; 
v_a_574_ = lean_ctor_get(v_x_570_, 0);
lean_inc(v_a_574_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v_a_574_);
lean_ctor_set(v___x_575_, 1, v___y_571_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_576_, v___y_577_);
lean_dec_ref(v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_579_, lean_object* v_stx_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_579_, v_stx_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
if (lean_obj_tag(v_a_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_a_585_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_593_ == 0)
{
lean_object* v_unused_594_; 
v_unused_594_ = lean_ctor_get(v___x_583_, 0);
lean_dec(v_unused_594_);
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = lean_box(0);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_585_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_623_; 
v_val_595_ = lean_ctor_get(v_a_584_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_584_);
if (v_isSharedCheck_623_ == 0)
{
v___x_597_ = v_a_584_;
v_isShared_598_ = v_isSharedCheck_623_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v_a_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_623_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_snd_599_; 
v_snd_599_ = lean_ctor_get(v_val_595_, 1);
lean_inc(v_snd_599_);
lean_dec(v_val_595_);
if (lean_obj_tag(v_snd_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
lean_del_object(v___x_597_);
v_a_600_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_583_, 2);
v_a_601_ = lean_ctor_get(v_snd_599_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v_snd_599_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_snd_599_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v_snd_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_606_, v_a_600_);
lean_dec_ref(v___x_606_);
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_622_; 
v_a_610_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_583_, 2);
v_a_611_ = lean_ctor_get(v_snd_599_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_snd_599_);
if (v_isSharedCheck_622_ == 0)
{
v___x_613_ = v_snd_599_;
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v_snd_599_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_a_611_);
v___x_616_ = v___x_597_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_621_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_616_);
v___x_618_ = v___x_613_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_620_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; 
v___x_619_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_618_, v_a_610_);
lean_dec_ref(v___x_618_);
return v___x_619_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_624_ = lean_ctor_get(v___x_583_, 0);
v_a_625_ = lean_ctor_get(v___x_583_, 1);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_583_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_inc(v_a_624_);
lean_dec(v___x_583_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_624_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_633_, lean_object* v_stx_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_633_, v_stx_634_, v___y_635_, v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_638_, lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_toCold_647_; lean_object* v_currRecDepth_648_; lean_object* v_ref_649_; uint8_t v_diag_650_; uint8_t v_suppressElabErrors_651_; lean_object* v_ref_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_toCold_647_ = lean_ctor_get(v___y_644_, 0);
v_currRecDepth_648_ = lean_ctor_get(v___y_644_, 1);
v_ref_649_ = lean_ctor_get(v___y_644_, 2);
v_diag_650_ = lean_ctor_get_uint8(v___y_644_, sizeof(void*)*3);
v_suppressElabErrors_651_ = lean_ctor_get_uint8(v___y_644_, sizeof(void*)*3 + 1);
v_ref_652_ = l_Lean_replaceRef(v_ref_638_, v_ref_649_);
lean_inc(v_currRecDepth_648_);
lean_inc_ref(v_toCold_647_);
v___x_653_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_653_, 0, v_toCold_647_);
lean_ctor_set(v___x_653_, 1, v_currRecDepth_648_);
lean_ctor_set(v___x_653_, 2, v_ref_652_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3, v_diag_650_);
lean_ctor_set_uint8(v___x_653_, sizeof(void*)*3 + 1, v_suppressElabErrors_651_);
v___x_654_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___x_653_, v___y_645_);
lean_dec_ref_known(v___x_653_, 3);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_655_, v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v_ref_655_);
return v_res_664_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_665_; double v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_float_of_nat(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_670_, lean_object* v_msg_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_ref_677_; lean_object* v___x_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_723_; 
v_ref_677_ = lean_ctor_get(v___y_674_, 2);
v___x_678_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_723_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_723_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_723_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_traceState_684_; lean_object* v_env_685_; lean_object* v_nextMacroScope_686_; lean_object* v_ngen_687_; lean_object* v_auxDeclNGen_688_; lean_object* v_cache_689_; lean_object* v_messages_690_; lean_object* v_infoState_691_; lean_object* v_snapshotTasks_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_722_; 
v___x_683_ = lean_st_ref_take(v___y_675_);
v_traceState_684_ = lean_ctor_get(v___x_683_, 4);
v_env_685_ = lean_ctor_get(v___x_683_, 0);
v_nextMacroScope_686_ = lean_ctor_get(v___x_683_, 1);
v_ngen_687_ = lean_ctor_get(v___x_683_, 2);
v_auxDeclNGen_688_ = lean_ctor_get(v___x_683_, 3);
v_cache_689_ = lean_ctor_get(v___x_683_, 5);
v_messages_690_ = lean_ctor_get(v___x_683_, 6);
v_infoState_691_ = lean_ctor_get(v___x_683_, 7);
v_snapshotTasks_692_ = lean_ctor_get(v___x_683_, 8);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_722_ == 0)
{
v___x_694_ = v___x_683_;
v_isShared_695_ = v_isSharedCheck_722_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snapshotTasks_692_);
lean_inc(v_infoState_691_);
lean_inc(v_messages_690_);
lean_inc(v_cache_689_);
lean_inc(v_traceState_684_);
lean_inc(v_auxDeclNGen_688_);
lean_inc(v_ngen_687_);
lean_inc(v_nextMacroScope_686_);
lean_inc(v_env_685_);
lean_dec(v___x_683_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_722_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
uint64_t v_tid_696_; lean_object* v_traces_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_721_; 
v_tid_696_ = lean_ctor_get_uint64(v_traceState_684_, sizeof(void*)*1);
v_traces_697_ = lean_ctor_get(v_traceState_684_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_traceState_684_);
if (v_isSharedCheck_721_ == 0)
{
v___x_699_ = v_traceState_684_;
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_traces_697_);
lean_dec(v_traceState_684_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_721_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; double v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_701_ = lean_box(0);
v___x_702_ = lean_box(0);
v___x_703_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_704_ = 0;
v___x_705_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_706_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_706_, 0, v_cls_670_);
lean_ctor_set(v___x_706_, 1, v___x_702_);
lean_ctor_set(v___x_706_, 2, v___x_705_);
lean_ctor_set_float(v___x_706_, sizeof(void*)*3, v___x_703_);
lean_ctor_set_float(v___x_706_, sizeof(void*)*3 + 8, v___x_703_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*3 + 16, v___x_704_);
v___x_707_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_708_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v_a_679_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
lean_inc(v_ref_677_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_ref_677_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_PersistentArray_push___redArg(v_traces_697_, v___x_709_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_710_);
v___x_712_ = v___x_699_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_710_);
lean_ctor_set_uint64(v_reuseFailAlloc_720_, sizeof(void*)*1, v_tid_696_);
v___x_712_ = v_reuseFailAlloc_720_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v___x_712_);
v___x_714_ = v___x_694_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_env_685_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_nextMacroScope_686_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_ngen_687_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_auxDeclNGen_688_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 5, v_cache_689_);
lean_ctor_set(v_reuseFailAlloc_719_, 6, v_messages_690_);
lean_ctor_set(v_reuseFailAlloc_719_, 7, v_infoState_691_);
lean_ctor_set(v_reuseFailAlloc_719_, 8, v_snapshotTasks_692_);
v___x_714_ = v_reuseFailAlloc_719_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_st_ref_put(v___y_675_, v___x_714_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_701_);
v___x_717_ = v___x_681_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_701_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_724_, lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_724_, v_msg_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
if (lean_obj_tag(v_as_735_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_toCold_745_; lean_object* v_options_746_; uint8_t v_hasTrace_747_; 
v_toCold_745_ = lean_ctor_get(v___y_740_, 0);
v_options_746_ = lean_ctor_get(v_toCold_745_, 2);
v_hasTrace_747_ = lean_ctor_get_uint8(v_options_746_, sizeof(void*)*1);
if (v_hasTrace_747_ == 0)
{
lean_object* v_tail_748_; 
v_tail_748_ = lean_ctor_get(v_as_735_, 1);
lean_inc(v_tail_748_);
lean_dec_ref_known(v_as_735_, 2);
v_as_735_ = v_tail_748_;
goto _start;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v_inheritedTraceOptions_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_head_750_ = lean_ctor_get(v_as_735_, 0);
lean_inc(v_head_750_);
v_tail_751_ = lean_ctor_get(v_as_735_, 1);
lean_inc(v_tail_751_);
lean_dec_ref_known(v_as_735_, 2);
v_fst_752_ = lean_ctor_get(v_head_750_, 0);
lean_inc_n(v_fst_752_, 2);
v_snd_753_ = lean_ctor_get(v_head_750_, 1);
lean_inc(v_snd_753_);
lean_dec(v_head_750_);
v_inheritedTraceOptions_754_ = lean_ctor_get(v_toCold_745_, 11);
v___x_755_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_756_ = l_Lean_Name_append(v___x_755_, v_fst_752_);
v___x_757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_754_, v_options_746_, v___x_756_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v_snd_753_);
lean_dec(v_fst_752_);
v_as_735_ = v_tail_751_;
goto _start;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_759_, 0, v_snd_753_);
v___x_760_ = l_Lean_MessageData_ofFormat(v___x_759_);
v___x_761_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_752_, v___x_760_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_dec_ref_known(v___x_761_, 1);
v_as_735_ = v_tail_751_;
goto _start;
}
else
{
lean_dec(v_tail_751_);
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 0)
{
lean_object* v___x_774_; 
v___x_774_ = lean_box(0);
return v___x_774_;
}
else
{
lean_object* v_key_775_; lean_object* v_value_776_; lean_object* v_tail_777_; uint8_t v___x_778_; 
v_key_775_ = lean_ctor_get(v_x_773_, 0);
v_value_776_ = lean_ctor_get(v_x_773_, 1);
v_tail_777_ = lean_ctor_get(v_x_773_, 2);
v___x_778_ = lean_name_eq(v_key_775_, v_a_772_);
if (v___x_778_ == 0)
{
v_x_773_ = v_tail_777_;
goto _start;
}
else
{
lean_object* v___x_780_; 
lean_inc(v_value_776_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_value_776_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_781_, lean_object* v_x_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_buckets_786_; lean_object* v___x_787_; uint64_t v___y_789_; 
v_buckets_786_ = lean_ctor_get(v_m_784_, 1);
v___x_787_ = lean_array_get_size(v_buckets_786_);
if (lean_obj_tag(v_a_785_) == 0)
{
uint64_t v___x_803_; 
v___x_803_ = 1723ULL;
v___y_789_ = v___x_803_;
goto v___jp_788_;
}
else
{
uint64_t v_hash_804_; 
v_hash_804_ = lean_ctor_get_uint64(v_a_785_, sizeof(void*)*2);
v___y_789_ = v_hash_804_;
goto v___jp_788_;
}
v___jp_788_:
{
uint64_t v___x_790_; uint64_t v___x_791_; uint64_t v_fold_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_790_ = 32ULL;
v___x_791_ = lean_uint64_shift_right(v___y_789_, v___x_790_);
v_fold_792_ = lean_uint64_xor(v___y_789_, v___x_791_);
v___x_793_ = 16ULL;
v___x_794_ = lean_uint64_shift_right(v_fold_792_, v___x_793_);
v___x_795_ = lean_uint64_xor(v_fold_792_, v___x_794_);
v___x_796_ = lean_uint64_to_usize(v___x_795_);
v___x_797_ = lean_usize_of_nat(v___x_787_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_sub(v___x_797_, v___x_798_);
v___x_800_ = lean_usize_land(v___x_796_, v___x_799_);
v___x_801_ = lean_array_uget_borrowed(v_buckets_786_, v___x_800_);
v___x_802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_785_, v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_m_805_);
return v_res_807_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_808_, lean_object* v_i_809_, lean_object* v_k_810_){
_start:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = lean_array_get_size(v_keys_808_);
v___x_812_ = lean_nat_dec_lt(v_i_809_, v___x_811_);
if (v___x_812_ == 0)
{
lean_dec(v_i_809_);
return v___x_812_;
}
else
{
lean_object* v_k_x27_813_; uint8_t v___x_814_; 
v_k_x27_813_ = lean_array_fget_borrowed(v_keys_808_, v_i_809_);
v___x_814_ = l_Lean_instBEqExtraModUse_beq(v_k_810_, v_k_x27_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_i_809_, v___x_815_);
lean_dec(v_i_809_);
v_i_809_ = v___x_816_;
goto _start;
}
else
{
lean_dec(v_i_809_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_818_, v_i_819_, v_k_820_);
lean_dec_ref(v_k_820_);
lean_dec_ref(v_keys_818_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_823_, size_t v_x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_es_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v_j_830_; lean_object* v___x_831_; 
v_es_826_ = lean_ctor_get(v_x_823_, 0);
v___x_827_ = lean_box(2);
v___x_828_ = ((size_t)31ULL);
v___x_829_ = lean_usize_land(v_x_824_, v___x_828_);
v_j_830_ = lean_usize_to_nat(v___x_829_);
v___x_831_ = lean_array_get_borrowed(v___x_827_, v_es_826_, v_j_830_);
lean_dec(v_j_830_);
switch(lean_obj_tag(v___x_831_))
{
case 0:
{
lean_object* v_key_832_; uint8_t v___x_833_; 
v_key_832_ = lean_ctor_get(v___x_831_, 0);
v___x_833_ = l_Lean_instBEqExtraModUse_beq(v_x_825_, v_key_832_);
return v___x_833_;
}
case 1:
{
lean_object* v_node_834_; size_t v___x_835_; size_t v___x_836_; 
v_node_834_ = lean_ctor_get(v___x_831_, 0);
v___x_835_ = ((size_t)5ULL);
v___x_836_ = lean_usize_shift_right(v_x_824_, v___x_835_);
v_x_823_ = v_node_834_;
v_x_824_ = v___x_836_;
goto _start;
}
default: 
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
}
else
{
lean_object* v_ks_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_ks_839_ = lean_ctor_get(v_x_823_, 0);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_839_, v___x_840_, v_x_825_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
size_t v_x_176093__boxed_845_; uint8_t v_res_846_; lean_object* v_r_847_; 
v_x_176093__boxed_845_ = lean_unbox_usize(v_x_843_);
lean_dec(v_x_843_);
v_res_846_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_842_, v_x_176093__boxed_845_, v_x_844_);
lean_dec_ref(v_x_844_);
lean_dec_ref(v_x_842_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint64_t v___x_850_; size_t v___x_851_; uint8_t v___x_852_; 
v___x_850_ = l_Lean_instHashableExtraModUse_hash(v_x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_848_, v___x_851_, v_x_849_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint8_t v_res_855_; lean_object* v_r_856_; 
v_res_855_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_853_, v_x_854_);
lean_dec_ref(v_x_854_);
lean_dec_ref(v_x_853_);
v_r_856_ = lean_box(v_res_855_);
return v_r_856_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_857_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_858_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
v___x_864_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
lean_ctor_set(v___x_864_, 3, v___x_863_);
lean_ctor_set(v___x_864_, 4, v___x_863_);
lean_ctor_set(v___x_864_, 5, v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v_cls_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_cls_876_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_877_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_878_ = l_Lean_Name_append(v___x_877_, v_cls_876_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_889_, uint8_t v_isMeta_890_, lean_object* v_hint_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_env_901_; uint8_t v_isExporting_902_; lean_object* v_entry_903_; lean_object* v___x_904_; lean_object* v_env_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_899_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0);
v___x_900_ = lean_st_ref_get(v___y_897_);
v_env_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_env_901_);
lean_dec(v___x_900_);
v_isExporting_902_ = lean_ctor_get_uint8(v_env_901_, sizeof(void*)*8);
lean_dec_ref(v_env_901_);
lean_inc(v_mod_889_);
v_entry_903_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_903_, 0, v_mod_889_);
lean_ctor_set_uint8(v_entry_903_, sizeof(void*)*1, v_isExporting_902_);
lean_ctor_set_uint8(v_entry_903_, sizeof(void*)*1 + 1, v_isMeta_890_);
v___x_904_ = lean_st_ref_get(v___y_897_);
v_env_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_ref(v_env_905_);
lean_dec(v___x_904_);
v___x_906_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_907_ = lean_box(1);
v___x_908_ = lean_box(0);
v___x_951_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_899_, v___x_906_, v_env_905_, v___x_907_, v___x_908_);
v___x_952_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_951_, v_entry_903_);
lean_dec(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v_toCold_953_; lean_object* v_options_954_; uint8_t v_hasTrace_955_; 
v_toCold_953_ = lean_ctor_get(v___y_896_, 0);
v_options_954_ = lean_ctor_get(v_toCold_953_, 2);
v_hasTrace_955_ = lean_ctor_get_uint8(v_options_954_, sizeof(void*)*1);
if (v_hasTrace_955_ == 0)
{
lean_dec(v_hint_891_);
lean_dec(v_mod_889_);
v___y_910_ = v___y_895_;
v___y_911_ = v___y_897_;
goto v___jp_909_;
}
else
{
lean_object* v_inheritedTraceOptions_956_; lean_object* v_cls_957_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_inheritedTraceOptions_956_ = lean_ctor_get(v_toCold_953_, 11);
v_cls_957_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6));
v___x_977_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_978_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_956_, v_options_954_, v___x_977_);
if (v___x_978_ == 0)
{
lean_dec(v_hint_891_);
lean_dec(v_mod_889_);
v___y_910_ = v___y_895_;
v___y_911_ = v___y_897_;
goto v___jp_909_;
}
else
{
lean_object* v___x_979_; lean_object* v___y_981_; 
v___x_979_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
if (v_isExporting_902_ == 0)
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_981_ = v___x_988_;
goto v___jp_980_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_981_ = v___x_989_;
goto v___jp_980_;
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_inc_ref(v___y_981_);
v___x_982_ = l_Lean_stringToMessageData(v___y_981_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_979_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
if (v_isMeta_890_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___y_964_ = v___x_985_;
v___y_965_ = v___x_986_;
goto v___jp_963_;
}
else
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18));
v___y_964_ = v___x_985_;
v___y_965_ = v___x_987_;
goto v___jp_963_;
}
}
}
v___jp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___y_959_);
lean_ctor_set(v___x_961_, 1, v___y_960_);
v___x_962_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_957_, v___x_961_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_dec_ref_known(v___x_962_, 1);
v___y_910_ = v___y_895_;
v___y_911_ = v___y_897_;
goto v___jp_909_;
}
else
{
lean_dec_ref_known(v_entry_903_, 1);
return v___x_962_;
}
}
v___jp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
lean_inc_ref(v___y_965_);
v___x_966_ = l_Lean_stringToMessageData(v___y_965_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___y_964_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_MessageData_ofName(v_mod_889_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_Name_isAnonymous(v_hint_891_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_974_ = l_Lean_MessageData_ofName(v_hint_891_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___y_959_ = v___x_971_;
v___y_960_ = v___x_975_;
goto v___jp_958_;
}
else
{
lean_object* v___x_976_; 
lean_dec(v_hint_891_);
v___x_976_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11);
v___y_959_ = v___x_971_;
v___y_960_ = v___x_976_;
goto v___jp_958_;
}
}
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref_known(v_entry_903_, 1);
lean_dec(v_hint_891_);
lean_dec(v_mod_889_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
v___jp_909_:
{
lean_object* v___x_912_; lean_object* v_toEnvExtension_913_; lean_object* v_env_914_; lean_object* v_nextMacroScope_915_; lean_object* v_ngen_916_; lean_object* v_auxDeclNGen_917_; lean_object* v_traceState_918_; lean_object* v_messages_919_; lean_object* v_infoState_920_; lean_object* v_snapshotTasks_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_949_; 
v___x_912_ = lean_st_ref_take(v___y_911_);
v_toEnvExtension_913_ = lean_ctor_get(v___x_906_, 0);
v_env_914_ = lean_ctor_get(v___x_912_, 0);
v_nextMacroScope_915_ = lean_ctor_get(v___x_912_, 1);
v_ngen_916_ = lean_ctor_get(v___x_912_, 2);
v_auxDeclNGen_917_ = lean_ctor_get(v___x_912_, 3);
v_traceState_918_ = lean_ctor_get(v___x_912_, 4);
v_messages_919_ = lean_ctor_get(v___x_912_, 6);
v_infoState_920_ = lean_ctor_get(v___x_912_, 7);
v_snapshotTasks_921_ = lean_ctor_get(v___x_912_, 8);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v___x_912_, 5);
lean_dec(v_unused_950_);
v___x_923_ = v___x_912_;
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snapshotTasks_921_);
lean_inc(v_infoState_920_);
lean_inc(v_messages_919_);
lean_inc(v_traceState_918_);
lean_inc(v_auxDeclNGen_917_);
lean_inc(v_ngen_916_);
lean_inc(v_nextMacroScope_915_);
lean_inc(v_env_914_);
lean_dec(v___x_912_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_asyncMode_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v_asyncMode_925_ = lean_ctor_get(v_toEnvExtension_913_, 2);
v___x_926_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_906_, v_env_914_, v_entry_903_, v_asyncMode_925_, v___x_908_);
v___x_927_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 5, v___x_927_);
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_nextMacroScope_915_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_ngen_916_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_auxDeclNGen_917_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_traceState_918_);
lean_ctor_set(v_reuseFailAlloc_948_, 5, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_948_, 6, v_messages_919_);
lean_ctor_set(v_reuseFailAlloc_948_, 7, v_infoState_920_);
lean_ctor_set(v_reuseFailAlloc_948_, 8, v_snapshotTasks_921_);
v___x_929_ = v_reuseFailAlloc_948_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_mctx_932_; lean_object* v_zetaDeltaFVarIds_933_; lean_object* v_postponed_934_; lean_object* v_diag_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_946_; 
v___x_930_ = lean_st_ref_put(v___y_911_, v___x_929_);
v___x_931_ = lean_st_ref_take(v___y_910_);
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
v___x_940_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
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
v___x_943_ = lean_st_ref_put(v___y_910_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
return v___x_944_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_992_, lean_object* v_isMeta_993_, lean_object* v_hint_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_isMeta_boxed_1002_; lean_object* v_res_1003_; 
v_isMeta_boxed_1002_ = lean_unbox(v_isMeta_993_);
v_res_1003_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_992_, v_isMeta_boxed_1002_, v_hint_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1004_, lean_object* v_declName_1005_, lean_object* v_as_1006_, size_t v_sz_1007_, size_t v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_usize_dec_lt(v_i_1008_, v_sz_1007_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v_declName_1005_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v_b_1009_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v_modules_1020_; lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v_toImport_1024_; lean_object* v_module_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1019_ = l_Lean_Environment_header(v___x_1004_);
v_modules_1020_ = lean_ctor_get(v___x_1019_, 3);
lean_inc_ref(v_modules_1020_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1022_ = lean_array_uget_borrowed(v_as_1006_, v_i_1008_);
v___x_1023_ = lean_array_get(v___x_1021_, v_modules_1020_, v_a_1022_);
lean_dec_ref(v_modules_1020_);
v_toImport_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc_ref(v_toImport_1024_);
lean_dec(v___x_1023_);
v_module_1025_ = lean_ctor_get(v_toImport_1024_, 0);
lean_inc(v_module_1025_);
lean_dec_ref(v_toImport_1024_);
v___x_1026_ = lean_box(0);
v___x_1027_ = 0;
lean_inc(v_declName_1005_);
v___x_1028_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1025_, v___x_1027_, v_declName_1005_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1028_) == 0)
{
size_t v___x_1029_; size_t v___x_1030_; 
lean_dec_ref_known(v___x_1028_, 1);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1008_, v___x_1029_);
v_i_1008_ = v___x_1030_;
v_b_1009_ = v___x_1026_;
goto _start;
}
else
{
lean_dec(v_declName_1005_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1032_, lean_object* v_declName_1033_, lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
size_t v_sz_boxed_1045_; size_t v_i_boxed_1046_; lean_object* v_res_1047_; 
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1046_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1032_, v_declName_1033_, v_as_1034_, v_sz_boxed_1045_, v_i_boxed_1046_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec_ref(v_as_1034_);
lean_dec_ref(v___x_1032_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1051_, uint8_t v_isMeta_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_env_1065_; lean_object* v___y_1067_; lean_object* v___x_1080_; 
v___x_1060_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0);
v___x_1061_ = lean_st_ref_get(v___y_1058_);
v_env_1065_ = lean_ctor_get(v___x_1061_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1061_);
v___x_1080_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1065_, v_declName_1051_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_dec_ref(v_env_1065_);
lean_dec(v_declName_1051_);
goto v___jp_1062_;
}
else
{
lean_object* v_val_1081_; lean_object* v___x_1082_; lean_object* v_modules_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_val_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = l_Lean_Environment_header(v_env_1065_);
v_modules_1083_ = lean_ctor_get(v___x_1082_, 3);
lean_inc_ref(v_modules_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = lean_array_get_size(v_modules_1083_);
v___x_1085_ = lean_nat_dec_lt(v_val_1081_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v_modules_1083_);
lean_dec(v_val_1081_);
lean_dec_ref(v_env_1065_);
lean_dec(v_declName_1051_);
goto v___jp_1062_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___y_1089_; 
v___x_1086_ = lean_array_fget(v_modules_1083_, v_val_1081_);
lean_dec(v_val_1081_);
lean_dec_ref(v_modules_1083_);
v___x_1087_ = lean_st_ref_get(v___y_1058_);
if (v_isMeta_1052_ == 0)
{
lean_dec(v___x_1087_);
v___y_1089_ = v_isMeta_1052_;
goto v___jp_1088_;
}
else
{
lean_object* v_env_1100_; uint8_t v___x_1101_; 
v_env_1100_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_env_1100_);
lean_dec(v___x_1087_);
lean_inc(v_declName_1051_);
v___x_1101_ = l_Lean_isMarkedMeta(v_env_1100_, v_declName_1051_);
if (v___x_1101_ == 0)
{
v___y_1089_ = v_isMeta_1052_;
goto v___jp_1088_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
v___y_1089_ = v___x_1102_;
goto v___jp_1088_;
}
}
v___jp_1088_:
{
lean_object* v_toImport_1090_; lean_object* v_module_1091_; lean_object* v___x_1092_; 
v_toImport_1090_ = lean_ctor_get(v___x_1086_, 0);
lean_inc_ref(v_toImport_1090_);
lean_dec(v___x_1086_);
v_module_1091_ = lean_ctor_get(v_toImport_1090_, 0);
lean_inc(v_module_1091_);
lean_dec_ref(v_toImport_1090_);
lean_inc(v_declName_1051_);
v___x_1092_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1091_, v___y_1089_, v_declName_1051_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref_known(v___x_1092_, 1);
v___x_1093_ = l_Lean_indirectModUseExt;
v___x_1094_ = lean_box(1);
v___x_1095_ = lean_box(0);
lean_inc_ref(v_env_1065_);
v___x_1096_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1060_, v___x_1093_, v_env_1065_, v___x_1094_, v___x_1095_);
v___x_1097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1096_, v_declName_1051_);
lean_dec(v___x_1096_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___y_1067_ = v___x_1098_;
goto v___jp_1066_;
}
else
{
lean_object* v_val_1099_; 
v_val_1099_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1097_, 1);
v___y_1067_ = v_val_1099_;
goto v___jp_1066_;
}
}
else
{
lean_dec_ref(v_env_1065_);
lean_dec(v_declName_1051_);
return v___x_1092_;
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = lean_box(0);
v_sz_1069_ = lean_array_size(v___y_1067_);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1065_, v_declName_1051_, v___y_1067_, v_sz_1069_, v___x_1070_, v___x_1068_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v_env_1065_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1071_, 0);
lean_dec(v_unused_1079_);
v___x_1073_ = v___x_1071_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v___x_1071_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1068_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1103_, lean_object* v_isMeta_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v_isMeta_boxed_1112_; lean_object* v_res_1113_; 
v_isMeta_boxed_1112_ = lean_unbox(v_isMeta_1104_);
v_res_1113_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1103_, v_isMeta_boxed_1112_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1114_, lean_object* v_b_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
if (lean_obj_tag(v_as_x27_1114_) == 0)
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_b_1115_);
return v___x_1123_;
}
else
{
lean_object* v_head_1124_; lean_object* v_tail_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
v_head_1124_ = lean_ctor_get(v_as_x27_1114_, 0);
v_tail_1125_ = lean_ctor_get(v_as_x27_1114_, 1);
v___x_1126_ = lean_box(0);
v___x_1127_ = 1;
lean_inc(v_head_1124_);
v___x_1128_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1124_, v___x_1127_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_dec_ref_known(v___x_1128_, 1);
v_as_x27_1114_ = v_tail_1125_;
v_b_1115_ = v___x_1126_;
goto _start;
}
else
{
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1130_, v_b_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v_as_x27_1130_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1140_, lean_object* v_currNamespace_1141_, lean_object* v_openDecls_1142_, lean_object* v_n_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = l_Lean_ResolveName_resolveNamespace(v_env_1140_, v_currNamespace_1141_, v_openDecls_1142_, v_n_1143_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1148_, lean_object* v_currNamespace_1149_, lean_object* v_openDecls_1150_, lean_object* v_n_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1148_, v_currNamespace_1149_, v_openDecls_1150_, v_n_1151_, v___y_1152_, v___y_1153_);
lean_dec_ref(v___y_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_currNamespace_1155_);
lean_ctor_set(v___x_1158_, 1, v___y_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1159_, v___y_1160_, v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1163_, lean_object* v_options_1164_, lean_object* v_currNamespace_1165_, lean_object* v_openDecls_1166_, lean_object* v_n_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = l_Lean_ResolveName_resolveGlobalName(v_env_1163_, v_options_1164_, v_currNamespace_1165_, v_openDecls_1166_, v_n_1167_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___y_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1172_, lean_object* v_options_1173_, lean_object* v_currNamespace_1174_, lean_object* v_openDecls_1175_, lean_object* v_n_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1172_, v_options_1173_, v_currNamespace_1174_, v_openDecls_1175_, v_n_1176_, v___y_1177_, v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_options_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_toCold_1190_; lean_object* v_env_1191_; lean_object* v_currRecDepth_1192_; lean_object* v_ref_1193_; lean_object* v_options_1194_; lean_object* v_maxRecDepth_1195_; lean_object* v_currNamespace_1196_; lean_object* v_openDecls_1197_; lean_object* v_quotContext_1198_; lean_object* v_currMacroScope_1199_; lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v_methods_1205_; lean_object* v___x_1206_; lean_object* v_nextMacroScope_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1189_ = lean_st_ref_get(v___y_1187_);
v_toCold_1190_ = lean_ctor_get(v___y_1186_, 0);
v_env_1191_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref_n(v_env_1191_, 4);
lean_dec(v___x_1189_);
v_currRecDepth_1192_ = lean_ctor_get(v___y_1186_, 1);
v_ref_1193_ = lean_ctor_get(v___y_1186_, 2);
v_options_1194_ = lean_ctor_get(v_toCold_1190_, 2);
v_maxRecDepth_1195_ = lean_ctor_get(v_toCold_1190_, 3);
v_currNamespace_1196_ = lean_ctor_get(v_toCold_1190_, 4);
v_openDecls_1197_ = lean_ctor_get(v_toCold_1190_, 5);
v_quotContext_1198_ = lean_ctor_get(v_toCold_1190_, 8);
v_currMacroScope_1199_ = lean_ctor_get(v_toCold_1190_, 9);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1200_, 0, v_env_1191_);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1201_, 0, v_env_1191_);
lean_inc_n(v_openDecls_1197_, 2);
lean_inc_n(v_currNamespace_1196_, 3);
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1202_, 0, v_env_1191_);
lean_closure_set(v___f_1202_, 1, v_currNamespace_1196_);
lean_closure_set(v___f_1202_, 2, v_openDecls_1197_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1203_, 0, v_currNamespace_1196_);
lean_inc_ref(v_options_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1204_, 0, v_env_1191_);
lean_closure_set(v___f_1204_, 1, v_options_1194_);
lean_closure_set(v___f_1204_, 2, v_currNamespace_1196_);
lean_closure_set(v___f_1204_, 3, v_openDecls_1197_);
v_methods_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1205_, 0, v___f_1200_);
lean_ctor_set(v_methods_1205_, 1, v___f_1203_);
lean_ctor_set(v_methods_1205_, 2, v___f_1201_);
lean_ctor_set(v_methods_1205_, 3, v___f_1202_);
lean_ctor_set(v_methods_1205_, 4, v___f_1204_);
v___x_1206_ = lean_st_ref_get(v___y_1187_);
v_nextMacroScope_1207_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_nextMacroScope_1207_);
lean_dec(v___x_1206_);
lean_inc(v_ref_1193_);
lean_inc(v_maxRecDepth_1195_);
lean_inc(v_currRecDepth_1192_);
lean_inc(v_currMacroScope_1199_);
lean_inc(v_quotContext_1198_);
v___x_1208_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1208_, 0, v_methods_1205_);
lean_ctor_set(v___x_1208_, 1, v_quotContext_1198_);
lean_ctor_set(v___x_1208_, 2, v_currMacroScope_1199_);
lean_ctor_set(v___x_1208_, 3, v_currRecDepth_1192_);
lean_ctor_set(v___x_1208_, 4, v_maxRecDepth_1195_);
lean_ctor_set(v___x_1208_, 5, v_ref_1193_);
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1210_, 0, v_nextMacroScope_1207_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
v___x_1211_ = lean_apply_2(v_x_1181_, v___x_1208_, v___x_1210_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v_a_1213_; lean_object* v_macroScope_1214_; lean_object* v_traceMsgs_1215_; lean_object* v_expandedMacroDecls_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_a_1212_);
v_a_1213_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1211_, 2);
v_macroScope_1214_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_macroScope_1214_);
v_traceMsgs_1215_ = lean_ctor_get(v_a_1212_, 1);
lean_inc(v_traceMsgs_1215_);
v_expandedMacroDecls_1216_ = lean_ctor_get(v_a_1212_, 2);
lean_inc(v_expandedMacroDecls_1216_);
lean_dec(v_a_1212_);
v___x_1217_ = lean_box(0);
v___x_1218_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1216_, v___x_1217_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v_expandedMacroDecls_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1219_; lean_object* v_env_1220_; lean_object* v_ngen_1221_; lean_object* v_auxDeclNGen_1222_; lean_object* v_traceState_1223_; lean_object* v_cache_1224_; lean_object* v_messages_1225_; lean_object* v_infoState_1226_; lean_object* v_snapshotTasks_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref_known(v___x_1218_, 1);
v___x_1219_ = lean_st_ref_take(v___y_1187_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
v_ngen_1221_ = lean_ctor_get(v___x_1219_, 2);
v_auxDeclNGen_1222_ = lean_ctor_get(v___x_1219_, 3);
v_traceState_1223_ = lean_ctor_get(v___x_1219_, 4);
v_cache_1224_ = lean_ctor_get(v___x_1219_, 5);
v_messages_1225_ = lean_ctor_get(v___x_1219_, 6);
v_infoState_1226_ = lean_ctor_get(v___x_1219_, 7);
v_snapshotTasks_1227_ = lean_ctor_get(v___x_1219_, 8);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v___x_1219_, 1);
lean_dec(v_unused_1254_);
v___x_1229_ = v___x_1219_;
v_isShared_1230_ = v_isSharedCheck_1253_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snapshotTasks_1227_);
lean_inc(v_infoState_1226_);
lean_inc(v_messages_1225_);
lean_inc(v_cache_1224_);
lean_inc(v_traceState_1223_);
lean_inc(v_auxDeclNGen_1222_);
lean_inc(v_ngen_1221_);
lean_inc(v_env_1220_);
lean_dec(v___x_1219_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1253_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_macroScope_1214_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_env_1220_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_macroScope_1214_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_ngen_1221_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_auxDeclNGen_1222_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_traceState_1223_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_cache_1224_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_messages_1225_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_infoState_1226_);
lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_snapshotTasks_1227_);
v___x_1232_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = lean_st_ref_put(v___y_1187_, v___x_1232_);
v___x_1234_ = l_List_reverse___redArg(v_traceMsgs_1215_);
v___x_1235_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1234_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1235_, 0);
lean_dec(v_unused_1243_);
v___x_1237_ = v___x_1235_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_dec(v___x_1235_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v_a_1213_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1213_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec(v_a_1213_);
v_a_1244_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1235_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1235_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_traceMsgs_1215_);
lean_dec(v_macroScope_1214_);
lean_dec(v_a_1213_);
v_a_1255_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1218_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1218_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1211_, 2);
if (lean_obj_tag(v_a_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v_a_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_a_1264_ = lean_ctor_get(v_a_1263_, 0);
lean_inc(v_a_1264_);
v_a_1265_ = lean_ctor_get(v_a_1263_, 1);
lean_inc_ref(v_a_1265_);
lean_dec_ref_known(v_a_1263_, 2);
v___x_1266_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1267_ = lean_string_dec_eq(v_a_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1265_);
v___x_1269_ = l_Lean_MessageData_ofFormat(v___x_1268_);
v___x_1270_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1264_, v___x_1269_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v_a_1264_);
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; 
lean_dec_ref(v_a_1265_);
v___x_1271_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1264_);
return v___x_1271_;
}
}
else
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1285_, size_t v_i_1286_, lean_object* v_bs_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_lt(v_i_1286_, v_sz_1285_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_bs_1287_);
return v___x_1289_;
}
else
{
lean_object* v_v_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_v_1290_ = lean_array_uget(v_bs_1287_, v_i_1286_);
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1290_);
v___x_1292_ = l_Lean_Syntax_isOfKind(v_v_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v_v_1290_);
lean_dec_ref(v_bs_1287_);
v___x_1293_ = lean_box(0);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Lean_Syntax_getArg(v_v_1290_, v___x_1294_);
v___x_1296_ = l_Lean_Syntax_isOfKind(v___x_1295_, v___x_1291_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
lean_dec(v_v_1290_);
lean_dec_ref(v_bs_1287_);
v___x_1297_ = lean_box(0);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; lean_object* v_bs_x27_1299_; lean_object* v___x_1300_; size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1298_ = lean_unsigned_to_nat(3u);
v_bs_x27_1299_ = lean_array_uset(v_bs_1287_, v_i_1286_, v___x_1294_);
v___x_1300_ = l_Lean_Syntax_getArg(v_v_1290_, v___x_1298_);
lean_dec(v_v_1290_);
v___x_1301_ = ((size_t)1ULL);
v___x_1302_ = lean_usize_add(v_i_1286_, v___x_1301_);
v___x_1303_ = lean_array_uset(v_bs_x27_1299_, v_i_1286_, v___x_1300_);
v_i_1286_ = v___x_1302_;
v_bs_1287_ = v___x_1303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_bs_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1308_, v_i_boxed_1309_, v_bs_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t v___x_1323_, size_t v_sz_1324_, size_t v_i_1325_, lean_object* v_bs_1326_){
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
v___x_1330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
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
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_bs_x27_1335_; 
v___x_1333_ = lean_unsigned_to_nat(3u);
v___x_1334_ = lean_unsigned_to_nat(0u);
v_bs_x27_1335_ = lean_array_uset(v_bs_1326_, v_i_1325_, v___x_1334_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1342_ = lean_unsigned_to_nat(1u);
v___x_1343_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1345_ = l_Lean_Syntax_isOfKind(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec_ref(v_bs_x27_1335_);
lean_dec(v_v_1329_);
v___x_1346_ = lean_box(0);
return v___x_1346_;
}
else
{
goto v___jp_1336_;
}
}
else
{
goto v___jp_1336_;
}
v___jp_1336_:
{
lean_object* v___x_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; 
v___x_1337_ = l_Lean_Syntax_getArg(v_v_1329_, v___x_1333_);
lean_dec(v_v_1329_);
v___x_1338_ = ((size_t)1ULL);
v___x_1339_ = lean_usize_add(v_i_1325_, v___x_1338_);
v___x_1340_ = lean_array_uset(v_bs_x27_1335_, v_i_1325_, v___x_1337_);
v_i_1325_ = v___x_1339_;
v_bs_1326_ = v___x_1340_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v___x_1347_, lean_object* v_sz_1348_, lean_object* v_i_1349_, lean_object* v_bs_1350_){
_start:
{
uint8_t v___x_176857__boxed_1351_; size_t v_sz_boxed_1352_; size_t v_i_boxed_1353_; lean_object* v_res_1354_; 
v___x_176857__boxed_1351_ = lean_unbox(v___x_1347_);
v_sz_boxed_1352_ = lean_unbox_usize(v_sz_1348_);
lean_dec(v_sz_1348_);
v_i_boxed_1353_ = lean_unbox_usize(v_i_1349_);
lean_dec(v_i_1349_);
v_res_1354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_176857__boxed_1351_, v_sz_boxed_1352_, v_i_boxed_1353_, v_bs_1350_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1361_, size_t v_i_1362_, lean_object* v_bs_1363_){
_start:
{
uint8_t v___x_1364_; 
v___x_1364_ = lean_usize_dec_lt(v_i_1362_, v_sz_1361_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_bs_1363_);
return v___x_1365_;
}
else
{
lean_object* v_v_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_v_1366_ = lean_array_uget(v_bs_1363_, v_i_1362_);
v___x_1367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1366_);
v___x_1368_ = l_Lean_Syntax_isOfKind(v_v_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v_v_1366_);
lean_dec_ref(v_bs_1363_);
v___x_1369_ = lean_box(0);
return v___x_1369_;
}
else
{
lean_object* v___x_1370_; lean_object* v_bs_x27_1371_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
v_bs_x27_1371_ = lean_array_uset(v_bs_1363_, v_i_1362_, v___x_1370_);
v___x_1378_ = l_Lean_Syntax_getArg(v_v_1366_, v___x_1370_);
lean_dec(v_v_1366_);
v___x_1379_ = l_Lean_Syntax_isNone(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_unsigned_to_nat(2u);
v___x_1381_ = l_Lean_Syntax_matchesNull(v___x_1378_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec_ref(v_bs_x27_1371_);
v___x_1382_ = lean_box(0);
return v___x_1382_;
}
else
{
goto v___jp_1372_;
}
}
else
{
lean_dec(v___x_1378_);
goto v___jp_1372_;
}
v___jp_1372_:
{
lean_object* v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1362_, v___x_1374_);
v___x_1376_ = lean_array_uset(v_bs_x27_1371_, v_i_1362_, v___x_1373_);
v_i_1362_ = v___x_1375_;
v_bs_1363_ = v___x_1376_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_bs_1385_){
_start:
{
size_t v_sz_boxed_1386_; size_t v_i_boxed_1387_; lean_object* v_res_1388_; 
v_sz_boxed_1386_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1386_, v_i_boxed_1387_, v_bs_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1389_, size_t v_i_1390_, lean_object* v_bs_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_usize_dec_lt(v_i_1390_, v_sz_1389_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_bs_1391_);
return v___x_1393_;
}
else
{
lean_object* v_v_1394_; lean_object* v___x_1395_; lean_object* v_bs_x27_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_v_1394_ = lean_array_uget(v_bs_1391_, v_i_1390_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v_bs_x27_1396_ = lean_array_uset(v_bs_1391_, v_i_1390_, v___x_1395_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1390_, v___x_1397_);
v___x_1399_ = lean_array_uset(v_bs_x27_1396_, v_i_1390_, v_v_1394_);
v_i_1390_ = v___x_1398_;
v_bs_1391_ = v___x_1399_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1401_, lean_object* v_i_1402_, lean_object* v_bs_1403_){
_start:
{
size_t v_sz_boxed_1404_; size_t v_i_boxed_1405_; lean_object* v_res_1406_; 
v_sz_boxed_1404_ = lean_unbox_usize(v_sz_1401_);
lean_dec(v_sz_1401_);
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1404_, v_i_boxed_1405_, v_bs_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1408_, v___y_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1412_, v_x_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_x_1413_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1420_, lean_object* v_as_x27_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
if (lean_obj_tag(v_as_x27_1421_) == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_stx_1420_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_b_1422_);
return v___x_1430_;
}
else
{
lean_object* v_head_1431_; lean_object* v_tail_1432_; lean_object* v_value_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_b_1422_);
v_head_1431_ = lean_ctor_get(v_as_x27_1421_, 0);
v_tail_1432_ = lean_ctor_get(v_as_x27_1421_, 1);
v_value_1433_ = lean_ctor_get(v_head_1431_, 1);
v___x_1434_ = lean_box(0);
v___x_1435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1436_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_inc(v_value_1433_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
lean_inc(v_stx_1420_);
v___x_1437_ = lean_apply_8(v_value_1433_, v_stx_1420_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, lean_box(0));
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_stx_1420_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1438_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___x_1434_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1468_; 
v_a_1448_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1450_ = v___x_1437_;
v_isShared_1451_ = v_isSharedCheck_1468_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1437_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1468_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___y_1453_; uint8_t v___x_1466_; 
v___x_1466_ = l_Lean_Exception_isInterrupt(v_a_1448_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; 
lean_inc(v_a_1448_);
v___x_1467_ = l_Lean_Exception_isRuntime(v_a_1448_);
v___y_1453_ = v___x_1467_;
goto v___jp_1452_;
}
else
{
v___y_1453_ = v___x_1466_;
goto v___jp_1452_;
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
if (lean_obj_tag(v_a_1448_) == 0)
{
lean_object* v___x_1455_; 
lean_dec(v_stx_1420_);
if (v_isShared_1451_ == 0)
{
v___x_1455_ = v___x_1450_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1448_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
lean_object* v_id_1457_; uint8_t v___x_1458_; 
v_id_1457_ = lean_ctor_get(v_a_1448_, 0);
v___x_1458_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1436_, v_id_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1460_; 
lean_dec(v_stx_1420_);
if (v_isShared_1451_ == 0)
{
v___x_1460_ = v___x_1450_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1448_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
else
{
lean_dec_ref_known(v_a_1448_, 2);
lean_del_object(v___x_1450_);
v_as_x27_1421_ = v_tail_1432_;
v_b_1422_ = v___x_1435_;
goto _start;
}
}
}
else
{
lean_object* v___x_1464_; 
lean_dec(v_stx_1420_);
if (v_isShared_1451_ == 0)
{
v___x_1464_ = v___x_1450_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1448_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1469_, lean_object* v_as_x27_1470_, lean_object* v_b_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1469_, v_as_x27_1470_, v_b_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v_as_x27_1470_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1482_, lean_object* v_rhs_x3f_1483_, lean_object* v_otherwise_x3f_1484_, lean_object* v_body_x3f_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
uint8_t v___y_1494_; uint8_t v___y_1495_; uint8_t v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v_body_1505_; lean_object* v___y_1526_; lean_object* v_otherwise_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_rhs_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; 
if (lean_obj_tag(v_rhs_x3f_1483_) == 0)
{
lean_object* v___x_1550_; 
v___x_1550_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1539_ = v___x_1550_;
v___y_1540_ = v_a_1486_;
v___y_1541_ = v_a_1487_;
v___y_1542_ = v_a_1488_;
v___y_1543_ = v_a_1489_;
v___y_1544_ = v_a_1490_;
v___y_1545_ = v_a_1491_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1551_; lean_object* v___x_1552_; 
v_val_1551_ = lean_ctor_get(v_rhs_x3f_1483_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v_rhs_x3f_1483_, 1);
v___x_1552_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1551_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v_rhs_1539_ = v_a_1553_;
v___y_1540_ = v_a_1486_;
v___y_1541_ = v_a_1487_;
v___y_1542_ = v_a_1488_;
v___y_1543_ = v_a_1489_;
v___y_1544_ = v_a_1490_;
v___y_1545_ = v_a_1491_;
goto v___jp_1538_;
}
else
{
lean_dec(v_body_x3f_1485_);
lean_dec(v_otherwise_x3f_1484_);
lean_dec_ref(v_reassigned_1482_);
return v___x_1552_;
}
}
v___jp_1493_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1500_, 0, v___y_1497_);
lean_ctor_set(v___x_1500_, 1, v___y_1499_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*2, v___y_1496_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*2 + 1, v___y_1498_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*2 + 2, v___y_1494_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*2 + 3, v___y_1495_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
v___jp_1502_:
{
lean_object* v___x_1506_; lean_object* v_info_1507_; uint8_t v_breaks_1508_; uint8_t v_continues_1509_; uint8_t v_returnsEarly_1510_; lean_object* v_numRegularExits_1511_; uint8_t v_noFallthrough_1512_; lean_object* v_reassigns_1513_; size_t v_sz_1514_; size_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1506_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1505_, v___y_1503_);
v_info_1507_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1504_, v___x_1506_);
v_breaks_1508_ = lean_ctor_get_uint8(v_info_1507_, sizeof(void*)*2);
v_continues_1509_ = lean_ctor_get_uint8(v_info_1507_, sizeof(void*)*2 + 1);
v_returnsEarly_1510_ = lean_ctor_get_uint8(v_info_1507_, sizeof(void*)*2 + 2);
v_numRegularExits_1511_ = lean_ctor_get(v_info_1507_, 0);
lean_inc(v_numRegularExits_1511_);
v_noFallthrough_1512_ = lean_ctor_get_uint8(v_info_1507_, sizeof(void*)*2 + 3);
v_reassigns_1513_ = lean_ctor_get(v_info_1507_, 1);
lean_inc(v_reassigns_1513_);
lean_dec_ref(v_info_1507_);
v_sz_1514_ = lean_array_size(v_reassigned_1482_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1514_, v___x_1515_, v_reassigned_1482_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_array_get_size(v___x_1516_);
v___x_1519_ = lean_nat_dec_lt(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v___x_1516_);
v___y_1494_ = v_returnsEarly_1510_;
v___y_1495_ = v_noFallthrough_1512_;
v___y_1496_ = v_breaks_1508_;
v___y_1497_ = v_numRegularExits_1511_;
v___y_1498_ = v_continues_1509_;
v___y_1499_ = v_reassigns_1513_;
goto v___jp_1493_;
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = lean_nat_dec_le(v___x_1518_, v___x_1518_);
if (v___x_1520_ == 0)
{
if (v___x_1519_ == 0)
{
lean_dec_ref(v___x_1516_);
v___y_1494_ = v_returnsEarly_1510_;
v___y_1495_ = v_noFallthrough_1512_;
v___y_1496_ = v_breaks_1508_;
v___y_1497_ = v_numRegularExits_1511_;
v___y_1498_ = v_continues_1509_;
v___y_1499_ = v_reassigns_1513_;
goto v___jp_1493_;
}
else
{
size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_usize_of_nat(v___x_1518_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1516_, v___x_1515_, v___x_1521_, v_reassigns_1513_);
lean_dec_ref(v___x_1516_);
v___y_1494_ = v_returnsEarly_1510_;
v___y_1495_ = v_noFallthrough_1512_;
v___y_1496_ = v_breaks_1508_;
v___y_1497_ = v_numRegularExits_1511_;
v___y_1498_ = v_continues_1509_;
v___y_1499_ = v___x_1522_;
goto v___jp_1493_;
}
}
else
{
size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_usize_of_nat(v___x_1518_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1516_, v___x_1515_, v___x_1523_, v_reassigns_1513_);
lean_dec_ref(v___x_1516_);
v___y_1494_ = v_returnsEarly_1510_;
v___y_1495_ = v_noFallthrough_1512_;
v___y_1496_ = v_breaks_1508_;
v___y_1497_ = v_numRegularExits_1511_;
v___y_1498_ = v_continues_1509_;
v___y_1499_ = v___x_1524_;
goto v___jp_1493_;
}
}
}
v___jp_1525_:
{
if (lean_obj_tag(v_body_x3f_1485_) == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1503_ = v_otherwise_1527_;
v___y_1504_ = v___y_1526_;
v_body_1505_ = v___x_1534_;
goto v___jp_1502_;
}
else
{
lean_object* v_val_1535_; lean_object* v___x_1536_; 
v_val_1535_ = lean_ctor_get(v_body_x3f_1485_, 0);
lean_inc(v_val_1535_);
lean_dec_ref_known(v_body_x3f_1485_, 1);
v___x_1536_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1535_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___y_1503_ = v_otherwise_1527_;
v___y_1504_ = v___y_1526_;
v_body_1505_ = v_a_1537_;
goto v___jp_1502_;
}
else
{
lean_dec_ref(v_otherwise_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_reassigned_1482_);
return v___x_1536_;
}
}
}
v___jp_1538_:
{
if (lean_obj_tag(v_otherwise_x3f_1484_) == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1526_ = v_rhs_1539_;
v_otherwise_1527_ = v___x_1546_;
v___y_1528_ = v___y_1540_;
v___y_1529_ = v___y_1541_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1545_;
goto v___jp_1525_;
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1548_; 
v_val_1547_ = lean_ctor_get(v_otherwise_x3f_1484_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_otherwise_x3f_1484_, 1);
v___x_1548_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1547_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___y_1526_ = v_rhs_1539_;
v_otherwise_1527_ = v_a_1549_;
v___y_1528_ = v___y_1540_;
v___y_1529_ = v___y_1541_;
v___y_1530_ = v___y_1542_;
v___y_1531_ = v___y_1543_;
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1545_;
goto v___jp_1525_;
}
else
{
lean_dec_ref(v_rhs_1539_);
lean_dec(v_body_x3f_1485_);
lean_dec_ref(v_reassigned_1482_);
return v___x_1548_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12));
v___x_1592_ = l_Lean_stringToMessageData(v___x_1591_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14));
v___x_1595_ = l_Lean_stringToMessageData(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1656_, lean_object* v_decl_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v_reassigns_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1657_);
v___x_1694_ = l_Lean_Syntax_isOfKind(v_decl_1657_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1657_);
v___x_1696_ = l_Lean_Syntax_isOfKind(v_decl_1657_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1697_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1698_ = lean_box(0);
v___x_1699_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1698_, v___x_1696_);
v___x_1700_ = l_Std_Format_defWidth;
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = l_Std_Format_pretty(v___x_1699_, v___x_1700_, v___x_1701_, v___x_1701_);
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1697_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1704_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v_pattern_1707_; lean_object* v___y_1709_; lean_object* v_otherwise_x3f_1710_; lean_object* v_body_x3f_x3f_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v_body_x3f_x3f_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___x_1741_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v_pattern_1707_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1706_);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1780_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1741_);
v___x_1781_ = l_Lean_Syntax_isNone(v___x_1780_);
if (v___x_1781_ == 0)
{
uint8_t v___x_1782_; 
lean_inc(v___x_1780_);
v___x_1782_ = l_Lean_Syntax_matchesNull(v___x_1780_, v___x_1741_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v___x_1780_);
lean_dec(v_pattern_1707_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1784_ = lean_box(0);
v___x_1785_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1784_, v___x_1782_);
v___x_1786_ = l_Std_Format_defWidth;
v___x_1787_ = l_Std_Format_pretty(v___x_1785_, v___x_1786_, v___x_1706_, v___x_1706_);
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1789_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = l_Lean_Syntax_getArg(v___x_1780_, v___x_1706_);
lean_dec(v___x_1780_);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1793_ = l_Lean_Syntax_isOfKind(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v_pattern_1707_);
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1795_ = lean_box(0);
v___x_1796_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1795_, v___x_1793_);
v___x_1797_ = l_Std_Format_defWidth;
v___x_1798_ = l_Std_Format_pretty(v___x_1796_, v___x_1797_, v___x_1706_, v___x_1706_);
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1800_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1801_;
}
else
{
v___y_1743_ = v_a_1658_;
v___y_1744_ = v_a_1659_;
v___y_1745_ = v_a_1660_;
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
goto v___jp_1742_;
}
}
}
else
{
lean_dec(v___x_1780_);
v___y_1743_ = v_a_1658_;
v___y_1744_ = v_a_1659_;
v___y_1745_ = v_a_1660_;
v___y_1746_ = v_a_1661_;
v___y_1747_ = v_a_1662_;
v___y_1748_ = v_a_1663_;
goto v___jp_1742_;
}
v___jp_1708_:
{
if (v_reassignment_1656_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_pattern_1707_);
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1678_ = v___y_1709_;
v___y_1679_ = v_body_x3f_x3f_1711_;
v___y_1680_ = v_otherwise_x3f_1710_;
v_reassigns_1681_ = v___x_1718_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
goto v___jp_1677_;
}
else
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1707_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___y_1678_ = v___y_1709_;
v___y_1679_ = v_body_x3f_x3f_1711_;
v___y_1680_ = v_otherwise_x3f_1710_;
v_reassigns_1681_ = v_a_1720_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1714_;
v___y_1685_ = v___y_1715_;
v___y_1686_ = v___y_1716_;
v___y_1687_ = v___y_1717_;
goto v___jp_1677_;
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_body_x3f_x3f_1711_);
lean_dec(v_otherwise_x3f_1710_);
lean_dec(v___y_1709_);
v_a_1721_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
v___jp_1729_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___y_1731_);
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_body_x3f_x3f_1732_);
v___y_1709_ = v___y_1730_;
v_otherwise_x3f_1710_ = v___x_1739_;
v_body_x3f_x3f_1711_ = v___x_1740_;
v___y_1712_ = v___y_1733_;
v___y_1713_ = v___y_1734_;
v___y_1714_ = v___y_1735_;
v___y_1715_ = v___y_1736_;
v___y_1716_ = v___y_1737_;
v___y_1717_ = v___y_1738_;
goto v___jp_1708_;
}
v___jp_1742_:
{
lean_object* v___x_1749_; lean_object* v_rhs_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___x_1749_ = lean_unsigned_to_nat(3u);
v_rhs_1750_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1749_);
v___x_1751_ = lean_unsigned_to_nat(4u);
v___x_1752_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1751_);
v___x_1753_ = l_Lean_Syntax_isNone(v___x_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
lean_inc(v___x_1752_);
v___x_1754_ = l_Lean_Syntax_matchesNull(v___x_1752_, v___x_1749_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1752_);
lean_dec(v_rhs_1750_);
lean_dec(v_pattern_1707_);
v___x_1755_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1756_ = lean_box(0);
v___x_1757_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1756_, v___x_1754_);
v___x_1758_ = l_Std_Format_defWidth;
v___x_1759_ = l_Std_Format_pretty(v___x_1757_, v___x_1758_, v___x_1706_, v___x_1706_);
v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1755_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1761_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1762_;
}
else
{
lean_object* v___x_1763_; lean_object* v_otherwise_x3f_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1764_ = l_Lean_Syntax_getArg(v___x_1752_, v___x_1741_);
v___x_1765_ = l_Lean_Syntax_getArg(v___x_1752_, v___x_1763_);
lean_dec(v___x_1752_);
v___x_1766_ = l_Lean_Syntax_isNone(v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
lean_inc(v___x_1765_);
v___x_1767_ = l_Lean_Syntax_matchesNull(v___x_1765_, v___x_1741_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___x_1765_);
lean_dec(v_otherwise_x3f_1764_);
lean_dec(v_rhs_1750_);
lean_dec(v_pattern_1707_);
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1769_, v___x_1767_);
v___x_1771_ = l_Std_Format_defWidth;
v___x_1772_ = l_Std_Format_pretty(v___x_1770_, v___x_1771_, v___x_1706_, v___x_1706_);
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1768_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1774_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1775_;
}
else
{
lean_object* v_body_x3f_x3f_1776_; lean_object* v___x_1777_; 
lean_dec(v_decl_1657_);
v_body_x3f_x3f_1776_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1706_);
lean_dec(v___x_1765_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_body_x3f_x3f_1776_);
v___y_1730_ = v_rhs_1750_;
v___y_1731_ = v_otherwise_x3f_1764_;
v_body_x3f_x3f_1732_ = v___x_1777_;
v___y_1733_ = v___y_1743_;
v___y_1734_ = v___y_1744_;
v___y_1735_ = v___y_1745_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
goto v___jp_1729_;
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v___x_1765_);
lean_dec(v_decl_1657_);
v___x_1778_ = lean_box(0);
v___y_1730_ = v_rhs_1750_;
v___y_1731_ = v_otherwise_x3f_1764_;
v_body_x3f_x3f_1732_ = v___x_1778_;
v___y_1733_ = v___y_1743_;
v___y_1734_ = v___y_1744_;
v___y_1735_ = v___y_1745_;
v___y_1736_ = v___y_1746_;
v___y_1737_ = v___y_1747_;
v___y_1738_ = v___y_1748_;
goto v___jp_1729_;
}
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v___x_1752_);
lean_dec(v_decl_1657_);
v___x_1779_ = lean_box(0);
v___y_1709_ = v_rhs_1750_;
v_otherwise_x3f_1710_ = v___x_1779_;
v_body_x3f_x3f_1711_ = v___x_1779_;
v___y_1712_ = v___y_1743_;
v___y_1713_ = v___y_1744_;
v___y_1714_ = v___y_1745_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v___y_1747_;
v___y_1717_ = v___y_1748_;
goto v___jp_1708_;
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v_x_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1802_ = lean_unsigned_to_nat(0u);
v_x_1803_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1802_);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1803_);
v___x_1818_ = l_Lean_Syntax_isOfKind(v_x_1803_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
lean_dec(v_x_1803_);
v___x_1819_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1820_ = lean_box(0);
v___x_1821_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1820_, v___x_1818_);
v___x_1822_ = l_Std_Format_defWidth;
v___x_1823_ = l_Std_Format_pretty(v___x_1821_, v___x_1822_, v___x_1802_, v___x_1802_);
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1819_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1825_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1827_);
v___x_1829_ = l_Lean_Syntax_isNone(v___x_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; 
lean_inc(v___x_1828_);
v___x_1830_ = l_Lean_Syntax_matchesNull(v___x_1828_, v___x_1827_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec(v___x_1828_);
lean_dec(v_x_1803_);
v___x_1831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1832_, v___x_1830_);
v___x_1834_ = l_Std_Format_defWidth;
v___x_1835_ = l_Std_Format_pretty(v___x_1833_, v___x_1834_, v___x_1802_, v___x_1802_);
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1831_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1837_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1802_);
lean_dec(v___x_1828_);
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1841_ = l_Lean_Syntax_isOfKind(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec(v_x_1803_);
v___x_1842_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1843_ = lean_box(0);
v___x_1844_ = l_Lean_Syntax_formatStx(v_decl_1657_, v___x_1843_, v___x_1841_);
v___x_1845_ = l_Std_Format_defWidth;
v___x_1846_ = l_Std_Format_pretty(v___x_1844_, v___x_1845_, v___x_1802_, v___x_1802_);
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1842_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1848_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1849_;
}
else
{
v___y_1805_ = v_a_1658_;
v___y_1806_ = v_a_1659_;
v___y_1807_ = v_a_1660_;
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
goto v___jp_1804_;
}
}
}
else
{
lean_dec(v___x_1828_);
v___y_1805_ = v_a_1658_;
v___y_1806_ = v_a_1659_;
v___y_1807_ = v_a_1660_;
v___y_1808_ = v_a_1661_;
v___y_1809_ = v_a_1662_;
v___y_1810_ = v_a_1663_;
goto v___jp_1804_;
}
}
v___jp_1804_:
{
lean_object* v___x_1811_; lean_object* v_rhs_1812_; 
v___x_1811_ = lean_unsigned_to_nat(3u);
v_rhs_1812_ = l_Lean_Syntax_getArg(v_decl_1657_, v___x_1811_);
lean_dec(v_decl_1657_);
if (v_reassignment_1656_ == 0)
{
lean_object* v___x_1813_; 
lean_dec(v_x_1803_);
v___x_1813_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1666_ = v___y_1806_;
v___y_1667_ = v___y_1805_;
v___y_1668_ = v___y_1810_;
v___y_1669_ = v___y_1807_;
v___y_1670_ = v___y_1808_;
v___y_1671_ = v_rhs_1812_;
v___y_1672_ = v___y_1809_;
v___y_1673_ = v___x_1813_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_mk_empty_array_with_capacity(v___x_1814_);
v___x_1816_ = lean_array_push(v___x_1815_, v_x_1803_);
v___y_1666_ = v___y_1806_;
v___y_1667_ = v___y_1805_;
v___y_1668_ = v___y_1810_;
v___y_1669_ = v___y_1807_;
v___y_1670_ = v___y_1808_;
v___y_1671_ = v_rhs_1812_;
v___y_1672_ = v___y_1809_;
v___y_1673_ = v___x_1816_;
goto v___jp_1665_;
}
}
}
v___jp_1665_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1671_);
v___x_1675_ = lean_box(0);
v___x_1676_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1673_, v___x_1674_, v___x_1675_, v___x_1675_, v___y_1667_, v___y_1666_, v___y_1669_, v___y_1670_, v___y_1672_, v___y_1668_);
return v___x_1676_;
}
v___jp_1677_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___y_1678_);
if (lean_obj_tag(v___y_1679_) == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_box(0);
v___x_1690_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1681_, v___x_1688_, v___y_1680_, v___x_1689_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1692_; 
v_val_1691_ = lean_ctor_get(v___y_1679_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___y_1679_, 1);
v___x_1692_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1681_, v___x_1688_, v___y_1680_, v_val_1691_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1975_, size_t v_sz_1976_, size_t v_i_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_b_1978_);
return v___x_1987_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1989_; 
v_a_1988_ = lean_array_uget_borrowed(v_as_1975_, v_i_1977_);
lean_inc(v_a_1988_);
v___x_1989_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1988_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_1990_, v_b_1978_);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1977_, v___x_1992_);
v_i_1977_ = v___x_1993_;
v_b_1978_ = v___x_1991_;
goto _start;
}
else
{
lean_dec_ref(v_b_1978_);
return v___x_1989_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2009_ = l_Lean_stringToMessageData(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2024_, lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_a_2037_; uint8_t v___x_2041_; 
v___x_2041_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2042_, 0, v_b_2028_);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v_a_2044_; uint8_t v___x_2045_; 
v___x_2043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2044_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
lean_inc(v_a_2044_);
v___x_2045_ = l_Lean_Syntax_isOfKind(v_a_2044_, v___x_2043_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_dec_ref_known(v___x_2046_, 1);
v_a_2037_ = v_b_2028_;
goto v___jp_2036_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_b_2028_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v___x_2055_; lean_object* v___y_2057_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2055_ = lean_unsigned_to_nat(3u);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = l_Lean_Syntax_getArg(v_a_2044_, v___x_2074_);
v___x_2076_ = l_Lean_Syntax_getArgs(v___x_2075_);
lean_dec(v___x_2075_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2079_ = lean_array_get_size(v___x_2076_);
v___x_2080_ = lean_nat_dec_lt(v___x_2077_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v___x_2076_);
v___y_2057_ = v___x_2078_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; lean_object* v___x_2085_; lean_object* v_snd_2086_; 
v___x_2081_ = lean_box(v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2078_);
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = lean_usize_of_nat(v___x_2079_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2045_, v___x_2024_, v___x_2076_, v___x_2083_, v___x_2084_, v___x_2082_);
lean_dec_ref(v___x_2076_);
v_snd_2086_ = lean_ctor_get(v___x_2085_, 1);
lean_inc(v_snd_2086_);
lean_dec_ref(v___x_2085_);
v___y_2057_ = v_snd_2086_;
goto v___jp_2056_;
}
v___jp_2056_:
{
size_t v_sz_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v_sz_2058_ = lean_array_size(v___y_2057_);
v___x_2059_ = ((size_t)0ULL);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2058_, v___x_2059_, v___y_2057_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_dec_ref_known(v___x_2061_, 1);
v_a_2037_ = v_b_2028_;
goto v___jp_2036_;
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_b_2028_);
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec_ref_known(v___x_2060_, 1);
v___x_2070_ = l_Lean_Syntax_getArg(v_a_2044_, v___x_2055_);
v___x_2071_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2070_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2028_, v_a_2072_);
v_a_2037_ = v___x_2073_;
goto v___jp_2036_;
}
else
{
lean_dec_ref(v_b_2028_);
return v___x_2071_;
}
}
}
}
}
v___jp_2036_:
{
size_t v___x_2038_; size_t v___x_2039_; 
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2027_, v___x_2038_);
v_i_2027_ = v___x_2039_;
v_b_2028_ = v_a_2037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2087_, size_t v_sz_2088_, size_t v_i_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_a_2099_; uint8_t v___x_2103_; 
v___x_2103_ = lean_usize_dec_lt(v_i_2089_, v_sz_2088_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_b_2090_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v_a_2106_ = lean_array_uget_borrowed(v_as_2087_, v_i_2089_);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2106_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v_a_2106_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2106_);
v___x_2122_ = l_Lean_Syntax_isOfKind(v_a_2106_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2124_ = lean_box(0);
lean_inc(v_a_2106_);
v___x_2125_ = l_Lean_Syntax_formatStx(v_a_2106_, v___x_2124_, v___x_2122_);
v___x_2126_ = l_Std_Format_defWidth;
v___x_2127_ = l_Std_Format_pretty(v___x_2125_, v___x_2126_, v___x_2105_, v___x_2105_);
v___x_2128_ = l_Lean_stringToMessageData(v___x_2127_);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2123_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2129_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_dec_ref_known(v___x_2130_, 1);
v_a_2099_ = v_b_2090_;
goto v___jp_2098_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v_b_2090_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = lean_unsigned_to_nat(1u);
v___x_2140_ = l_Lean_Syntax_getArg(v_a_2106_, v___x_2139_);
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2140_);
v___x_2142_ = l_Lean_Syntax_isOfKind(v___x_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec(v___x_2140_);
v___x_2143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2144_ = lean_box(0);
lean_inc(v_a_2106_);
v___x_2145_ = l_Lean_Syntax_formatStx(v_a_2106_, v___x_2144_, v___x_2142_);
v___x_2146_ = l_Std_Format_defWidth;
v___x_2147_ = l_Std_Format_pretty(v___x_2145_, v___x_2146_, v___x_2105_, v___x_2105_);
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2143_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2149_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
v_a_2099_ = v_b_2090_;
goto v___jp_2098_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_b_2090_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; size_t v_sz_2161_; size_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2159_ = l_Lean_Syntax_getArg(v___x_2140_, v___x_2105_);
lean_dec(v___x_2140_);
v___x_2160_ = l_Lean_Syntax_getArgs(v___x_2159_);
lean_dec(v___x_2159_);
v_sz_2161_ = lean_array_size(v___x_2160_);
v___x_2162_ = ((size_t)0ULL);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2120_, v___x_2160_, v_sz_2161_, v___x_2162_, v_b_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec_ref(v___x_2160_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_a_2099_ = v_a_2164_;
goto v___jp_2098_;
}
else
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_unsigned_to_nat(2u);
v___x_2166_ = l_Lean_Syntax_getArg(v_a_2106_, v___x_2165_);
v___x_2167_ = l_Lean_Syntax_isNone(v___x_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Lean_Syntax_matchesNull(v___x_2166_, v___x_2165_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2170_ = lean_box(0);
lean_inc(v_a_2106_);
v___x_2171_ = l_Lean_Syntax_formatStx(v_a_2106_, v___x_2170_, v___x_2168_);
v___x_2172_ = l_Std_Format_defWidth;
v___x_2173_ = l_Std_Format_pretty(v___x_2171_, v___x_2172_, v___x_2105_, v___x_2105_);
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2169_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2175_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_dec_ref_known(v___x_2176_, 1);
v_a_2099_ = v_b_2090_;
goto v___jp_2098_;
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref(v_b_2090_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
v___y_2108_ = v___y_2091_;
v___y_2109_ = v___y_2092_;
v___y_2110_ = v___y_2093_;
v___y_2111_ = v___y_2094_;
v___y_2112_ = v___y_2095_;
v___y_2113_ = v___y_2096_;
goto v___jp_2107_;
}
}
else
{
lean_dec(v___x_2166_);
v___y_2108_ = v___y_2091_;
v___y_2109_ = v___y_2092_;
v___y_2110_ = v___y_2093_;
v___y_2111_ = v___y_2094_;
v___y_2112_ = v___y_2095_;
v___y_2113_ = v___y_2096_;
goto v___jp_2107_;
}
}
v___jp_2107_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_unsigned_to_nat(4u);
v___x_2115_ = l_Lean_Syntax_getArg(v_a_2106_, v___x_2114_);
v___x_2116_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2115_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2117_, v_b_2090_);
v_a_2099_ = v___x_2118_;
goto v___jp_2098_;
}
else
{
lean_dec_ref(v_b_2090_);
return v___x_2116_;
}
}
}
v___jp_2098_:
{
size_t v___x_2100_; size_t v___x_2101_; 
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2089_, v___x_2100_);
v_i_2089_ = v___x_2101_;
v_b_2090_ = v_a_2099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2185_) == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
else
{
lean_object* v_val_2195_; lean_object* v___x_2196_; 
v_val_2195_ = lean_ctor_get(v_stx_x3f_2185_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v_stx_x3f_2185_, 1);
v___x_2196_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2195_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
return v___x_2196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2215_, lean_object* v_as_2216_, size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_b_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_a_2228_; uint8_t v___x_2232_; 
v___x_2232_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_b_2219_);
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; lean_object* v_a_2235_; uint8_t v___x_2236_; 
v___x_2234_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2235_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
lean_inc(v_a_2235_);
v___x_2236_ = l_Lean_Syntax_isOfKind(v_a_2235_, v___x_2234_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
v_a_2228_ = v_b_2219_;
goto v___jp_2227_;
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_b_2219_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v___x_2246_; lean_object* v___y_2248_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2246_ = lean_unsigned_to_nat(3u);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = l_Lean_Syntax_getArg(v_a_2235_, v___x_2265_);
v___x_2267_ = l_Lean_Syntax_getArgs(v___x_2266_);
lean_dec(v___x_2266_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2270_ = lean_array_get_size(v___x_2267_);
v___x_2271_ = lean_nat_dec_lt(v___x_2268_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec_ref(v___x_2267_);
v___y_2248_ = v___x_2269_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; lean_object* v_snd_2277_; 
v___x_2272_ = lean_box(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___x_2269_);
v___x_2274_ = ((size_t)0ULL);
v___x_2275_ = lean_usize_of_nat(v___x_2270_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2236_, v___x_2215_, v___x_2267_, v___x_2274_, v___x_2275_, v___x_2273_);
lean_dec_ref(v___x_2267_);
v_snd_2277_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_snd_2277_);
lean_dec_ref(v___x_2276_);
v___y_2248_ = v_snd_2277_;
goto v___jp_2247_;
}
v___jp_2247_:
{
size_t v_sz_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v_sz_2249_ = lean_array_size(v___y_2248_);
v___x_2250_ = ((size_t)0ULL);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2249_, v___x_2250_, v___y_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_dec_ref_known(v___x_2252_, 1);
v_a_2228_ = v_b_2219_;
goto v___jp_2227_;
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v_b_2219_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec_ref_known(v___x_2251_, 1);
v___x_2261_ = l_Lean_Syntax_getArg(v_a_2235_, v___x_2246_);
v___x_2262_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2261_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2219_, v_a_2263_);
v_a_2228_ = v___x_2264_;
goto v___jp_2227_;
}
else
{
lean_dec_ref(v_b_2219_);
return v___x_2262_;
}
}
}
}
}
v___jp_2227_:
{
size_t v___x_2229_; size_t v___x_2230_; 
v___x_2229_ = ((size_t)1ULL);
v___x_2230_ = lean_usize_add(v_i_2218_, v___x_2229_);
v_i_2218_ = v___x_2230_;
v_b_2219_ = v_a_2228_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2326_ = l_Lean_NameSet_empty;
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = 0;
v___x_2329_ = 1;
v___x_2330_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2330_, 0, v___x_2327_);
lean_ctor_set(v___x_2330_, 1, v___x_2326_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*2, v___x_2329_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*2 + 1, v___x_2328_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*2 + 2, v___x_2328_);
lean_ctor_set_uint8(v___x_2330_, sizeof(void*)*2 + 3, v___x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___y_2340_; lean_object* v_bodyInfo_2341_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2385_; lean_object* v_bodyInfo_2386_; lean_object* v___x_2389_; lean_object* v_env_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2389_ = lean_st_ref_get(v_a_2337_);
v_env_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_ref(v_env_2390_);
lean_dec(v___x_2389_);
lean_inc(v_stx_2331_);
v___x_2391_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2391_, 0, v_env_2390_);
lean_closure_set(v___x_2391_, 1, v_stx_2331_);
v___x_2392_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2391_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_5103_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_5103_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_5103_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
if (lean_obj_tag(v_a_2393_) == 1)
{
lean_object* v_val_2405_; lean_object* v_snd_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_del_object(v___x_2395_);
lean_dec(v_stx_2331_);
v_val_2405_ = lean_ctor_get(v_a_2393_, 0);
lean_inc(v_val_2405_);
lean_dec_ref_known(v_a_2393_, 1);
v_snd_2406_ = lean_ctor_get(v_val_2405_, 1);
lean_inc(v_snd_2406_);
lean_dec(v_val_2405_);
v___x_2407_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2407_, 0, lean_box(0));
lean_closure_set(v___x_2407_, 1, v_snd_2406_);
v___x_2408_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2407_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v_stx_2331_ = v_a_2409_;
goto _start;
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_a_2411_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2408_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2408_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v___x_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; 
lean_dec(v_a_2393_);
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
lean_inc(v_stx_2331_);
v___x_2420_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2419_);
v___x_2421_ = 1;
if (v___x_2420_ == 0)
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3));
lean_inc(v_stx_2331_);
v___x_2423_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5));
lean_inc(v_stx_2331_);
v___x_2425_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7));
lean_inc(v_stx_2331_);
v___x_2427_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; 
v___x_2428_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9));
lean_inc(v_stx_2331_);
v___x_2429_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2331_);
v___x_2545_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2331_);
v___x_2598_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; uint8_t v___x_2600_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; 
v___x_2599_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2331_);
v___x_2600_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___y_2661_; lean_object* v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v___y_2665_; lean_object* v___y_2666_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; 
lean_del_object(v___x_2395_);
v___x_2658_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2331_);
v___x_2659_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2331_);
v___x_2728_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2331_);
v___x_2730_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2331_);
v___x_2732_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2331_);
v___x_2734_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2331_);
v___x_2736_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2331_);
v___x_2738_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2331_);
v___x_2740_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; uint8_t v___x_2742_; lean_object* v___y_2744_; lean_object* v___y_2745_; uint8_t v___y_2746_; uint8_t v___y_2747_; 
v___x_2741_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2331_);
v___x_2742_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2331_);
v___x_2751_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(v_stx_2331_);
v___x_2753_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2331_);
v___x_2755_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2331_);
v___x_2757_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2331_);
v___x_2759_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2331_);
v___x_2761_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2331_);
v___x_2763_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2331_);
v___x_2765_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2331_);
v___x_2767_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v_stx_2331_);
v___x_2769_ = l_Lean_Syntax_isOfKind(v_stx_2331_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_env_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2770_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2771_ = lean_st_ref_get(v_a_2337_);
v_env_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_env_2772_);
lean_dec(v___x_2771_);
v___x_2773_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2774_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2773_, v_env_2772_, v___x_2770_);
v___x_2775_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2776_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2774_, v___x_2775_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_2774_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2807_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2807_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2807_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_fst_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2805_; 
v_fst_2781_ = lean_ctor_get(v_a_2777_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_a_2777_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v_a_2777_, 1);
lean_dec(v_unused_2806_);
v___x_2783_ = v_a_2777_;
v_isShared_2784_ = v_isSharedCheck_2805_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_fst_2781_);
lean_dec(v_a_2777_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2805_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
if (lean_obj_tag(v_fst_2781_) == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_del_object(v___x_2779_);
v___x_2785_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2786_ = l_Lean_MessageData_ofName(v___x_2770_);
lean_inc_ref(v___x_2786_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set_tag(v___x_2783_, 7);
lean_ctor_set(v___x_2783_, 1, v___x_2786_);
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2788_ = v___x_2783_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2789_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2792_ = l_Lean_indentD(v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2786_);
v___x_2797_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2798_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2799_;
}
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; 
lean_del_object(v___x_2783_);
lean_dec(v___x_2770_);
lean_dec(v_stx_2331_);
v_val_2801_ = lean_ctor_get(v_fst_2781_, 0);
lean_inc(v_val_2801_);
lean_dec_ref_known(v_fst_2781_, 1);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v_val_2801_);
v___x_2803_ = v___x_2779_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_val_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v___x_2770_);
lean_dec(v_stx_2331_);
v_a_2808_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2776_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2776_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___y_2820_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_unsigned_to_nat(5u);
v___x_2818_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2817_);
v___x_2829_ = lean_unsigned_to_nat(6u);
v___x_2830_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2829_);
lean_dec(v_stx_2331_);
v___x_2831_ = l_Lean_Syntax_getOptional_x3f(v___x_2830_);
lean_dec(v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_box(0);
v___y_2820_ = v___x_2832_;
goto v___jp_2819_;
}
else
{
lean_object* v_val_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
v_val_2833_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2831_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_val_2833_);
lean_dec(v___x_2831_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_val_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
v___y_2820_ = v___x_2838_;
goto v___jp_2819_;
}
}
}
v___jp_2819_:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2818_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2821_) == 0)
{
if (lean_obj_tag(v___y_2820_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = l_Lean_NameSet_empty;
v___x_2824_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2824_, 0, v___x_2816_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2, v___x_2767_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 1, v___x_2767_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 2, v___x_2767_);
lean_ctor_set_uint8(v___x_2824_, sizeof(void*)*2 + 3, v___x_2767_);
v___y_2340_ = v_a_2822_;
v_bodyInfo_2341_ = v___x_2824_;
goto v___jp_2339_;
}
else
{
lean_object* v_a_2825_; lean_object* v_val_2826_; lean_object* v___x_2827_; 
v_a_2825_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2821_, 1);
v_val_2826_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v___y_2820_, 1);
v___x_2827_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2826_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___y_2340_ = v_a_2825_;
v_bodyInfo_2341_ = v_a_2828_;
goto v___jp_2339_;
}
else
{
lean_dec(v_a_2825_);
return v___x_2827_;
}
}
}
else
{
lean_dec(v___y_2820_);
return v___x_2821_;
}
}
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___y_2845_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_unsigned_to_nat(5u);
v___x_2843_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2842_);
v___x_2854_ = lean_unsigned_to_nat(6u);
v___x_2855_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2854_);
lean_dec(v_stx_2331_);
v___x_2856_ = l_Lean_Syntax_getOptional_x3f(v___x_2855_);
lean_dec(v___x_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_box(0);
v___y_2845_ = v___x_2857_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_val_2858_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2856_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v___x_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_val_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v___y_2845_ = v___x_2863_;
goto v___jp_2844_;
}
}
}
v___jp_2844_:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2843_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2846_) == 0)
{
if (lean_obj_tag(v___y_2845_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_NameSet_empty;
v___x_2849_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2849_, 0, v___x_2841_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*2, v___x_2765_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*2 + 1, v___x_2765_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*2 + 2, v___x_2765_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*2 + 3, v___x_2765_);
v___y_2385_ = v_a_2847_;
v_bodyInfo_2386_ = v___x_2849_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2850_; lean_object* v_val_2851_; lean_object* v___x_2852_; 
v_a_2850_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2846_, 1);
v_val_2851_ = lean_ctor_get(v___y_2845_, 0);
lean_inc(v_val_2851_);
lean_dec_ref_known(v___y_2845_, 1);
v___x_2852_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2851_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___y_2385_ = v_a_2850_;
v_bodyInfo_2386_ = v_a_2853_;
goto v___jp_2384_;
}
else
{
lean_dec(v_a_2850_);
return v___x_2852_;
}
}
}
else
{
lean_dec(v___y_2845_);
return v___x_2846_;
}
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_3081_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2867_);
v___x_3082_ = l_Lean_Syntax_isNone(v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = lean_unsigned_to_nat(5u);
v___x_3084_ = l_Lean_Syntax_matchesNull(v___x_3081_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v_env_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3085_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3086_ = lean_st_ref_get(v_a_2337_);
v_env_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_env_3087_);
lean_dec(v___x_3086_);
v___x_3088_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3089_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3088_, v_env_3087_, v___x_3085_);
v___x_3090_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3091_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3089_, v___x_3090_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3089_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3122_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3122_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3122_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_fst_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3120_; 
v_fst_3096_ = lean_ctor_get(v_a_3092_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_a_3092_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_a_3092_, 1);
lean_dec(v_unused_3121_);
v___x_3098_ = v_a_3092_;
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_fst_3096_);
lean_dec(v_a_3092_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
if (lean_obj_tag(v_fst_3096_) == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_del_object(v___x_3094_);
v___x_3100_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3101_ = l_Lean_MessageData_ofName(v___x_3085_);
lean_inc_ref(v___x_3101_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 7);
lean_ctor_set(v___x_3098_, 1, v___x_3101_);
lean_ctor_set(v___x_3098_, 0, v___x_3100_);
v___x_3103_ = v___x_3098_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3104_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3107_ = l_Lean_indentD(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3105_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v___x_3101_);
v___x_3112_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3113_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3114_;
}
}
else
{
lean_object* v_val_3116_; lean_object* v___x_3118_; 
lean_del_object(v___x_3098_);
lean_dec(v___x_3085_);
lean_dec(v_stx_2331_);
v_val_3116_ = lean_ctor_get(v_fst_3096_, 0);
lean_inc(v_val_3116_);
lean_dec_ref_known(v_fst_3096_, 1);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_val_3116_);
v___x_3118_ = v___x_3094_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_val_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v___x_3085_);
lean_dec(v_stx_2331_);
v_a_3123_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3091_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3091_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
v___y_2869_ = v_a_2332_;
v___y_2870_ = v_a_2333_;
v___y_2871_ = v_a_2334_;
v___y_2872_ = v_a_2335_;
v___y_2873_ = v_a_2336_;
v___y_2874_ = v_a_2337_;
goto v___jp_2868_;
}
}
else
{
lean_dec(v___x_3081_);
v___y_2869_ = v_a_2332_;
v___y_2870_ = v_a_2333_;
v___y_2871_ = v_a_2334_;
v___y_2872_ = v_a_2335_;
v___y_2873_ = v_a_2336_;
v___y_2874_ = v_a_2337_;
goto v___jp_2868_;
}
v___jp_2868_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2875_ = lean_unsigned_to_nat(4u);
v___x_2876_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2875_);
v___x_2877_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2876_);
v___x_2878_ = l_Lean_Syntax_isOfKind(v___x_2876_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_env_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_dec(v___x_2876_);
lean_inc_n(v_stx_2331_, 2);
v___x_2879_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2880_ = lean_st_ref_get(v___y_2874_);
v_env_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc_ref(v_env_2881_);
lean_dec(v___x_2880_);
v___x_2882_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2883_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2882_, v_env_2881_, v___x_2879_);
v___x_2884_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2885_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2883_, v___x_2884_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___x_2883_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2916_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v_fst_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2914_; 
v_fst_2890_ = lean_ctor_get(v_a_2886_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_a_2886_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v_a_2886_, 1);
lean_dec(v_unused_2915_);
v___x_2892_ = v_a_2886_;
v_isShared_2893_ = v_isSharedCheck_2914_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_fst_2890_);
lean_dec(v_a_2886_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2914_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
if (lean_obj_tag(v_fst_2890_) == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
lean_del_object(v___x_2888_);
v___x_2894_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2895_ = l_Lean_MessageData_ofName(v___x_2879_);
lean_inc_ref(v___x_2895_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 7);
lean_ctor_set(v___x_2892_, 1, v___x_2895_);
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2898_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2901_ = l_Lean_indentD(v___x_2900_);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2899_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2902_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
lean_ctor_set(v___x_2905_, 1, v___x_2895_);
v___x_2906_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2907_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2908_;
}
}
else
{
lean_object* v_val_2910_; lean_object* v___x_2912_; 
lean_del_object(v___x_2892_);
lean_dec(v___x_2879_);
lean_dec(v_stx_2331_);
v_val_2910_ = lean_ctor_get(v_fst_2890_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_fst_2890_, 1);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v_val_2910_);
v___x_2912_ = v___x_2888_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_val_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v___x_2879_);
lean_dec(v_stx_2331_);
v_a_2917_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2885_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2885_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; size_t v_sz_2927_; size_t v___x_2928_; lean_object* v___x_2929_; 
v___x_2925_ = l_Lean_Syntax_getArg(v___x_2876_, v___x_2866_);
v___x_2926_ = l_Lean_Syntax_getArgs(v___x_2925_);
lean_dec(v___x_2925_);
v_sz_2927_ = lean_array_size(v___x_2926_);
v___x_2928_ = ((size_t)0ULL);
v___x_2929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_2763_, v_sz_2927_, v___x_2928_, v___x_2926_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v___x_2876_);
lean_inc_n(v_stx_2331_, 2);
v___x_2930_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2931_ = lean_st_ref_get(v___y_2874_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2931_);
v___x_2933_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2934_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2933_, v_env_2932_, v___x_2930_);
v___x_2935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2936_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2934_, v___x_2935_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___x_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2967_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2967_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2967_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_fst_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2965_; 
v_fst_2941_ = lean_ctor_get(v_a_2937_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_a_2937_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; 
v_unused_2966_ = lean_ctor_get(v_a_2937_, 1);
lean_dec(v_unused_2966_);
v___x_2943_ = v_a_2937_;
v_isShared_2944_ = v_isSharedCheck_2965_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_fst_2941_);
lean_dec(v_a_2937_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2965_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
if (lean_obj_tag(v_fst_2941_) == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
lean_del_object(v___x_2939_);
v___x_2945_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2946_ = l_Lean_MessageData_ofName(v___x_2930_);
lean_inc_ref(v___x_2946_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 7);
lean_ctor_set(v___x_2943_, 1, v___x_2946_);
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2946_);
v___x_2948_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2949_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2952_ = l_Lean_indentD(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v___x_2946_);
v___x_2957_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2958_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2959_;
}
}
else
{
lean_object* v_val_2961_; lean_object* v___x_2963_; 
lean_del_object(v___x_2943_);
lean_dec(v___x_2930_);
lean_dec(v_stx_2331_);
v_val_2961_ = lean_ctor_get(v_fst_2941_, 0);
lean_inc(v_val_2961_);
lean_dec_ref_known(v_fst_2941_, 1);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v_val_2961_);
v___x_2963_ = v___x_2939_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_val_2961_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v___x_2930_);
lean_dec(v_stx_2331_);
v_a_2968_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2936_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2936_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v_val_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_val_2976_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_val_2976_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2977_ = l_Lean_Syntax_getArg(v___x_2876_, v___x_2867_);
lean_dec(v___x_2876_);
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
lean_inc(v___x_2977_);
v___x_2979_ = l_Lean_Syntax_isOfKind(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_env_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec(v___x_2977_);
lean_dec(v_val_2976_);
lean_inc_n(v_stx_2331_, 2);
v___x_2980_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2981_ = lean_st_ref_get(v___y_2874_);
v_env_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref(v_env_2982_);
lean_dec(v___x_2981_);
v___x_2983_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2984_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2983_, v_env_2982_, v___x_2980_);
v___x_2985_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2986_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2984_, v___x_2985_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___x_2984_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3017_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3017_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3017_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_fst_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3015_; 
v_fst_2991_ = lean_ctor_get(v_a_2987_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_a_2987_, 1);
lean_dec(v_unused_3016_);
v___x_2993_ = v_a_2987_;
v_isShared_2994_ = v_isSharedCheck_3015_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_fst_2991_);
lean_dec(v_a_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3015_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
if (lean_obj_tag(v_fst_2991_) == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
lean_del_object(v___x_2989_);
v___x_2995_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2996_ = l_Lean_MessageData_ofName(v___x_2980_);
lean_inc_ref(v___x_2996_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set_tag(v___x_2993_, 7);
lean_ctor_set(v___x_2993_, 1, v___x_2996_);
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2998_ = v___x_2993_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3010_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_2999_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3002_ = l_Lean_indentD(v___x_3001_);
v___x_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3000_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set(v___x_3006_, 1, v___x_2996_);
v___x_3007_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3008_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_3009_;
}
}
else
{
lean_object* v_val_3011_; lean_object* v___x_3013_; 
lean_del_object(v___x_2993_);
lean_dec(v___x_2980_);
lean_dec(v_stx_2331_);
v_val_3011_ = lean_ctor_get(v_fst_2991_, 0);
lean_inc(v_val_3011_);
lean_dec_ref_known(v_fst_2991_, 1);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v_val_3011_);
v___x_3013_ = v___x_2989_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_val_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v___x_2980_);
lean_dec(v_stx_2331_);
v_a_3018_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_2986_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_2986_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3026_ = l_Lean_Syntax_getArg(v___x_2977_, v___x_2867_);
v___x_3027_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
v___x_3028_ = l_Lean_Syntax_isOfKind(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_env_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec(v___x_2977_);
lean_dec(v_val_2976_);
lean_inc_n(v_stx_2331_, 2);
v___x_3029_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3030_ = lean_st_ref_get(v___y_2874_);
v_env_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc_ref(v_env_3031_);
lean_dec(v___x_3030_);
v___x_3032_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3033_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3032_, v_env_3031_, v___x_3029_);
v___x_3034_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3035_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3033_, v___x_3034_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___x_3033_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3066_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3066_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3066_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_fst_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3064_; 
v_fst_3040_ = lean_ctor_get(v_a_3036_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v_a_3036_, 1);
lean_dec(v_unused_3065_);
v___x_3042_ = v_a_3036_;
v_isShared_3043_ = v_isSharedCheck_3064_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_fst_3040_);
lean_dec(v_a_3036_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3064_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
if (lean_obj_tag(v_fst_3040_) == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_del_object(v___x_3038_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3045_ = l_Lean_MessageData_ofName(v___x_3029_);
lean_inc_ref(v___x_3045_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set_tag(v___x_3042_, 7);
lean_ctor_set(v___x_3042_, 1, v___x_3045_);
lean_ctor_set(v___x_3042_, 0, v___x_3044_);
v___x_3047_ = v___x_3042_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3048_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3051_ = l_Lean_indentD(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3049_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___x_3045_);
v___x_3056_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3057_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_3058_;
}
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3062_; 
lean_del_object(v___x_3042_);
lean_dec(v___x_3029_);
lean_dec(v_stx_2331_);
v_val_3060_ = lean_ctor_get(v_fst_3040_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v_fst_3040_, 1);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_val_3060_);
v___x_3062_ = v___x_3038_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_val_3060_);
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
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v___x_3029_);
lean_dec(v_stx_2331_);
v_a_3067_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3035_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3035_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec(v_stx_2331_);
v___x_3075_ = lean_unsigned_to_nat(3u);
v___x_3076_ = l_Lean_Syntax_getArg(v___x_2977_, v___x_3075_);
lean_dec(v___x_2977_);
v___x_3077_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3076_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; size_t v_sz_3079_; lean_object* v___x_3080_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v_sz_3079_ = lean_array_size(v_val_2976_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2976_, v_sz_3079_, v___x_2928_, v_a_3078_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v_val_2976_);
return v___x_3080_;
}
else
{
lean_dec(v_val_2976_);
return v___x_3077_;
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
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v_stx_2331_);
v___x_3131_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v_stx_2331_);
v___x_3133_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
return v___x_3134_;
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_stx_2331_);
v___x_3135_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec(v_stx_2331_);
v___x_3137_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_dec(v_stx_2331_);
v___x_3139_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
return v___x_3140_;
}
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; size_t v_sz_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3141_ = lean_unsigned_to_nat(2u);
v___x_3142_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3141_);
v___x_3143_ = l_Lean_Syntax_getArgs(v___x_3142_);
lean_dec(v___x_3142_);
v_sz_3144_ = lean_array_size(v___x_3143_);
v___x_3145_ = ((size_t)0ULL);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3144_, v___x_3145_, v___x_3143_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v_env_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3147_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3148_ = lean_st_ref_get(v_a_2337_);
v_env_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc_ref(v_env_3149_);
lean_dec(v___x_3148_);
v___x_3150_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3151_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3150_, v_env_3149_, v___x_3147_);
v___x_3152_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3153_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3151_, v___x_3152_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3151_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3184_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3184_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_fst_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3182_; 
v_fst_3158_ = lean_ctor_get(v_a_3154_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_a_3154_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_a_3154_, 1);
lean_dec(v_unused_3183_);
v___x_3160_ = v_a_3154_;
v_isShared_3161_ = v_isSharedCheck_3182_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_fst_3158_);
lean_dec(v_a_3154_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3182_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
if (lean_obj_tag(v_fst_3158_) == 0)
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
lean_del_object(v___x_3156_);
v___x_3162_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3163_ = l_Lean_MessageData_ofName(v___x_3147_);
lean_inc_ref(v___x_3163_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 7);
lean_ctor_set(v___x_3160_, 1, v___x_3163_);
lean_ctor_set(v___x_3160_, 0, v___x_3162_);
v___x_3165_ = v___x_3160_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3166_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3169_ = l_Lean_indentD(v___x_3168_);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3167_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3163_);
v___x_3174_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3175_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3176_;
}
}
else
{
lean_object* v_val_3178_; lean_object* v___x_3180_; 
lean_del_object(v___x_3160_);
lean_dec(v___x_3147_);
lean_dec(v_stx_2331_);
v_val_3178_ = lean_ctor_get(v_fst_3158_, 0);
lean_inc(v_val_3178_);
lean_dec_ref_known(v_fst_3158_, 1);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v_val_3178_);
v___x_3180_ = v___x_3156_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_val_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v___x_3147_);
lean_dec(v_stx_2331_);
v_a_3185_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3153_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3153_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
else
{
lean_object* v_val_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3327_; 
v_val_3193_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3195_ = v___x_3146_;
v_isShared_3196_ = v_isSharedCheck_3327_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_val_3193_);
lean_dec(v___x_3146_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3327_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_finSeq_x3f_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3197_ = lean_unsigned_to_nat(1u);
v___x_3198_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3197_);
v___x_3222_ = lean_unsigned_to_nat(3u);
v___x_3223_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3222_);
v___x_3224_ = l_Lean_Syntax_isNone(v___x_3223_);
if (v___x_3224_ == 0)
{
uint8_t v___x_3225_; 
lean_inc(v___x_3223_);
v___x_3225_ = l_Lean_Syntax_matchesNull(v___x_3223_, v___x_3197_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_env_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v___x_3223_);
lean_dec(v___x_3198_);
lean_del_object(v___x_3195_);
lean_dec(v_val_3193_);
lean_inc_n(v_stx_2331_, 2);
v___x_3226_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3227_ = lean_st_ref_get(v_a_2337_);
v_env_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc_ref(v_env_3228_);
lean_dec(v___x_3227_);
v___x_3229_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3230_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3229_, v_env_3228_, v___x_3226_);
v___x_3231_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3232_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3230_, v___x_3231_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3230_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3263_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3263_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3263_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_fst_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3261_; 
v_fst_3237_ = lean_ctor_get(v_a_3233_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_a_3233_);
if (v_isSharedCheck_3261_ == 0)
{
lean_object* v_unused_3262_; 
v_unused_3262_ = lean_ctor_get(v_a_3233_, 1);
lean_dec(v_unused_3262_);
v___x_3239_ = v_a_3233_;
v_isShared_3240_ = v_isSharedCheck_3261_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_fst_3237_);
lean_dec(v_a_3233_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3261_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
if (lean_obj_tag(v_fst_3237_) == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_del_object(v___x_3235_);
v___x_3241_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3242_ = l_Lean_MessageData_ofName(v___x_3226_);
lean_inc_ref(v___x_3242_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 7);
lean_ctor_set(v___x_3239_, 1, v___x_3242_);
lean_ctor_set(v___x_3239_, 0, v___x_3241_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3248_ = l_Lean_indentD(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3246_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v___x_3242_);
v___x_3253_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3254_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3255_;
}
}
else
{
lean_object* v_val_3257_; lean_object* v___x_3259_; 
lean_del_object(v___x_3239_);
lean_dec(v___x_3226_);
lean_dec(v_stx_2331_);
v_val_3257_ = lean_ctor_get(v_fst_3237_, 0);
lean_inc(v_val_3257_);
lean_dec_ref_known(v_fst_3237_, 1);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v_val_3257_);
v___x_3259_ = v___x_3235_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_val_3257_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v___x_3226_);
lean_dec(v_stx_2331_);
v_a_3264_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3232_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3232_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v___x_3272_ = lean_unsigned_to_nat(0u);
v___x_3273_ = l_Lean_Syntax_getArg(v___x_3223_, v___x_3272_);
lean_dec(v___x_3223_);
v___x_3274_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
lean_inc(v___x_3273_);
v___x_3275_ = l_Lean_Syntax_isOfKind(v___x_3273_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_env_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v___x_3273_);
lean_dec(v___x_3198_);
lean_del_object(v___x_3195_);
lean_dec(v_val_3193_);
lean_inc_n(v_stx_2331_, 2);
v___x_3276_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3277_ = lean_st_ref_get(v_a_2337_);
v_env_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc_ref(v_env_3278_);
lean_dec(v___x_3277_);
v___x_3279_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3280_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3279_, v_env_3278_, v___x_3276_);
v___x_3281_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3282_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3280_, v___x_3281_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3280_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3313_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3313_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3313_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_fst_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3311_; 
v_fst_3287_ = lean_ctor_get(v_a_3283_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_a_3283_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v_a_3283_, 1);
lean_dec(v_unused_3312_);
v___x_3289_ = v_a_3283_;
v_isShared_3290_ = v_isSharedCheck_3311_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_fst_3287_);
lean_dec(v_a_3283_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3311_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
if (lean_obj_tag(v_fst_3287_) == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
lean_del_object(v___x_3285_);
v___x_3291_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3292_ = l_Lean_MessageData_ofName(v___x_3276_);
lean_inc_ref(v___x_3292_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 7);
lean_ctor_set(v___x_3289_, 1, v___x_3292_);
lean_ctor_set(v___x_3289_, 0, v___x_3291_);
v___x_3294_ = v___x_3289_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3295_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3298_ = l_Lean_indentD(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3292_);
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3302_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3304_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3305_;
}
}
else
{
lean_object* v_val_3307_; lean_object* v___x_3309_; 
lean_del_object(v___x_3289_);
lean_dec(v___x_3276_);
lean_dec(v_stx_2331_);
v_val_3307_ = lean_ctor_get(v_fst_3287_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v_fst_3287_, 1);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v_val_3307_);
v___x_3309_ = v___x_3285_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_val_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v___x_3276_);
lean_dec(v_stx_2331_);
v_a_3314_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3282_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3282_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v_stx_2331_);
v___x_3322_ = l_Lean_Syntax_getArg(v___x_3273_, v___x_3197_);
lean_dec(v___x_3273_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3322_);
v___x_3324_ = v___x_3195_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
v_finSeq_x3f_3200_ = v___x_3324_;
v___y_3201_ = v_a_2332_;
v___y_3202_ = v_a_2333_;
v___y_3203_ = v_a_2334_;
v___y_3204_ = v_a_2335_;
v___y_3205_ = v_a_2336_;
v___y_3206_ = v_a_2337_;
goto v___jp_3199_;
}
}
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v___x_3223_);
lean_del_object(v___x_3195_);
lean_dec(v_stx_2331_);
v___x_3326_ = lean_box(0);
v_finSeq_x3f_3200_ = v___x_3326_;
v___y_3201_ = v_a_2332_;
v___y_3202_ = v_a_2333_;
v___y_3203_ = v_a_2334_;
v___y_3204_ = v_a_2335_;
v___y_3205_ = v_a_2336_;
v___y_3206_ = v_a_2337_;
goto v___jp_3199_;
}
v___jp_3199_:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3198_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; size_t v_sz_3209_; lean_object* v___x_3210_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v_sz_3209_ = lean_array_size(v_val_3193_);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3193_, v_sz_3209_, v___x_3145_, v_a_3208_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v_val_3193_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3221_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3221_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3211_, v_a_3213_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 0, v___x_3217_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
lean_dec(v_a_3211_);
return v___x_3212_;
}
}
else
{
lean_dec(v_finSeq_x3f_3200_);
return v___x_3210_;
}
}
else
{
lean_dec(v_finSeq_x3f_3200_);
lean_dec(v_val_3193_);
return v___x_3207_;
}
}
}
}
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3452_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3329_);
v___x_3453_ = l_Lean_Syntax_isNone(v___x_3452_);
if (v___x_3453_ == 0)
{
uint8_t v___x_3454_; 
lean_inc(v___x_3452_);
v___x_3454_ = l_Lean_Syntax_matchesNull(v___x_3452_, v___x_3329_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_env_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec(v___x_3452_);
lean_inc_n(v_stx_2331_, 2);
v___x_3455_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3456_ = lean_st_ref_get(v_a_2337_);
v_env_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_ref(v_env_3457_);
lean_dec(v___x_3456_);
v___x_3458_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3459_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3458_, v_env_3457_, v___x_3455_);
v___x_3460_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3461_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3459_, v___x_3460_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3459_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3492_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_fst_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3490_; 
v_fst_3466_ = lean_ctor_get(v_a_3462_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_a_3462_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v_a_3462_, 1);
lean_dec(v_unused_3491_);
v___x_3468_ = v_a_3462_;
v_isShared_3469_ = v_isSharedCheck_3490_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_fst_3466_);
lean_dec(v_a_3462_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3490_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
if (lean_obj_tag(v_fst_3466_) == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
lean_del_object(v___x_3464_);
v___x_3470_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3471_ = l_Lean_MessageData_ofName(v___x_3455_);
lean_inc_ref(v___x_3471_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 7);
lean_ctor_set(v___x_3468_, 1, v___x_3471_);
lean_ctor_set(v___x_3468_, 0, v___x_3470_);
v___x_3473_ = v___x_3468_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3474_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3477_ = l_Lean_indentD(v___x_3476_);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3475_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3471_);
v___x_3482_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3483_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3484_;
}
}
else
{
lean_object* v_val_3486_; lean_object* v___x_3488_; 
lean_del_object(v___x_3468_);
lean_dec(v___x_3455_);
lean_dec(v_stx_2331_);
v_val_3486_ = lean_ctor_get(v_fst_3466_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v_fst_3466_, 1);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v_val_3486_);
v___x_3488_ = v___x_3464_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_val_3486_);
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
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec(v___x_3455_);
lean_dec(v_stx_2331_);
v_a_3493_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3461_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3461_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
if (v___x_3453_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3501_ = l_Lean_Syntax_getArg(v___x_3452_, v___x_3328_);
lean_dec(v___x_3452_);
v___x_3502_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3503_ = l_Lean_Syntax_isOfKind(v___x_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_env_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3504_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3505_ = lean_st_ref_get(v_a_2337_);
v_env_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3506_);
lean_dec(v___x_3505_);
v___x_3507_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3508_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3507_, v_env_3506_, v___x_3504_);
v___x_3509_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3510_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3508_, v___x_3509_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3508_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3541_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3541_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3541_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_fst_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3539_; 
v_fst_3515_ = lean_ctor_get(v_a_3511_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v_a_3511_, 1);
lean_dec(v_unused_3540_);
v___x_3517_ = v_a_3511_;
v_isShared_3518_ = v_isSharedCheck_3539_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_fst_3515_);
lean_dec(v_a_3511_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3539_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
if (lean_obj_tag(v_fst_3515_) == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
lean_del_object(v___x_3513_);
v___x_3519_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3520_ = l_Lean_MessageData_ofName(v___x_3504_);
lean_inc_ref(v___x_3520_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set_tag(v___x_3517_, 7);
lean_ctor_set(v___x_3517_, 1, v___x_3520_);
lean_ctor_set(v___x_3517_, 0, v___x_3519_);
v___x_3522_ = v___x_3517_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3523_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3526_ = l_Lean_indentD(v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3524_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3527_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3520_);
v___x_3531_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3532_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3533_;
}
}
else
{
lean_object* v_val_3535_; lean_object* v___x_3537_; 
lean_del_object(v___x_3517_);
lean_dec(v___x_3504_);
lean_dec(v_stx_2331_);
v_val_3535_ = lean_ctor_get(v_fst_3515_, 0);
lean_inc(v_val_3535_);
lean_dec_ref_known(v_fst_3515_, 1);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v_val_3535_);
v___x_3537_ = v___x_3513_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_val_3535_);
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
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v___x_3504_);
lean_dec(v_stx_2331_);
v_a_3542_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3510_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3510_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
v___y_3347_ = v_a_2332_;
v___y_3348_ = v_a_2333_;
v___y_3349_ = v_a_2334_;
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
goto v___jp_3346_;
}
}
else
{
lean_dec(v___x_3452_);
v___y_3347_ = v_a_2332_;
v___y_3348_ = v_a_2333_;
v___y_3349_ = v_a_2334_;
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
goto v___jp_3346_;
}
}
}
else
{
lean_dec(v___x_3452_);
v___y_3347_ = v_a_2332_;
v___y_3348_ = v_a_2333_;
v___y_3349_ = v_a_2334_;
v___y_3350_ = v_a_2335_;
v___y_3351_ = v_a_2336_;
v___y_3352_ = v_a_2337_;
goto v___jp_3346_;
}
v___jp_3330_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_unsigned_to_nat(3u);
v___x_3338_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3337_);
lean_dec(v_stx_2331_);
v___x_3339_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3338_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; uint8_t v_breaks_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v_breaks_3341_ = lean_ctor_get_uint8(v_a_3340_, sizeof(void*)*2);
if (v_breaks_3341_ == 0)
{
uint8_t v_returnsEarly_3342_; lean_object* v_reassigns_3343_; 
v_returnsEarly_3342_ = lean_ctor_get_uint8(v_a_3340_, sizeof(void*)*2 + 2);
v_reassigns_3343_ = lean_ctor_get(v_a_3340_, 1);
lean_inc(v_reassigns_3343_);
lean_dec(v_a_3340_);
v___y_2744_ = v_reassigns_3343_;
v___y_2745_ = v___x_3328_;
v___y_2746_ = v_returnsEarly_3342_;
v___y_2747_ = v___x_2751_;
goto v___jp_2743_;
}
else
{
uint8_t v_returnsEarly_3344_; lean_object* v_reassigns_3345_; 
v_returnsEarly_3344_ = lean_ctor_get_uint8(v_a_3340_, sizeof(void*)*2 + 2);
v_reassigns_3345_ = lean_ctor_get(v_a_3340_, 1);
lean_inc(v_reassigns_3345_);
lean_dec(v_a_3340_);
v___y_2744_ = v_reassigns_3345_;
v___y_2745_ = v___x_3329_;
v___y_2746_ = v_returnsEarly_3344_;
v___y_2747_ = v___x_2742_;
goto v___jp_2743_;
}
}
else
{
return v___x_3339_;
}
}
v___jp_3346_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; 
v___x_3353_ = lean_unsigned_to_nat(2u);
v___x_3354_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3353_);
v___x_3355_ = l_Lean_Syntax_isNone(v___x_3354_);
if (v___x_3355_ == 0)
{
uint8_t v___x_3356_; 
lean_inc(v___x_3354_);
v___x_3356_ = l_Lean_Syntax_matchesNull(v___x_3354_, v___x_3329_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v_env_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec(v___x_3354_);
lean_inc_n(v_stx_2331_, 2);
v___x_3357_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3358_ = lean_st_ref_get(v___y_3352_);
v_env_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_ref(v_env_3359_);
lean_dec(v___x_3358_);
v___x_3360_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3361_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3360_, v_env_3359_, v___x_3357_);
v___x_3362_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3363_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3361_, v___x_3362_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___x_3361_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3394_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3394_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3394_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3392_; 
v_fst_3368_ = lean_ctor_get(v_a_3364_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_a_3364_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v_a_3364_, 1);
lean_dec(v_unused_3393_);
v___x_3370_ = v_a_3364_;
v_isShared_3371_ = v_isSharedCheck_3392_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_fst_3368_);
lean_dec(v_a_3364_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3392_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
if (lean_obj_tag(v_fst_3368_) == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
lean_del_object(v___x_3366_);
v___x_3372_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3373_ = l_Lean_MessageData_ofName(v___x_3357_);
lean_inc_ref(v___x_3373_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set_tag(v___x_3370_, 7);
lean_ctor_set(v___x_3370_, 1, v___x_3373_);
lean_ctor_set(v___x_3370_, 0, v___x_3372_);
v___x_3375_ = v___x_3370_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3379_ = l_Lean_indentD(v___x_3378_);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3377_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v___x_3373_);
v___x_3384_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3385_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
return v___x_3386_;
}
}
else
{
lean_object* v_val_3388_; lean_object* v___x_3390_; 
lean_del_object(v___x_3370_);
lean_dec(v___x_3357_);
lean_dec(v_stx_2331_);
v_val_3388_ = lean_ctor_get(v_fst_3368_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_fst_3368_, 1);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v_val_3388_);
v___x_3390_ = v___x_3366_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_val_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v___x_3357_);
lean_dec(v_stx_2331_);
v_a_3395_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3363_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3363_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
if (v___x_3355_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3403_ = l_Lean_Syntax_getArg(v___x_3354_, v___x_3328_);
lean_dec(v___x_3354_);
v___x_3404_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3405_ = l_Lean_Syntax_isOfKind(v___x_3403_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_env_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3406_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3407_ = lean_st_ref_get(v___y_3352_);
v_env_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc_ref(v_env_3408_);
lean_dec(v___x_3407_);
v___x_3409_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3410_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3409_, v_env_3408_, v___x_3406_);
v___x_3411_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3412_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3410_, v___x_3411_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___x_3410_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3443_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3443_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3443_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_fst_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3441_; 
v_fst_3417_ = lean_ctor_get(v_a_3413_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_a_3413_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; 
v_unused_3442_ = lean_ctor_get(v_a_3413_, 1);
lean_dec(v_unused_3442_);
v___x_3419_ = v_a_3413_;
v_isShared_3420_ = v_isSharedCheck_3441_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_fst_3417_);
lean_dec(v_a_3413_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3441_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
if (lean_obj_tag(v_fst_3417_) == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_del_object(v___x_3415_);
v___x_3421_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3422_ = l_Lean_MessageData_ofName(v___x_3406_);
lean_inc_ref(v___x_3422_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 7);
lean_ctor_set(v___x_3419_, 1, v___x_3422_);
lean_ctor_set(v___x_3419_, 0, v___x_3421_);
v___x_3424_ = v___x_3419_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3425_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3428_ = l_Lean_indentD(v___x_3427_);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3426_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v___x_3422_);
v___x_3433_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3434_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
return v___x_3435_;
}
}
else
{
lean_object* v_val_3437_; lean_object* v___x_3439_; 
lean_del_object(v___x_3419_);
lean_dec(v___x_3406_);
lean_dec(v_stx_2331_);
v_val_3437_ = lean_ctor_get(v_fst_3417_, 0);
lean_inc(v_val_3437_);
lean_dec_ref_known(v_fst_3417_, 1);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v_val_3437_);
v___x_3439_ = v___x_3415_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_val_3437_);
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
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v___x_3406_);
lean_dec(v_stx_2331_);
v_a_3444_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3412_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3412_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
v___y_3331_ = v___y_3347_;
v___y_3332_ = v___y_3348_;
v___y_3333_ = v___y_3349_;
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
goto v___jp_3330_;
}
}
else
{
lean_dec(v___x_3354_);
v___y_3331_ = v___y_3347_;
v___y_3332_ = v___y_3348_;
v___y_3333_ = v___y_3349_;
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
goto v___jp_3330_;
}
}
}
else
{
lean_dec(v___x_3354_);
v___y_3331_ = v___y_3347_;
v___y_3332_ = v___y_3348_;
v___y_3333_ = v___y_3349_;
v___y_3334_ = v___y_3350_;
v___y_3335_ = v___y_3351_;
v___y_3336_ = v___y_3352_;
goto v___jp_3330_;
}
}
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3687_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_unsigned_to_nat(1u);
v___x_3836_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3551_);
v___x_3837_ = l_Lean_Syntax_getArgs(v___x_3836_);
lean_dec(v___x_3836_);
v___x_3838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3839_ = lean_array_get_size(v___x_3837_);
v___x_3840_ = lean_nat_dec_lt(v___x_3550_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_dec_ref(v___x_3837_);
v___y_3687_ = v___x_3838_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; size_t v___x_3843_; size_t v___x_3844_; lean_object* v___x_3845_; lean_object* v_snd_3846_; 
v___x_3841_ = lean_box(v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
lean_ctor_set(v___x_3842_, 1, v___x_3838_);
v___x_3843_ = ((size_t)0ULL);
v___x_3844_ = lean_usize_of_nat(v___x_3839_);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2742_, v___x_2740_, v___x_3837_, v___x_3843_, v___x_3844_, v___x_3842_);
lean_dec_ref(v___x_3837_);
v_snd_3846_ = lean_ctor_get(v___x_3845_, 1);
lean_inc(v_snd_3846_);
lean_dec_ref(v___x_3845_);
v___y_3687_ = v_snd_3846_;
goto v___jp_3686_;
}
v___jp_3552_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = lean_unsigned_to_nat(5u);
v___x_3560_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3559_);
lean_dec(v_stx_2331_);
v___x_3561_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3560_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3579_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3579_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3579_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
uint8_t v_returnsEarly_3566_; lean_object* v_reassigns_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v_returnsEarly_3566_ = lean_ctor_get_uint8(v_a_3562_, sizeof(void*)*2 + 2);
v_reassigns_3567_ = lean_ctor_get(v_a_3562_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_a_3562_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v_a_3562_, 0);
lean_dec(v_unused_3578_);
v___x_3569_ = v_a_3562_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_reassigns_3567_);
lean_dec(v_a_3562_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3551_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_reassigns_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*2 + 2, v_returnsEarly_3566_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3574_; 
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*2, v___x_2740_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*2 + 1, v___x_2740_);
lean_ctor_set_uint8(v___x_3572_, sizeof(void*)*2 + 3, v___x_2740_);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 0, v___x_3572_);
v___x_3574_ = v___x_3564_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
else
{
return v___x_3561_;
}
}
v___jp_3580_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3587_ = lean_unsigned_to_nat(3u);
v___x_3588_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3587_);
v___x_3589_ = l_Lean_Syntax_isNone(v___x_3588_);
if (v___x_3589_ == 0)
{
uint8_t v___x_3590_; 
lean_inc(v___x_3588_);
v___x_3590_ = l_Lean_Syntax_matchesNull(v___x_3588_, v___x_3551_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_env_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
lean_dec(v___x_3588_);
lean_inc_n(v_stx_2331_, 2);
v___x_3591_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3592_ = lean_st_ref_get(v___y_3586_);
v_env_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc_ref(v_env_3593_);
lean_dec(v___x_3592_);
v___x_3594_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3595_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3594_, v_env_3593_, v___x_3591_);
v___x_3596_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3597_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3595_, v___x_3596_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___x_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3628_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3628_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3628_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v_fst_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3626_; 
v_fst_3602_ = lean_ctor_get(v_a_3598_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v_a_3598_, 1);
lean_dec(v_unused_3627_);
v___x_3604_ = v_a_3598_;
v_isShared_3605_ = v_isSharedCheck_3626_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_fst_3602_);
lean_dec(v_a_3598_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3626_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
if (lean_obj_tag(v_fst_3602_) == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_del_object(v___x_3600_);
v___x_3606_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3607_ = l_Lean_MessageData_ofName(v___x_3591_);
lean_inc_ref(v___x_3607_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 7);
lean_ctor_set(v___x_3604_, 1, v___x_3607_);
lean_ctor_set(v___x_3604_, 0, v___x_3606_);
v___x_3609_ = v___x_3604_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3610_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3613_ = l_Lean_indentD(v___x_3612_);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v___x_3607_);
v___x_3618_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3619_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3620_;
}
}
else
{
lean_object* v_val_3622_; lean_object* v___x_3624_; 
lean_del_object(v___x_3604_);
lean_dec(v___x_3591_);
lean_dec(v_stx_2331_);
v_val_3622_ = lean_ctor_get(v_fst_3602_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v_fst_3602_, 1);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v_val_3622_);
v___x_3624_ = v___x_3600_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_val_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v___x_3591_);
lean_dec(v_stx_2331_);
v_a_3629_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3597_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3597_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
if (v___x_3589_ == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3637_ = l_Lean_Syntax_getArg(v___x_3588_, v___x_3550_);
lean_dec(v___x_3588_);
v___x_3638_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3639_ = l_Lean_Syntax_isOfKind(v___x_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v_env_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3640_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3641_ = lean_st_ref_get(v___y_3586_);
v_env_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc_ref(v_env_3642_);
lean_dec(v___x_3641_);
v___x_3643_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3644_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3643_, v_env_3642_, v___x_3640_);
v___x_3645_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3646_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3644_, v___x_3645_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___x_3644_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3677_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3677_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3677_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_fst_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3675_; 
v_fst_3651_ = lean_ctor_get(v_a_3647_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_a_3647_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_a_3647_, 1);
lean_dec(v_unused_3676_);
v___x_3653_ = v_a_3647_;
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_fst_3651_);
lean_dec(v_a_3647_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3675_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
if (lean_obj_tag(v_fst_3651_) == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
lean_del_object(v___x_3649_);
v___x_3655_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3656_ = l_Lean_MessageData_ofName(v___x_3640_);
lean_inc_ref(v___x_3656_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 7);
lean_ctor_set(v___x_3653_, 1, v___x_3656_);
lean_ctor_set(v___x_3653_, 0, v___x_3655_);
v___x_3658_ = v___x_3653_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3659_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3662_ = l_Lean_indentD(v___x_3661_);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3660_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v___x_3656_);
v___x_3667_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3668_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3669_;
}
}
else
{
lean_object* v_val_3671_; lean_object* v___x_3673_; 
lean_del_object(v___x_3653_);
lean_dec(v___x_3640_);
lean_dec(v_stx_2331_);
v_val_3671_ = lean_ctor_get(v_fst_3651_, 0);
lean_inc(v_val_3671_);
lean_dec_ref_known(v_fst_3651_, 1);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v_val_3671_);
v___x_3673_ = v___x_3649_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_val_3671_);
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
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___x_3640_);
lean_dec(v_stx_2331_);
v_a_3678_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3646_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3646_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
v___y_3553_ = v___y_3581_;
v___y_3554_ = v___y_3582_;
v___y_3555_ = v___y_3583_;
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
goto v___jp_3552_;
}
}
else
{
lean_dec(v___x_3588_);
v___y_3553_ = v___y_3581_;
v___y_3554_ = v___y_3582_;
v___y_3555_ = v___y_3583_;
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
goto v___jp_3552_;
}
}
}
else
{
lean_dec(v___x_3588_);
v___y_3553_ = v___y_3581_;
v___y_3554_ = v___y_3582_;
v___y_3555_ = v___y_3583_;
v___y_3556_ = v___y_3584_;
v___y_3557_ = v___y_3585_;
v___y_3558_ = v___y_3586_;
goto v___jp_3552_;
}
}
v___jp_3686_:
{
size_t v_sz_3688_; size_t v___x_3689_; lean_object* v___x_3690_; 
v_sz_3688_ = lean_array_size(v___y_3687_);
v___x_3689_ = ((size_t)0ULL);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3688_, v___x_3689_, v___y_3687_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_env_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3691_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3692_ = lean_st_ref_get(v_a_2337_);
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
v___x_3694_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3695_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3694_, v_env_3693_, v___x_3691_);
v___x_3696_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3697_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3695_, v___x_3696_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3695_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3728_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3728_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3728_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v_fst_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3726_; 
v_fst_3702_ = lean_ctor_get(v_a_3698_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_a_3698_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v_a_3698_, 1);
lean_dec(v_unused_3727_);
v___x_3704_ = v_a_3698_;
v_isShared_3705_ = v_isSharedCheck_3726_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_fst_3702_);
lean_dec(v_a_3698_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3726_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
if (lean_obj_tag(v_fst_3702_) == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
lean_del_object(v___x_3700_);
v___x_3706_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3707_ = l_Lean_MessageData_ofName(v___x_3691_);
lean_inc_ref(v___x_3707_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set_tag(v___x_3704_, 7);
lean_ctor_set(v___x_3704_, 1, v___x_3707_);
lean_ctor_set(v___x_3704_, 0, v___x_3706_);
v___x_3709_ = v___x_3704_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3710_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3713_ = l_Lean_indentD(v___x_3712_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3711_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___x_3707_);
v___x_3718_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3719_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3720_;
}
}
else
{
lean_object* v_val_3722_; lean_object* v___x_3724_; 
lean_del_object(v___x_3704_);
lean_dec(v___x_3691_);
lean_dec(v_stx_2331_);
v_val_3722_ = lean_ctor_get(v_fst_3702_, 0);
lean_inc(v_val_3722_);
lean_dec_ref_known(v_fst_3702_, 1);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v_val_3722_);
v___x_3724_ = v___x_3700_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_val_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v___x_3691_);
lean_dec(v_stx_2331_);
v_a_3729_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3697_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3697_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
lean_dec_ref_known(v___x_3690_, 1);
v___x_3737_ = lean_unsigned_to_nat(2u);
v___x_3738_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3737_);
v___x_3739_ = l_Lean_Syntax_isNone(v___x_3738_);
if (v___x_3739_ == 0)
{
uint8_t v___x_3740_; 
lean_inc(v___x_3738_);
v___x_3740_ = l_Lean_Syntax_matchesNull(v___x_3738_, v___x_3551_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v_env_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec(v___x_3738_);
lean_inc_n(v_stx_2331_, 2);
v___x_3741_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3742_ = lean_st_ref_get(v_a_2337_);
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc_ref(v_env_3743_);
lean_dec(v___x_3742_);
v___x_3744_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3745_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3744_, v_env_3743_, v___x_3741_);
v___x_3746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3747_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3745_, v___x_3746_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3745_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3778_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3778_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3778_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v_fst_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3776_; 
v_fst_3752_ = lean_ctor_get(v_a_3748_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_a_3748_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; 
v_unused_3777_ = lean_ctor_get(v_a_3748_, 1);
lean_dec(v_unused_3777_);
v___x_3754_ = v_a_3748_;
v_isShared_3755_ = v_isSharedCheck_3776_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_fst_3752_);
lean_dec(v_a_3748_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3776_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
if (lean_obj_tag(v_fst_3752_) == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_del_object(v___x_3750_);
v___x_3756_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3757_ = l_Lean_MessageData_ofName(v___x_3741_);
lean_inc_ref(v___x_3757_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set_tag(v___x_3754_, 7);
lean_ctor_set(v___x_3754_, 1, v___x_3757_);
lean_ctor_set(v___x_3754_, 0, v___x_3756_);
v___x_3759_ = v___x_3754_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3760_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3763_ = l_Lean_indentD(v___x_3762_);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3761_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v___x_3757_);
v___x_3768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3769_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3770_;
}
}
else
{
lean_object* v_val_3772_; lean_object* v___x_3774_; 
lean_del_object(v___x_3754_);
lean_dec(v___x_3741_);
lean_dec(v_stx_2331_);
v_val_3772_ = lean_ctor_get(v_fst_3752_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v_fst_3752_, 1);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_val_3772_);
v___x_3774_ = v___x_3750_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_val_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec(v___x_3741_);
lean_dec(v_stx_2331_);
v_a_3779_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3747_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3747_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
if (v___x_3739_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = l_Lean_Syntax_getArg(v___x_3738_, v___x_3550_);
lean_dec(v___x_3738_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_3789_ = l_Lean_Syntax_isOfKind(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v_env_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3790_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3791_ = lean_st_ref_get(v_a_2337_);
v_env_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc_ref(v_env_3792_);
lean_dec(v___x_3791_);
v___x_3793_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3794_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3793_, v_env_3792_, v___x_3790_);
v___x_3795_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3796_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3794_, v___x_3795_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3794_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3827_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3827_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3827_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_fst_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3825_; 
v_fst_3801_ = lean_ctor_get(v_a_3797_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_a_3797_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_a_3797_, 1);
lean_dec(v_unused_3826_);
v___x_3803_ = v_a_3797_;
v_isShared_3804_ = v_isSharedCheck_3825_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_fst_3801_);
lean_dec(v_a_3797_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3825_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
if (lean_obj_tag(v_fst_3801_) == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
lean_del_object(v___x_3799_);
v___x_3805_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3806_ = l_Lean_MessageData_ofName(v___x_3790_);
lean_inc_ref(v___x_3806_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 7);
lean_ctor_set(v___x_3803_, 1, v___x_3806_);
lean_ctor_set(v___x_3803_, 0, v___x_3805_);
v___x_3808_ = v___x_3803_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3809_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3812_ = l_Lean_indentD(v___x_3811_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3810_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
lean_ctor_set(v___x_3816_, 1, v___x_3806_);
v___x_3817_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3818_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3819_;
}
}
else
{
lean_object* v_val_3821_; lean_object* v___x_3823_; 
lean_del_object(v___x_3803_);
lean_dec(v___x_3790_);
lean_dec(v_stx_2331_);
v_val_3821_ = lean_ctor_get(v_fst_3801_, 0);
lean_inc(v_val_3821_);
lean_dec_ref_known(v_fst_3801_, 1);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_val_3821_);
v___x_3823_ = v___x_3799_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_val_3821_);
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
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v___x_3790_);
lean_dec(v_stx_2331_);
v_a_3828_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3796_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3796_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
v___y_3581_ = v_a_2332_;
v___y_3582_ = v_a_2333_;
v___y_3583_ = v_a_2334_;
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
goto v___jp_3580_;
}
}
else
{
lean_dec(v___x_3738_);
v___y_3581_ = v_a_2332_;
v___y_3582_ = v_a_2333_;
v___y_3583_ = v_a_2334_;
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
goto v___jp_3580_;
}
}
}
else
{
lean_dec(v___x_3738_);
v___y_3581_ = v_a_2332_;
v___y_3582_ = v_a_2333_;
v___y_3583_ = v_a_2334_;
v___y_3584_ = v_a_2335_;
v___y_3585_ = v_a_2336_;
v___y_3586_ = v_a_2337_;
goto v___jp_3580_;
}
}
}
}
v___jp_2743_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2748_, 0, v___y_2745_);
lean_ctor_set(v___x_2748_, 1, v___y_2744_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*2, v___x_2742_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*2 + 1, v___x_2742_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*2 + 2, v___y_2746_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*2 + 3, v___y_2747_);
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
return v___x_2749_;
}
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3847_ = lean_unsigned_to_nat(1u);
v___x_3848_ = lean_unsigned_to_nat(3u);
v___x_3849_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3848_);
lean_dec(v_stx_2331_);
v___x_3850_ = l_Lean_NameSet_empty;
v___x_3851_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3851_, 0, v___x_3847_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*2, v___x_2738_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*2 + 1, v___x_2738_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*2 + 2, v___x_2738_);
lean_ctor_set_uint8(v___x_3851_, sizeof(void*)*2 + 3, v___x_2738_);
v___x_3852_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3849_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3861_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3861_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3851_, v_a_3853_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3857_);
v___x_3859_ = v___x_3855_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
else
{
lean_dec_ref_known(v___x_3851_, 2);
return v___x_3852_;
}
}
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; size_t v_sz_3865_; size_t v___x_3866_; lean_object* v___x_3867_; 
v___x_3862_ = lean_unsigned_to_nat(4u);
v___x_3863_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3862_);
v___x_3864_ = l_Lean_Syntax_getArgs(v___x_3863_);
lean_dec(v___x_3863_);
v_sz_3865_ = lean_array_size(v___x_3864_);
v___x_3866_ = ((size_t)0ULL);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3865_, v___x_3866_, v___x_3864_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v_env_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_inc_n(v_stx_2331_, 2);
v___x_3868_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3869_ = lean_st_ref_get(v_a_2337_);
v_env_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc_ref(v_env_3870_);
lean_dec(v___x_3869_);
v___x_3871_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3872_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3871_, v_env_3870_, v___x_3868_);
v___x_3873_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3874_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3872_, v___x_3873_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3905_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3905_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3905_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v_fst_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3903_; 
v_fst_3879_ = lean_ctor_get(v_a_3875_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_a_3875_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; 
v_unused_3904_ = lean_ctor_get(v_a_3875_, 1);
lean_dec(v_unused_3904_);
v___x_3881_ = v_a_3875_;
v_isShared_3882_ = v_isSharedCheck_3903_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_fst_3879_);
lean_dec(v_a_3875_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3903_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
if (lean_obj_tag(v_fst_3879_) == 0)
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
lean_del_object(v___x_3877_);
v___x_3883_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3884_ = l_Lean_MessageData_ofName(v___x_3868_);
lean_inc_ref(v___x_3884_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 7);
lean_ctor_set(v___x_3881_, 1, v___x_3884_);
lean_ctor_set(v___x_3881_, 0, v___x_3883_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3887_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3890_ = l_Lean_indentD(v___x_3889_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3888_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
v___x_3892_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___x_3884_);
v___x_3895_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3896_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3897_;
}
}
else
{
lean_object* v_val_3899_; lean_object* v___x_3901_; 
lean_del_object(v___x_3881_);
lean_dec(v___x_3868_);
lean_dec(v_stx_2331_);
v_val_3899_ = lean_ctor_get(v_fst_3879_, 0);
lean_inc(v_val_3899_);
lean_dec_ref_known(v_fst_3879_, 1);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v_val_3899_);
v___x_3901_ = v___x_3877_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_val_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec(v___x_3868_);
lean_dec(v_stx_2331_);
v_a_3906_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3874_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3874_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_val_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_4001_; 
v_val_3914_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3916_ = v___x_3867_;
v_isShared_3917_ = v_isSharedCheck_4001_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_val_3914_);
lean_dec(v___x_3867_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_4001_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_elseSeq_x3f_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3918_ = lean_unsigned_to_nat(3u);
v___x_3919_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3918_);
v___x_3944_ = lean_unsigned_to_nat(5u);
v___x_3945_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_3944_);
v___x_3946_ = l_Lean_Syntax_isNone(v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3945_);
v___x_3948_ = l_Lean_Syntax_matchesNull(v___x_3945_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v_env_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec(v___x_3945_);
lean_dec(v___x_3919_);
lean_del_object(v___x_3916_);
lean_dec(v_val_3914_);
lean_inc_n(v_stx_2331_, 2);
v___x_3949_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_3950_ = lean_st_ref_get(v_a_2337_);
v_env_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc_ref(v_env_3951_);
lean_dec(v___x_3950_);
v___x_3952_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3953_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3952_, v_env_3951_, v___x_3949_);
v___x_3954_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3955_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_3953_, v___x_3954_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_3953_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3986_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3986_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3986_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_fst_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3984_; 
v_fst_3960_ = lean_ctor_get(v_a_3956_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_a_3956_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v_a_3956_, 1);
lean_dec(v_unused_3985_);
v___x_3962_ = v_a_3956_;
v_isShared_3963_ = v_isSharedCheck_3984_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_fst_3960_);
lean_dec(v_a_3956_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3984_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
if (lean_obj_tag(v_fst_3960_) == 0)
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3967_; 
lean_del_object(v___x_3958_);
v___x_3964_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3965_ = l_Lean_MessageData_ofName(v___x_3949_);
lean_inc_ref(v___x_3965_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set_tag(v___x_3962_, 7);
lean_ctor_set(v___x_3962_, 1, v___x_3965_);
lean_ctor_set(v___x_3962_, 0, v___x_3964_);
v___x_3967_ = v___x_3962_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3964_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3968_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3967_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_3971_ = l_Lean_indentD(v___x_3970_);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3969_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
lean_ctor_set(v___x_3975_, 1, v___x_3965_);
v___x_3976_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3977_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_3978_;
}
}
else
{
lean_object* v_val_3980_; lean_object* v___x_3982_; 
lean_del_object(v___x_3962_);
lean_dec(v___x_3949_);
lean_dec(v_stx_2331_);
v_val_3980_ = lean_ctor_get(v_fst_3960_, 0);
lean_inc(v_val_3980_);
lean_dec_ref_known(v_fst_3960_, 1);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v_val_3980_);
v___x_3982_ = v___x_3958_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_val_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v___x_3949_);
lean_dec(v_stx_2331_);
v_a_3987_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3955_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3955_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3998_; 
lean_dec(v_stx_2331_);
v___x_3995_ = lean_unsigned_to_nat(1u);
v___x_3996_ = l_Lean_Syntax_getArg(v___x_3945_, v___x_3995_);
lean_dec(v___x_3945_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3996_);
v___x_3998_ = v___x_3916_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
v_elseSeq_x3f_3921_ = v___x_3998_;
v___y_3922_ = v_a_2332_;
v___y_3923_ = v_a_2333_;
v___y_3924_ = v_a_2334_;
v___y_3925_ = v_a_2335_;
v___y_3926_ = v_a_2336_;
v___y_3927_ = v_a_2337_;
goto v___jp_3920_;
}
}
}
else
{
lean_object* v___x_4000_; 
lean_dec(v___x_3945_);
lean_del_object(v___x_3916_);
lean_dec(v_stx_2331_);
v___x_4000_ = lean_box(0);
v_elseSeq_x3f_3921_ = v___x_4000_;
v___y_3922_ = v_a_2332_;
v___y_3923_ = v_a_2333_;
v___y_3924_ = v_a_2334_;
v___y_3925_ = v_a_2335_;
v___y_3926_ = v_a_2336_;
v___y_3927_ = v_a_2337_;
goto v___jp_3920_;
}
v___jp_3920_:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; size_t v_sz_3931_; lean_object* v___x_3932_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = l_Array_reverse___redArg(v_val_3914_);
v_sz_3931_ = lean_array_size(v___x_3930_);
v___x_3932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3930_, v_sz_3931_, v___x_3866_, v_a_3929_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec_ref(v___x_3930_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3919_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3943_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3935_, v_a_3933_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
else
{
lean_dec(v_a_3933_);
return v___x_3934_;
}
}
else
{
lean_dec(v___x_3919_);
return v___x_3932_;
}
}
else
{
lean_dec(v___x_3919_);
lean_dec(v_val_3914_);
return v___x_3928_;
}
}
}
}
}
}
else
{
lean_object* v___x_4002_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___x_4066_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___x_4173_; uint8_t v___x_4174_; 
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4066_ = lean_unsigned_to_nat(1u);
v___x_4173_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4066_);
v___x_4174_ = l_Lean_Syntax_isNone(v___x_4173_);
if (v___x_4174_ == 0)
{
uint8_t v___x_4175_; 
lean_inc(v___x_4173_);
v___x_4175_ = l_Lean_Syntax_matchesNull(v___x_4173_, v___x_4066_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v_env_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec(v___x_4173_);
lean_inc_n(v_stx_2331_, 2);
v___x_4176_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4177_ = lean_st_ref_get(v_a_2337_);
v_env_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_ref(v_env_4178_);
lean_dec(v___x_4177_);
v___x_4179_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4180_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4179_, v_env_4178_, v___x_4176_);
v___x_4181_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4182_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4180_, v___x_4181_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4180_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4213_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4185_ = v___x_4182_;
v_isShared_4186_ = v_isSharedCheck_4213_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4213_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v_fst_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4211_; 
v_fst_4187_ = lean_ctor_get(v_a_4183_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_a_4183_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v_a_4183_, 1);
lean_dec(v_unused_4212_);
v___x_4189_ = v_a_4183_;
v_isShared_4190_ = v_isSharedCheck_4211_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_fst_4187_);
lean_dec(v_a_4183_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4211_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
if (lean_obj_tag(v_fst_4187_) == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4194_; 
lean_del_object(v___x_4185_);
v___x_4191_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4192_ = l_Lean_MessageData_ofName(v___x_4176_);
lean_inc_ref(v___x_4192_);
if (v_isShared_4190_ == 0)
{
lean_ctor_set_tag(v___x_4189_, 7);
lean_ctor_set(v___x_4189_, 1, v___x_4192_);
lean_ctor_set(v___x_4189_, 0, v___x_4191_);
v___x_4194_ = v___x_4189_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4206_, 1, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4195_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4194_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4198_ = l_Lean_indentD(v___x_4197_);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4196_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___x_4192_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4202_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4204_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4205_;
}
}
else
{
lean_object* v_val_4207_; lean_object* v___x_4209_; 
lean_del_object(v___x_4189_);
lean_dec(v___x_4176_);
lean_dec(v_stx_2331_);
v_val_4207_ = lean_ctor_get(v_fst_4187_, 0);
lean_inc(v_val_4207_);
lean_dec_ref_known(v_fst_4187_, 1);
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 0, v_val_4207_);
v___x_4209_ = v___x_4185_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_val_4207_);
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
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v___x_4176_);
lean_dec(v_stx_2331_);
v_a_4214_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4182_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4182_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v___x_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v___x_4222_ = l_Lean_Syntax_getArg(v___x_4173_, v___x_4002_);
lean_dec(v___x_4173_);
v___x_4223_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
v___x_4224_ = l_Lean_Syntax_isOfKind(v___x_4222_, v___x_4223_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v_env_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4225_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4226_ = lean_st_ref_get(v_a_2337_);
v_env_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc_ref(v_env_4227_);
lean_dec(v___x_4226_);
v___x_4228_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4229_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4228_, v_env_4227_, v___x_4225_);
v___x_4230_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4231_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4229_, v___x_4230_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4229_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4262_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4262_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4262_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v_fst_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4260_; 
v_fst_4236_ = lean_ctor_get(v_a_4232_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_a_4232_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; 
v_unused_4261_ = lean_ctor_get(v_a_4232_, 1);
lean_dec(v_unused_4261_);
v___x_4238_ = v_a_4232_;
v_isShared_4239_ = v_isSharedCheck_4260_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_fst_4236_);
lean_dec(v_a_4232_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4260_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
if (lean_obj_tag(v_fst_4236_) == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4243_; 
lean_del_object(v___x_4234_);
v___x_4240_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4241_ = l_Lean_MessageData_ofName(v___x_4225_);
lean_inc_ref(v___x_4241_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set_tag(v___x_4238_, 7);
lean_ctor_set(v___x_4238_, 1, v___x_4241_);
lean_ctor_set(v___x_4238_, 0, v___x_4240_);
v___x_4243_ = v___x_4238_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4244_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4243_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4247_ = l_Lean_indentD(v___x_4246_);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4245_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
lean_ctor_set(v___x_4251_, 1, v___x_4241_);
v___x_4252_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4253_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4254_;
}
}
else
{
lean_object* v_val_4256_; lean_object* v___x_4258_; 
lean_del_object(v___x_4238_);
lean_dec(v___x_4225_);
lean_dec(v_stx_2331_);
v_val_4256_ = lean_ctor_get(v_fst_4236_, 0);
lean_inc(v_val_4256_);
lean_dec_ref_known(v_fst_4236_, 1);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v_val_4256_);
v___x_4258_ = v___x_4234_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_val_4256_);
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
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v___x_4225_);
lean_dec(v_stx_2331_);
v_a_4263_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4231_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4231_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
v___y_4068_ = v_a_2332_;
v___y_4069_ = v_a_2333_;
v___y_4070_ = v_a_2334_;
v___y_4071_ = v_a_2335_;
v___y_4072_ = v_a_2336_;
v___y_4073_ = v_a_2337_;
goto v___jp_4067_;
}
}
}
else
{
lean_dec(v___x_4173_);
v___y_4068_ = v_a_2332_;
v___y_4069_ = v_a_2333_;
v___y_4070_ = v_a_2334_;
v___y_4071_ = v_a_2335_;
v___y_4072_ = v_a_2336_;
v___y_4073_ = v_a_2337_;
goto v___jp_4067_;
}
v___jp_4003_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; uint8_t v___x_4013_; 
v___x_4010_ = lean_unsigned_to_nat(6u);
v___x_4011_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4010_);
v___x_4012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_4011_);
v___x_4013_ = l_Lean_Syntax_isOfKind(v___x_4011_, v___x_4012_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_env_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
lean_dec(v___x_4011_);
lean_inc_n(v_stx_2331_, 2);
v___x_4014_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4015_ = lean_st_ref_get(v___y_4009_);
v_env_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_ref(v_env_4016_);
lean_dec(v___x_4015_);
v___x_4017_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4018_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4017_, v_env_4016_, v___x_4014_);
v___x_4019_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4020_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4018_, v___x_4019_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___x_4018_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4051_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4023_ = v___x_4020_;
v_isShared_4024_ = v_isSharedCheck_4051_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4051_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v_fst_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4049_; 
v_fst_4025_ = lean_ctor_get(v_a_4021_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_a_4021_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v_a_4021_, 1);
lean_dec(v_unused_4050_);
v___x_4027_ = v_a_4021_;
v_isShared_4028_ = v_isSharedCheck_4049_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_fst_4025_);
lean_dec(v_a_4021_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4049_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
if (lean_obj_tag(v_fst_4025_) == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
lean_del_object(v___x_4023_);
v___x_4029_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4030_ = l_Lean_MessageData_ofName(v___x_4014_);
lean_inc_ref(v___x_4030_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set_tag(v___x_4027_, 7);
lean_ctor_set(v___x_4027_, 1, v___x_4030_);
lean_ctor_set(v___x_4027_, 0, v___x_4029_);
v___x_4032_ = v___x_4027_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4033_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4032_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
v___x_4035_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4036_ = l_Lean_indentD(v___x_4035_);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4034_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
lean_ctor_set(v___x_4040_, 1, v___x_4030_);
v___x_4041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4040_);
lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4042_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4043_;
}
}
else
{
lean_object* v_val_4045_; lean_object* v___x_4047_; 
lean_del_object(v___x_4027_);
lean_dec(v___x_4014_);
lean_dec(v_stx_2331_);
v_val_4045_ = lean_ctor_get(v_fst_4025_, 0);
lean_inc(v_val_4045_);
lean_dec_ref_known(v_fst_4025_, 1);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v_val_4045_);
v___x_4047_ = v___x_4023_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_val_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v___x_4014_);
lean_dec(v_stx_2331_);
v_a_4052_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4020_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4020_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; size_t v_sz_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
lean_dec(v_stx_2331_);
v___x_4060_ = l_Lean_Syntax_getArg(v___x_4011_, v___x_4002_);
lean_dec(v___x_4011_);
v___x_4061_ = l_Lean_Syntax_getArgs(v___x_4060_);
lean_dec(v___x_4060_);
v___x_4062_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4063_ = lean_array_size(v___x_4061_);
v___x_4064_ = ((size_t)0ULL);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2734_, v___x_4061_, v_sz_4063_, v___x_4064_, v___x_4062_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec_ref(v___x_4061_);
return v___x_4065_;
}
}
v___jp_4067_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; uint8_t v___x_4076_; 
v___x_4074_ = lean_unsigned_to_nat(2u);
v___x_4075_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4074_);
v___x_4076_ = l_Lean_Syntax_isNone(v___x_4075_);
if (v___x_4076_ == 0)
{
uint8_t v___x_4077_; 
lean_inc(v___x_4075_);
v___x_4077_ = l_Lean_Syntax_matchesNull(v___x_4075_, v___x_4066_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v_env_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec(v___x_4075_);
lean_inc_n(v_stx_2331_, 2);
v___x_4078_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4079_ = lean_st_ref_get(v___y_4073_);
v_env_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc_ref(v_env_4080_);
lean_dec(v___x_4079_);
v___x_4081_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4082_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4081_, v_env_4080_, v___x_4078_);
v___x_4083_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4084_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4082_, v___x_4083_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___x_4082_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4115_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4115_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4115_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v_fst_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4113_; 
v_fst_4089_ = lean_ctor_get(v_a_4085_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_a_4085_);
if (v_isSharedCheck_4113_ == 0)
{
lean_object* v_unused_4114_; 
v_unused_4114_ = lean_ctor_get(v_a_4085_, 1);
lean_dec(v_unused_4114_);
v___x_4091_ = v_a_4085_;
v_isShared_4092_ = v_isSharedCheck_4113_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_fst_4089_);
lean_dec(v_a_4085_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4113_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
if (lean_obj_tag(v_fst_4089_) == 0)
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4096_; 
lean_del_object(v___x_4087_);
v___x_4093_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4094_ = l_Lean_MessageData_ofName(v___x_4078_);
lean_inc_ref(v___x_4094_);
if (v_isShared_4092_ == 0)
{
lean_ctor_set_tag(v___x_4091_, 7);
lean_ctor_set(v___x_4091_, 1, v___x_4094_);
lean_ctor_set(v___x_4091_, 0, v___x_4093_);
v___x_4096_ = v___x_4091_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4093_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v___x_4094_);
v___x_4096_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4097_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4100_ = l_Lean_indentD(v___x_4099_);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4098_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v___x_4094_);
v___x_4105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4106_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
return v___x_4107_;
}
}
else
{
lean_object* v_val_4109_; lean_object* v___x_4111_; 
lean_del_object(v___x_4091_);
lean_dec(v___x_4078_);
lean_dec(v_stx_2331_);
v_val_4109_ = lean_ctor_get(v_fst_4089_, 0);
lean_inc(v_val_4109_);
lean_dec_ref_known(v_fst_4089_, 1);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v_val_4109_);
v___x_4111_ = v___x_4087_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_val_4109_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v___x_4078_);
lean_dec(v_stx_2331_);
v_a_4116_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4084_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4084_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; 
v___x_4124_ = l_Lean_Syntax_getArg(v___x_4075_, v___x_4002_);
lean_dec(v___x_4075_);
v___x_4125_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4126_ = l_Lean_Syntax_isOfKind(v___x_4124_, v___x_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v_env_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4127_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4128_ = lean_st_ref_get(v___y_4073_);
v_env_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc_ref(v_env_4129_);
lean_dec(v___x_4128_);
v___x_4130_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4131_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4130_, v_env_4129_, v___x_4127_);
v___x_4132_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4133_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4131_, v___x_4132_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___x_4131_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4164_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4136_ = v___x_4133_;
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4164_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v_fst_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4162_; 
v_fst_4138_ = lean_ctor_get(v_a_4134_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_a_4134_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; 
v_unused_4163_ = lean_ctor_get(v_a_4134_, 1);
lean_dec(v_unused_4163_);
v___x_4140_ = v_a_4134_;
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_fst_4138_);
lean_dec(v_a_4134_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4162_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
if (lean_obj_tag(v_fst_4138_) == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
lean_del_object(v___x_4136_);
v___x_4142_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4143_ = l_Lean_MessageData_ofName(v___x_4127_);
lean_inc_ref(v___x_4143_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set_tag(v___x_4140_, 7);
lean_ctor_set(v___x_4140_, 1, v___x_4143_);
lean_ctor_set(v___x_4140_, 0, v___x_4142_);
v___x_4145_ = v___x_4140_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4157_, 1, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4149_ = l_Lean_indentD(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4147_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4150_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v___x_4143_);
v___x_4154_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4153_);
lean_ctor_set(v___x_4155_, 1, v___x_4154_);
v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4155_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
return v___x_4156_;
}
}
else
{
lean_object* v_val_4158_; lean_object* v___x_4160_; 
lean_del_object(v___x_4140_);
lean_dec(v___x_4127_);
lean_dec(v_stx_2331_);
v_val_4158_ = lean_ctor_get(v_fst_4138_, 0);
lean_inc(v_val_4158_);
lean_dec_ref_known(v_fst_4138_, 1);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 0, v_val_4158_);
v___x_4160_ = v___x_4136_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_val_4158_);
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
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v___x_4127_);
lean_dec(v_stx_2331_);
v_a_4165_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4133_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4133_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
v___y_4004_ = v___y_4068_;
v___y_4005_ = v___y_4069_;
v___y_4006_ = v___y_4070_;
v___y_4007_ = v___y_4071_;
v___y_4008_ = v___y_4072_;
v___y_4009_ = v___y_4073_;
goto v___jp_4003_;
}
}
}
else
{
lean_dec(v___x_4075_);
v___y_4004_ = v___y_4068_;
v___y_4005_ = v___y_4069_;
v___y_4006_ = v___y_4070_;
v___y_4007_ = v___y_4071_;
v___y_4008_ = v___y_4072_;
v___y_4009_ = v___y_4073_;
goto v___jp_4003_;
}
}
}
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = lean_unsigned_to_nat(0u);
v___x_4272_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4271_);
if (v___x_2732_ == 0)
{
lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4273_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4272_);
v___x_4274_ = l_Lean_Syntax_isOfKind(v___x_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
if (v___x_2732_ == 0)
{
lean_object* v___x_4275_; uint8_t v___x_4276_; 
v___x_4275_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4272_);
v___x_4276_ = l_Lean_Syntax_isOfKind(v___x_4272_, v___x_4275_);
if (v___x_4276_ == 0)
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v_env_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_dec(v___x_4272_);
lean_inc_n(v_stx_2331_, 2);
v___x_4277_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4278_ = lean_st_ref_get(v_a_2337_);
v_env_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc_ref(v_env_4279_);
lean_dec(v___x_4278_);
v___x_4280_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4281_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4280_, v_env_4279_, v___x_4277_);
v___x_4282_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4283_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4281_, v___x_4282_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4281_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4314_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4286_ = v___x_4283_;
v_isShared_4287_ = v_isSharedCheck_4314_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4283_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4314_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v_fst_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4312_; 
v_fst_4288_ = lean_ctor_get(v_a_4284_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_a_4284_);
if (v_isSharedCheck_4312_ == 0)
{
lean_object* v_unused_4313_; 
v_unused_4313_ = lean_ctor_get(v_a_4284_, 1);
lean_dec(v_unused_4313_);
v___x_4290_ = v_a_4284_;
v_isShared_4291_ = v_isSharedCheck_4312_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_fst_4288_);
lean_dec(v_a_4284_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4312_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
if (lean_obj_tag(v_fst_4288_) == 0)
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
lean_del_object(v___x_4286_);
v___x_4292_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4293_ = l_Lean_MessageData_ofName(v___x_4277_);
lean_inc_ref(v___x_4293_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set_tag(v___x_4290_, 7);
lean_ctor_set(v___x_4290_, 1, v___x_4293_);
lean_ctor_set(v___x_4290_, 0, v___x_4292_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4307_, 1, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4296_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4299_ = l_Lean_indentD(v___x_4298_);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4297_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
lean_ctor_set(v___x_4303_, 1, v___x_4293_);
v___x_4304_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4305_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4306_;
}
}
else
{
lean_object* v_val_4308_; lean_object* v___x_4310_; 
lean_del_object(v___x_4290_);
lean_dec(v___x_4277_);
lean_dec(v_stx_2331_);
v_val_4308_ = lean_ctor_get(v_fst_4288_, 0);
lean_inc(v_val_4308_);
lean_dec_ref_known(v_fst_4288_, 1);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 0, v_val_4308_);
v___x_4310_ = v___x_4286_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_val_4308_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v___x_4277_);
lean_dec(v_stx_2331_);
v_a_4315_ = lean_ctor_get(v___x_4283_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4283_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4283_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4283_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v___x_4323_; 
lean_dec(v_stx_2331_);
v___x_4323_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2421_, v___x_4272_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4323_;
}
}
else
{
lean_object* v___x_4324_; 
lean_dec(v_stx_2331_);
v___x_4324_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2421_, v___x_4272_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4324_;
}
}
else
{
lean_object* v___x_4325_; 
lean_dec(v_stx_2331_);
v___x_4325_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2421_, v___x_4272_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4325_;
}
}
else
{
lean_object* v___x_4326_; 
lean_dec(v_stx_2331_);
v___x_4326_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2421_, v___x_4272_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4326_;
}
}
}
else
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_unsigned_to_nat(0u);
v___x_4328_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4327_);
if (v___x_2730_ == 0)
{
lean_object* v___x_4355_; uint8_t v___x_4356_; 
v___x_4355_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4328_);
v___x_4356_ = l_Lean_Syntax_isOfKind(v___x_4328_, v___x_4355_);
if (v___x_4356_ == 0)
{
if (v___x_2730_ == 0)
{
lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4357_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4328_);
v___x_4358_ = l_Lean_Syntax_isOfKind(v___x_4328_, v___x_4357_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v_env_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
lean_dec(v___x_4328_);
lean_inc_n(v_stx_2331_, 2);
v___x_4359_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4360_ = lean_st_ref_get(v_a_2337_);
v_env_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc_ref(v_env_4361_);
lean_dec(v___x_4360_);
v___x_4362_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4363_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4362_, v_env_4361_, v___x_4359_);
v___x_4364_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4365_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4363_, v___x_4364_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4363_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4396_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4396_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4396_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v_fst_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4394_; 
v_fst_4370_ = lean_ctor_get(v_a_4366_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_a_4366_);
if (v_isSharedCheck_4394_ == 0)
{
lean_object* v_unused_4395_; 
v_unused_4395_ = lean_ctor_get(v_a_4366_, 1);
lean_dec(v_unused_4395_);
v___x_4372_ = v_a_4366_;
v_isShared_4373_ = v_isSharedCheck_4394_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_fst_4370_);
lean_dec(v_a_4366_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4394_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
if (lean_obj_tag(v_fst_4370_) == 0)
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
lean_del_object(v___x_4368_);
v___x_4374_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4375_ = l_Lean_MessageData_ofName(v___x_4359_);
lean_inc_ref(v___x_4375_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 7);
lean_ctor_set(v___x_4372_, 1, v___x_4375_);
lean_ctor_set(v___x_4372_, 0, v___x_4374_);
v___x_4377_ = v___x_4372_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4374_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4378_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4381_ = l_Lean_indentD(v___x_4380_);
v___x_4382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4379_);
lean_ctor_set(v___x_4382_, 1, v___x_4381_);
v___x_4383_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4382_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
lean_ctor_set(v___x_4385_, 1, v___x_4375_);
v___x_4386_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4387_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4388_;
}
}
else
{
lean_object* v_val_4390_; lean_object* v___x_4392_; 
lean_del_object(v___x_4372_);
lean_dec(v___x_4359_);
lean_dec(v_stx_2331_);
v_val_4390_ = lean_ctor_get(v_fst_4370_, 0);
lean_inc(v_val_4390_);
lean_dec_ref_known(v_fst_4370_, 1);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v_val_4390_);
v___x_4392_ = v___x_4368_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_val_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_dec(v___x_4359_);
lean_dec(v_stx_2331_);
v_a_4397_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4365_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4365_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_4329_;
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_4329_;
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_4342_;
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_4342_;
}
v___jp_4329_:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4328_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4328_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = lean_box(0);
v___x_4333_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4331_, v___x_4332_, v___x_4332_, v___x_4332_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4333_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4330_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4330_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
v___jp_4342_:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4328_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4328_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4343_, 1);
v___x_4345_ = lean_box(0);
v___x_4346_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4344_, v___x_4345_, v___x_4345_, v___x_4345_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4346_;
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v_a_4347_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4343_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4343_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
}
else
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4405_);
v___x_4407_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
lean_inc(v___x_4406_);
v___x_4408_ = l_Lean_Syntax_isOfKind(v___x_4406_, v___x_4407_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v_env_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
lean_dec(v___x_4406_);
lean_inc_n(v_stx_2331_, 2);
v___x_4409_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4410_ = lean_st_ref_get(v_a_2337_);
v_env_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc_ref(v_env_4411_);
lean_dec(v___x_4410_);
v___x_4412_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4413_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4412_, v_env_4411_, v___x_4409_);
v___x_4414_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4415_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4413_, v___x_4414_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4413_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4446_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4446_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4446_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v_fst_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4444_; 
v_fst_4420_ = lean_ctor_get(v_a_4416_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v_a_4416_);
if (v_isSharedCheck_4444_ == 0)
{
lean_object* v_unused_4445_; 
v_unused_4445_ = lean_ctor_get(v_a_4416_, 1);
lean_dec(v_unused_4445_);
v___x_4422_ = v_a_4416_;
v_isShared_4423_ = v_isSharedCheck_4444_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_fst_4420_);
lean_dec(v_a_4416_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4444_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
if (lean_obj_tag(v_fst_4420_) == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
lean_del_object(v___x_4418_);
v___x_4424_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4425_ = l_Lean_MessageData_ofName(v___x_4409_);
lean_inc_ref(v___x_4425_);
if (v_isShared_4423_ == 0)
{
lean_ctor_set_tag(v___x_4422_, 7);
lean_ctor_set(v___x_4422_, 1, v___x_4425_);
lean_ctor_set(v___x_4422_, 0, v___x_4424_);
v___x_4427_ = v___x_4422_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4424_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4428_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
v___x_4430_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4431_ = l_Lean_indentD(v___x_4430_);
v___x_4432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4429_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___x_4425_);
v___x_4436_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4437_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4438_;
}
}
else
{
lean_object* v_val_4440_; lean_object* v___x_4442_; 
lean_del_object(v___x_4422_);
lean_dec(v___x_4409_);
lean_dec(v_stx_2331_);
v_val_4440_ = lean_ctor_get(v_fst_4420_, 0);
lean_inc(v_val_4440_);
lean_dec_ref_known(v_fst_4420_, 1);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v_val_4440_);
v___x_4442_ = v___x_4418_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_val_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v___x_4409_);
lean_dec(v_stx_2331_);
v_a_4447_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4415_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4415_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v___x_4455_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___x_4561_; uint8_t v___x_4562_; 
v___x_4455_ = lean_unsigned_to_nat(1u);
v___x_4561_ = l_Lean_Syntax_getArg(v___x_4406_, v___x_4455_);
lean_dec(v___x_4406_);
v___x_4562_ = l_Lean_Syntax_isNone(v___x_4561_);
if (v___x_4562_ == 0)
{
uint8_t v___x_4563_; 
v___x_4563_ = l_Lean_Syntax_matchesNull(v___x_4561_, v___x_4455_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v_env_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4564_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4565_ = lean_st_ref_get(v_a_2337_);
v_env_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc_ref(v_env_4566_);
lean_dec(v___x_4565_);
v___x_4567_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4568_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4567_, v_env_4566_, v___x_4564_);
v___x_4569_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4570_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4568_, v___x_4569_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4568_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4601_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4573_ = v___x_4570_;
v_isShared_4574_ = v_isSharedCheck_4601_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4570_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4601_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v_fst_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4599_; 
v_fst_4575_ = lean_ctor_get(v_a_4571_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_a_4571_);
if (v_isSharedCheck_4599_ == 0)
{
lean_object* v_unused_4600_; 
v_unused_4600_ = lean_ctor_get(v_a_4571_, 1);
lean_dec(v_unused_4600_);
v___x_4577_ = v_a_4571_;
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_fst_4575_);
lean_dec(v_a_4571_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4599_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
if (lean_obj_tag(v_fst_4575_) == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
lean_del_object(v___x_4573_);
v___x_4579_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4580_ = l_Lean_MessageData_ofName(v___x_4564_);
lean_inc_ref(v___x_4580_);
if (v_isShared_4578_ == 0)
{
lean_ctor_set_tag(v___x_4577_, 7);
lean_ctor_set(v___x_4577_, 1, v___x_4580_);
lean_ctor_set(v___x_4577_, 0, v___x_4579_);
v___x_4582_ = v___x_4577_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4594_, 1, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4583_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4586_ = l_Lean_indentD(v___x_4585_);
v___x_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4584_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
lean_ctor_set(v___x_4590_, 1, v___x_4580_);
v___x_4591_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4590_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4592_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4593_;
}
}
else
{
lean_object* v_val_4595_; lean_object* v___x_4597_; 
lean_del_object(v___x_4577_);
lean_dec(v___x_4564_);
lean_dec(v_stx_2331_);
v_val_4595_ = lean_ctor_get(v_fst_4575_, 0);
lean_inc(v_val_4595_);
lean_dec_ref_known(v_fst_4575_, 1);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 0, v_val_4595_);
v___x_4597_ = v___x_4573_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_val_4595_);
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
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_dec(v___x_4564_);
lean_dec(v_stx_2331_);
v_a_4602_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4570_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4570_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
else
{
v___y_4457_ = v_a_2332_;
v___y_4458_ = v_a_2333_;
v___y_4459_ = v_a_2334_;
v___y_4460_ = v_a_2335_;
v___y_4461_ = v_a_2336_;
v___y_4462_ = v_a_2337_;
goto v___jp_4456_;
}
}
else
{
lean_dec(v___x_4561_);
v___y_4457_ = v_a_2332_;
v___y_4458_ = v_a_2333_;
v___y_4459_ = v_a_2334_;
v___y_4460_ = v_a_2335_;
v___y_4461_ = v_a_2336_;
v___y_4462_ = v_a_2337_;
goto v___jp_4456_;
}
v___jp_4456_:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4463_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4455_);
v___x_4464_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__90));
lean_inc(v___x_4463_);
v___x_4465_ = l_Lean_Syntax_isOfKind(v___x_4463_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v_env_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec(v___x_4463_);
lean_inc_n(v_stx_2331_, 2);
v___x_4466_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4467_ = lean_st_ref_get(v___y_4462_);
v_env_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc_ref(v_env_4468_);
lean_dec(v___x_4467_);
v___x_4469_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4470_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4469_, v_env_4468_, v___x_4466_);
v___x_4471_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4472_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4470_, v___x_4471_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___x_4470_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4503_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4503_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4503_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_fst_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4501_; 
v_fst_4477_ = lean_ctor_get(v_a_4473_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_a_4473_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v_a_4473_, 1);
lean_dec(v_unused_4502_);
v___x_4479_ = v_a_4473_;
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_fst_4477_);
lean_dec(v_a_4473_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4501_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
if (lean_obj_tag(v_fst_4477_) == 0)
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
lean_del_object(v___x_4475_);
v___x_4481_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4482_ = l_Lean_MessageData_ofName(v___x_4466_);
lean_inc_ref(v___x_4482_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set_tag(v___x_4479_, 7);
lean_ctor_set(v___x_4479_, 1, v___x_4482_);
lean_ctor_set(v___x_4479_, 0, v___x_4481_);
v___x_4484_ = v___x_4479_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4481_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4485_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4484_);
lean_ctor_set(v___x_4486_, 1, v___x_4485_);
v___x_4487_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4488_ = l_Lean_indentD(v___x_4487_);
v___x_4489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4486_);
lean_ctor_set(v___x_4489_, 1, v___x_4488_);
v___x_4490_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4491_);
lean_ctor_set(v___x_4492_, 1, v___x_4482_);
v___x_4493_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4494_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
return v___x_4495_;
}
}
else
{
lean_object* v_val_4497_; lean_object* v___x_4499_; 
lean_del_object(v___x_4479_);
lean_dec(v___x_4466_);
lean_dec(v_stx_2331_);
v_val_4497_ = lean_ctor_get(v_fst_4477_, 0);
lean_inc(v_val_4497_);
lean_dec_ref_known(v_fst_4477_, 1);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v_val_4497_);
v___x_4499_ = v___x_4475_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_val_4497_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v___x_4466_);
lean_dec(v_stx_2331_);
v_a_4504_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4472_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4472_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v___x_4512_; uint8_t v___x_4513_; 
v___x_4512_ = l_Lean_Syntax_getArg(v___x_4463_, v___x_4455_);
lean_dec(v___x_4463_);
v___x_4513_ = l_Lean_Syntax_isNone(v___x_4512_);
if (v___x_4513_ == 0)
{
uint8_t v___x_4514_; 
v___x_4514_ = l_Lean_Syntax_matchesNull(v___x_4512_, v___x_4455_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v_env_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4515_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4516_ = lean_st_ref_get(v___y_4462_);
v_env_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc_ref(v_env_4517_);
lean_dec(v___x_4516_);
v___x_4518_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4519_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4518_, v_env_4517_, v___x_4515_);
v___x_4520_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4521_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4519_, v___x_4520_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___x_4519_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4552_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4524_ = v___x_4521_;
v_isShared_4525_ = v_isSharedCheck_4552_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4552_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v_fst_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4550_; 
v_fst_4526_ = lean_ctor_get(v_a_4522_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_a_4522_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v_a_4522_, 1);
lean_dec(v_unused_4551_);
v___x_4528_ = v_a_4522_;
v_isShared_4529_ = v_isSharedCheck_4550_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_fst_4526_);
lean_dec(v_a_4522_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4550_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
if (lean_obj_tag(v_fst_4526_) == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
lean_del_object(v___x_4524_);
v___x_4530_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4531_ = l_Lean_MessageData_ofName(v___x_4515_);
lean_inc_ref(v___x_4531_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set_tag(v___x_4528_, 7);
lean_ctor_set(v___x_4528_, 1, v___x_4531_);
lean_ctor_set(v___x_4528_, 0, v___x_4530_);
v___x_4533_ = v___x_4528_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4530_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4534_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4533_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4537_ = l_Lean_indentD(v___x_4536_);
v___x_4538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4535_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4540_);
lean_ctor_set(v___x_4541_, 1, v___x_4531_);
v___x_4542_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
v___x_4544_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4543_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
return v___x_4544_;
}
}
else
{
lean_object* v_val_4546_; lean_object* v___x_4548_; 
lean_del_object(v___x_4528_);
lean_dec(v___x_4515_);
lean_dec(v_stx_2331_);
v_val_4546_ = lean_ctor_get(v_fst_4526_, 0);
lean_inc(v_val_4546_);
lean_dec_ref_known(v_fst_4526_, 1);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v_val_4546_);
v___x_4548_ = v___x_4524_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_val_4546_);
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
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v___x_4515_);
lean_dec(v_stx_2331_);
v_a_4553_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4521_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4521_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2381_;
}
}
else
{
lean_dec(v___x_4512_);
lean_dec(v_stx_2331_);
goto v___jp_2381_;
}
}
}
}
}
}
else
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4610_ = lean_unsigned_to_nat(1u);
v___x_4611_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4610_);
v___x_4612_ = l_Lean_Syntax_isNone(v___x_4611_);
if (v___x_4612_ == 0)
{
uint8_t v___x_4613_; 
v___x_4613_ = l_Lean_Syntax_matchesNull(v___x_4611_, v___x_4610_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v_env_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4614_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4615_ = lean_st_ref_get(v_a_2337_);
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc_ref(v_env_4616_);
lean_dec(v___x_4615_);
v___x_4617_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4618_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4617_, v_env_4616_, v___x_4614_);
v___x_4619_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4620_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4618_, v___x_4619_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4618_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4651_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4623_ = v___x_4620_;
v_isShared_4624_ = v_isSharedCheck_4651_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4620_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4651_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v_fst_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4649_; 
v_fst_4625_ = lean_ctor_get(v_a_4621_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_a_4621_);
if (v_isSharedCheck_4649_ == 0)
{
lean_object* v_unused_4650_; 
v_unused_4650_ = lean_ctor_get(v_a_4621_, 1);
lean_dec(v_unused_4650_);
v___x_4627_ = v_a_4621_;
v_isShared_4628_ = v_isSharedCheck_4649_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_fst_4625_);
lean_dec(v_a_4621_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4649_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
if (lean_obj_tag(v_fst_4625_) == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
lean_del_object(v___x_4623_);
v___x_4629_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4630_ = l_Lean_MessageData_ofName(v___x_4614_);
lean_inc_ref(v___x_4630_);
if (v_isShared_4628_ == 0)
{
lean_ctor_set_tag(v___x_4627_, 7);
lean_ctor_set(v___x_4627_, 1, v___x_4630_);
lean_ctor_set(v___x_4627_, 0, v___x_4629_);
v___x_4632_ = v___x_4627_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v___x_4630_);
v___x_4632_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4633_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4632_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4636_ = l_Lean_indentD(v___x_4635_);
v___x_4637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4634_);
lean_ctor_set(v___x_4637_, 1, v___x_4636_);
v___x_4638_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4637_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v___x_4630_);
v___x_4641_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4642_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4643_;
}
}
else
{
lean_object* v_val_4645_; lean_object* v___x_4647_; 
lean_del_object(v___x_4627_);
lean_dec(v___x_4614_);
lean_dec(v_stx_2331_);
v_val_4645_ = lean_ctor_get(v_fst_4625_, 0);
lean_inc(v_val_4645_);
lean_dec_ref_known(v_fst_4625_, 1);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v_val_4645_);
v___x_4647_ = v___x_4623_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_val_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec(v___x_4614_);
lean_dec(v_stx_2331_);
v_a_4652_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4620_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4620_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
else
{
v___y_2671_ = v_a_2332_;
v___y_2672_ = v_a_2333_;
v___y_2673_ = v_a_2334_;
v___y_2674_ = v_a_2335_;
v___y_2675_ = v_a_2336_;
v___y_2676_ = v_a_2337_;
goto v___jp_2670_;
}
}
else
{
lean_dec(v___x_4611_);
v___y_2671_ = v_a_2332_;
v___y_2672_ = v_a_2333_;
v___y_2673_ = v_a_2334_;
v___y_2674_ = v_a_2335_;
v___y_2675_ = v_a_2336_;
v___y_2676_ = v_a_2337_;
goto v___jp_2670_;
}
}
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; 
v___x_4660_ = lean_unsigned_to_nat(1u);
v___x_4661_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4660_);
v___x_4662_ = l_Lean_Syntax_isNone(v___x_4661_);
if (v___x_4662_ == 0)
{
uint8_t v___x_4663_; 
v___x_4663_ = l_Lean_Syntax_matchesNull(v___x_4661_, v___x_4660_);
if (v___x_4663_ == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v_env_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4664_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4665_ = lean_st_ref_get(v_a_2337_);
v_env_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_ref(v_env_4666_);
lean_dec(v___x_4665_);
v___x_4667_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4668_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4667_, v_env_4666_, v___x_4664_);
v___x_4669_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4670_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4668_, v___x_4669_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4668_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4701_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4701_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4701_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v_fst_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4699_; 
v_fst_4675_ = lean_ctor_get(v_a_4671_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_a_4671_);
if (v_isSharedCheck_4699_ == 0)
{
lean_object* v_unused_4700_; 
v_unused_4700_ = lean_ctor_get(v_a_4671_, 1);
lean_dec(v_unused_4700_);
v___x_4677_ = v_a_4671_;
v_isShared_4678_ = v_isSharedCheck_4699_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_fst_4675_);
lean_dec(v_a_4671_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4699_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
if (lean_obj_tag(v_fst_4675_) == 0)
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
lean_del_object(v___x_4673_);
v___x_4679_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4680_ = l_Lean_MessageData_ofName(v___x_4664_);
lean_inc_ref(v___x_4680_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set_tag(v___x_4677_, 7);
lean_ctor_set(v___x_4677_, 1, v___x_4680_);
lean_ctor_set(v___x_4677_, 0, v___x_4679_);
v___x_4682_ = v___x_4677_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___x_4680_);
v___x_4682_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4683_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4682_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4686_ = l_Lean_indentD(v___x_4685_);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4684_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4687_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
lean_ctor_set(v___x_4690_, 1, v___x_4680_);
v___x_4691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4692_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4693_;
}
}
else
{
lean_object* v_val_4695_; lean_object* v___x_4697_; 
lean_del_object(v___x_4677_);
lean_dec(v___x_4664_);
lean_dec(v_stx_2331_);
v_val_4695_ = lean_ctor_get(v_fst_4675_, 0);
lean_inc(v_val_4695_);
lean_dec_ref_known(v_fst_4675_, 1);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v_val_4695_);
v___x_4697_ = v___x_4673_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_val_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v___x_4664_);
lean_dec(v_stx_2331_);
v_a_4702_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4670_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4670_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
v___y_2602_ = v_a_2332_;
v___y_2603_ = v_a_2333_;
v___y_2604_ = v_a_2334_;
v___y_2605_ = v_a_2335_;
v___y_2606_ = v_a_2336_;
v___y_2607_ = v_a_2337_;
goto v___jp_2601_;
}
}
else
{
lean_dec(v___x_4661_);
v___y_2602_ = v_a_2332_;
v___y_2603_ = v_a_2333_;
v___y_2604_ = v_a_2334_;
v___y_2605_ = v_a_2335_;
v___y_2606_ = v_a_2336_;
v___y_2607_ = v_a_2337_;
goto v___jp_2601_;
}
}
v___jp_2660_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_unsigned_to_nat(3u);
v___x_2668_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2667_);
lean_dec(v_stx_2331_);
v___x_2669_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2659_, v___x_2668_, v___y_2663_, v___y_2666_, v___y_2662_, v___y_2664_, v___y_2661_, v___y_2665_);
return v___x_2669_;
}
v___jp_2670_:
{
if (v___x_2659_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2677_ = lean_unsigned_to_nat(2u);
v___x_2678_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2677_);
v___x_2679_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2680_ = l_Lean_Syntax_isOfKind(v___x_2678_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_env_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2681_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2682_ = lean_st_ref_get(v___y_2676_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2683_);
lean_dec(v___x_2682_);
v___x_2684_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2685_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2684_, v_env_2683_, v___x_2681_);
v___x_2686_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2687_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2685_, v___x_2686_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___x_2685_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2718_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2718_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_fst_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2716_; 
v_fst_2692_ = lean_ctor_get(v_a_2688_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_a_2688_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v_a_2688_, 1);
lean_dec(v_unused_2717_);
v___x_2694_ = v_a_2688_;
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_fst_2692_);
lean_dec(v_a_2688_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_fst_2692_) == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_del_object(v___x_2690_);
v___x_2696_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2697_ = l_Lean_MessageData_ofName(v___x_2681_);
lean_inc_ref(v___x_2697_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 7);
lean_ctor_set(v___x_2694_, 1, v___x_2697_);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2699_ = v___x_2694_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2700_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2703_ = l_Lean_indentD(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2697_);
v___x_2708_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2709_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v___x_2710_;
}
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2714_; 
lean_del_object(v___x_2694_);
lean_dec(v___x_2681_);
lean_dec(v_stx_2331_);
v_val_2712_ = lean_ctor_get(v_fst_2692_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v_fst_2692_, 1);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v_val_2712_);
v___x_2714_ = v___x_2690_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_val_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v___x_2681_);
lean_dec(v_stx_2331_);
v_a_2719_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2687_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2687_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
else
{
v___y_2661_ = v___y_2675_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2672_;
goto v___jp_2660_;
}
}
else
{
v___y_2661_ = v___y_2675_;
v___y_2662_ = v___y_2673_;
v___y_2663_ = v___y_2671_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2672_;
goto v___jp_2660_;
}
}
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4710_ = lean_unsigned_to_nat(0u);
v___x_4711_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4710_);
v___x_4712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4713_ = l_Lean_Syntax_isOfKind(v___x_4711_, v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_env_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
lean_del_object(v___x_2395_);
lean_inc_n(v_stx_2331_, 2);
v___x_4714_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4715_ = lean_st_ref_get(v_a_2337_);
v_env_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc_ref(v_env_4716_);
lean_dec(v___x_4715_);
v___x_4717_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4718_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4717_, v_env_4716_, v___x_4714_);
v___x_4719_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4720_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4718_, v___x_4719_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4718_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4751_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4751_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4751_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_fst_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4749_; 
v_fst_4725_ = lean_ctor_get(v_a_4721_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v_a_4721_);
if (v_isSharedCheck_4749_ == 0)
{
lean_object* v_unused_4750_; 
v_unused_4750_ = lean_ctor_get(v_a_4721_, 1);
lean_dec(v_unused_4750_);
v___x_4727_ = v_a_4721_;
v_isShared_4728_ = v_isSharedCheck_4749_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_fst_4725_);
lean_dec(v_a_4721_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4749_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
if (lean_obj_tag(v_fst_4725_) == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4732_; 
lean_del_object(v___x_4723_);
v___x_4729_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4730_ = l_Lean_MessageData_ofName(v___x_4714_);
lean_inc_ref(v___x_4730_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set_tag(v___x_4727_, 7);
lean_ctor_set(v___x_4727_, 1, v___x_4730_);
lean_ctor_set(v___x_4727_, 0, v___x_4729_);
v___x_4732_ = v___x_4727_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4729_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4733_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4732_);
lean_ctor_set(v___x_4734_, 1, v___x_4733_);
v___x_4735_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4736_ = l_Lean_indentD(v___x_4735_);
v___x_4737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4734_);
lean_ctor_set(v___x_4737_, 1, v___x_4736_);
v___x_4738_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4737_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
lean_ctor_set(v___x_4740_, 1, v___x_4730_);
v___x_4741_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4742_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4743_;
}
}
else
{
lean_object* v_val_4745_; lean_object* v___x_4747_; 
lean_del_object(v___x_4727_);
lean_dec(v___x_4714_);
lean_dec(v_stx_2331_);
v_val_4745_ = lean_ctor_get(v_fst_4725_, 0);
lean_inc(v_val_4745_);
lean_dec_ref_known(v_fst_4725_, 1);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_val_4745_);
v___x_4747_ = v___x_4723_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_val_4745_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
lean_dec(v___x_4714_);
lean_dec(v_stx_2331_);
v_a_4752_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4720_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4720_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
else
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; uint8_t v___x_4763_; 
v___x_4760_ = lean_unsigned_to_nat(1u);
v___x_4761_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4760_);
v___x_4762_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__92));
lean_inc(v___x_4761_);
v___x_4763_ = l_Lean_Syntax_isOfKind(v___x_4761_, v___x_4762_);
if (v___x_4763_ == 0)
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v_env_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
lean_dec(v___x_4761_);
lean_del_object(v___x_2395_);
lean_inc_n(v_stx_2331_, 2);
v___x_4764_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4765_ = lean_st_ref_get(v_a_2337_);
v_env_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc_ref(v_env_4766_);
lean_dec(v___x_4765_);
v___x_4767_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4768_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4767_, v_env_4766_, v___x_4764_);
v___x_4769_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4770_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4768_, v___x_4769_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4768_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4801_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4773_ = v___x_4770_;
v_isShared_4774_ = v_isSharedCheck_4801_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4770_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4801_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v_fst_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4799_; 
v_fst_4775_ = lean_ctor_get(v_a_4771_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v_a_4771_);
if (v_isSharedCheck_4799_ == 0)
{
lean_object* v_unused_4800_; 
v_unused_4800_ = lean_ctor_get(v_a_4771_, 1);
lean_dec(v_unused_4800_);
v___x_4777_ = v_a_4771_;
v_isShared_4778_ = v_isSharedCheck_4799_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_fst_4775_);
lean_dec(v_a_4771_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4799_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
if (lean_obj_tag(v_fst_4775_) == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4782_; 
lean_del_object(v___x_4773_);
v___x_4779_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4780_ = l_Lean_MessageData_ofName(v___x_4764_);
lean_inc_ref(v___x_4780_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set_tag(v___x_4777_, 7);
lean_ctor_set(v___x_4777_, 1, v___x_4780_);
lean_ctor_set(v___x_4777_, 0, v___x_4779_);
v___x_4782_ = v___x_4777_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4779_);
lean_ctor_set(v_reuseFailAlloc_4794_, 1, v___x_4780_);
v___x_4782_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4783_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4782_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4786_ = l_Lean_indentD(v___x_4785_);
v___x_4787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4784_);
lean_ctor_set(v___x_4787_, 1, v___x_4786_);
v___x_4788_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
lean_ctor_set(v___x_4790_, 1, v___x_4780_);
v___x_4791_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4790_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v___x_4793_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4792_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4793_;
}
}
else
{
lean_object* v_val_4795_; lean_object* v___x_4797_; 
lean_del_object(v___x_4777_);
lean_dec(v___x_4764_);
lean_dec(v_stx_2331_);
v_val_4795_ = lean_ctor_get(v_fst_4775_, 0);
lean_inc(v_val_4795_);
lean_dec_ref_known(v_fst_4775_, 1);
if (v_isShared_4774_ == 0)
{
lean_ctor_set(v___x_4773_, 0, v_val_4795_);
v___x_4797_ = v___x_4773_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_val_4795_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec(v___x_4764_);
lean_dec(v_stx_2331_);
v_a_4802_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4770_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4770_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_object* v___x_4810_; uint8_t v___x_4811_; 
v___x_4810_ = l_Lean_Syntax_getArg(v___x_4761_, v___x_4710_);
lean_dec(v___x_4761_);
lean_inc(v___x_4810_);
v___x_4811_ = l_Lean_Syntax_matchesNull(v___x_4810_, v___x_4760_);
if (v___x_4811_ == 0)
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v_env_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_dec(v___x_4810_);
lean_del_object(v___x_2395_);
lean_inc_n(v_stx_2331_, 2);
v___x_4812_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4813_ = lean_st_ref_get(v_a_2337_);
v_env_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc_ref(v_env_4814_);
lean_dec(v___x_4813_);
v___x_4815_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4816_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4815_, v_env_4814_, v___x_4812_);
v___x_4817_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4818_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4816_, v___x_4817_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4816_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4849_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4821_ = v___x_4818_;
v_isShared_4822_ = v_isSharedCheck_4849_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4818_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4849_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_fst_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4847_; 
v_fst_4823_ = lean_ctor_get(v_a_4819_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v_a_4819_);
if (v_isSharedCheck_4847_ == 0)
{
lean_object* v_unused_4848_; 
v_unused_4848_ = lean_ctor_get(v_a_4819_, 1);
lean_dec(v_unused_4848_);
v___x_4825_ = v_a_4819_;
v_isShared_4826_ = v_isSharedCheck_4847_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_fst_4823_);
lean_dec(v_a_4819_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4847_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
if (lean_obj_tag(v_fst_4823_) == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4830_; 
lean_del_object(v___x_4821_);
v___x_4827_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4828_ = l_Lean_MessageData_ofName(v___x_4812_);
lean_inc_ref(v___x_4828_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set_tag(v___x_4825_, 7);
lean_ctor_set(v___x_4825_, 1, v___x_4828_);
lean_ctor_set(v___x_4825_, 0, v___x_4827_);
v___x_4830_ = v___x_4825_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4827_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___x_4828_);
v___x_4830_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4831_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4834_ = l_Lean_indentD(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4832_);
lean_ctor_set(v___x_4835_, 1, v___x_4834_);
v___x_4836_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4835_);
lean_ctor_set(v___x_4837_, 1, v___x_4836_);
v___x_4838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
lean_ctor_set(v___x_4838_, 1, v___x_4828_);
v___x_4839_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
v___x_4841_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4840_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4841_;
}
}
else
{
lean_object* v_val_4843_; lean_object* v___x_4845_; 
lean_del_object(v___x_4825_);
lean_dec(v___x_4812_);
lean_dec(v_stx_2331_);
v_val_4843_ = lean_ctor_get(v_fst_4823_, 0);
lean_inc(v_val_4843_);
lean_dec_ref_known(v_fst_4823_, 1);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v_val_4843_);
v___x_4845_ = v___x_4821_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_val_4843_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec(v___x_4812_);
lean_dec(v_stx_2331_);
v_a_4850_ = lean_ctor_get(v___x_4818_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4818_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4818_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
if (v___x_2598_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4858_ = l_Lean_Syntax_getArg(v___x_4810_, v___x_4710_);
lean_dec(v___x_4810_);
v___x_4859_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__94));
v___x_4860_ = l_Lean_Syntax_isOfKind(v___x_4858_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v_env_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
lean_del_object(v___x_2395_);
lean_inc_n(v_stx_2331_, 2);
v___x_4861_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4862_ = lean_st_ref_get(v_a_2337_);
v_env_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc_ref(v_env_4863_);
lean_dec(v___x_4862_);
v___x_4864_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4865_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4864_, v_env_4863_, v___x_4861_);
v___x_4866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4867_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4865_, v___x_4866_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4865_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4898_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4898_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4898_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v_fst_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4896_; 
v_fst_4872_ = lean_ctor_get(v_a_4868_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v_a_4868_);
if (v_isSharedCheck_4896_ == 0)
{
lean_object* v_unused_4897_; 
v_unused_4897_ = lean_ctor_get(v_a_4868_, 1);
lean_dec(v_unused_4897_);
v___x_4874_ = v_a_4868_;
v_isShared_4875_ = v_isSharedCheck_4896_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_fst_4872_);
lean_dec(v_a_4868_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4896_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
if (lean_obj_tag(v_fst_4872_) == 0)
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4879_; 
lean_del_object(v___x_4870_);
v___x_4876_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4877_ = l_Lean_MessageData_ofName(v___x_4861_);
lean_inc_ref(v___x_4877_);
if (v_isShared_4875_ == 0)
{
lean_ctor_set_tag(v___x_4874_, 7);
lean_ctor_set(v___x_4874_, 1, v___x_4877_);
lean_ctor_set(v___x_4874_, 0, v___x_4876_);
v___x_4879_ = v___x_4874_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4891_, 1, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4880_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4883_ = l_Lean_indentD(v___x_4882_);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4881_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4884_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v___x_4877_);
v___x_4888_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4887_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4889_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4890_;
}
}
else
{
lean_object* v_val_4892_; lean_object* v___x_4894_; 
lean_del_object(v___x_4874_);
lean_dec(v___x_4861_);
lean_dec(v_stx_2331_);
v_val_4892_ = lean_ctor_get(v_fst_4872_, 0);
lean_inc(v_val_4892_);
lean_dec_ref_known(v_fst_4872_, 1);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v_val_4892_);
v___x_4894_ = v___x_4870_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_val_4892_);
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
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_dec(v___x_4861_);
lean_dec(v_stx_2331_);
v_a_4899_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4867_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4867_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2397_;
}
}
else
{
lean_dec(v___x_4810_);
lean_dec(v_stx_2331_);
goto v___jp_2397_;
}
}
}
}
}
v___jp_2601_:
{
if (v___x_2600_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2608_ = lean_unsigned_to_nat(2u);
v___x_2609_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2608_);
v___x_2610_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2611_ = l_Lean_Syntax_isOfKind(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_env_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2612_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2613_ = lean_st_ref_get(v___y_2607_);
v_env_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_ref(v_env_2614_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2616_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2615_, v_env_2614_, v___x_2612_);
v___x_2617_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2618_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2616_, v___x_2617_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___x_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2649_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2649_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2649_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v_fst_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2647_; 
v_fst_2623_ = lean_ctor_get(v_a_2619_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_a_2619_, 1);
lean_dec(v_unused_2648_);
v___x_2625_ = v_a_2619_;
v_isShared_2626_ = v_isSharedCheck_2647_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_fst_2623_);
lean_dec(v_a_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2647_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
if (lean_obj_tag(v_fst_2623_) == 0)
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_del_object(v___x_2621_);
v___x_2627_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2628_ = l_Lean_MessageData_ofName(v___x_2612_);
lean_inc_ref(v___x_2628_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 7);
lean_ctor_set(v___x_2625_, 1, v___x_2628_);
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2631_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2634_ = l_Lean_indentD(v___x_2633_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2632_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2628_);
v___x_2639_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2640_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2641_;
}
}
else
{
lean_object* v_val_2643_; lean_object* v___x_2645_; 
lean_del_object(v___x_2625_);
lean_dec(v___x_2612_);
lean_dec(v_stx_2331_);
v_val_2643_ = lean_ctor_get(v_fst_2623_, 0);
lean_inc(v_val_2643_);
lean_dec_ref_known(v_fst_2623_, 1);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v_val_2643_);
v___x_2645_ = v___x_2621_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_val_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v___x_2612_);
lean_dec(v_stx_2331_);
v_a_2650_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2618_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2618_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
v___y_2358_ = v___y_2604_;
v___y_2359_ = v___y_2605_;
v___y_2360_ = v___y_2607_;
v___y_2361_ = v___y_2603_;
v___y_2362_ = v___y_2602_;
v___y_2363_ = v___y_2606_;
goto v___jp_2357_;
}
}
else
{
v___y_2358_ = v___y_2604_;
v___y_2359_ = v___y_2605_;
v___y_2360_ = v___y_2607_;
v___y_2361_ = v___y_2603_;
v___y_2362_ = v___y_2602_;
v___y_2363_ = v___y_2606_;
goto v___jp_2357_;
}
}
}
else
{
lean_del_object(v___x_2395_);
if (v___x_2545_ == 0)
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; uint8_t v___x_4910_; 
v___x_4907_ = lean_unsigned_to_nat(1u);
v___x_4908_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4907_);
v___x_4909_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_4910_ = l_Lean_Syntax_isOfKind(v___x_4908_, v___x_4909_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v_env_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4911_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4912_ = lean_st_ref_get(v_a_2337_);
v_env_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc_ref(v_env_4913_);
lean_dec(v___x_4912_);
v___x_4914_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4915_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4914_, v_env_4913_, v___x_4911_);
v___x_4916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4917_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4915_, v___x_4916_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4915_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4948_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4948_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4948_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v_fst_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4946_; 
v_fst_4922_ = lean_ctor_get(v_a_4918_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_a_4918_);
if (v_isSharedCheck_4946_ == 0)
{
lean_object* v_unused_4947_; 
v_unused_4947_ = lean_ctor_get(v_a_4918_, 1);
lean_dec(v_unused_4947_);
v___x_4924_ = v_a_4918_;
v_isShared_4925_ = v_isSharedCheck_4946_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_fst_4922_);
lean_dec(v_a_4918_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4946_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
if (lean_obj_tag(v_fst_4922_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4929_; 
lean_del_object(v___x_4920_);
v___x_4926_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4927_ = l_Lean_MessageData_ofName(v___x_4911_);
lean_inc_ref(v___x_4927_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set_tag(v___x_4924_, 7);
lean_ctor_set(v___x_4924_, 1, v___x_4927_);
lean_ctor_set(v___x_4924_, 0, v___x_4926_);
v___x_4929_ = v___x_4924_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4926_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v___x_4927_);
v___x_4929_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4930_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4929_);
lean_ctor_set(v___x_4931_, 1, v___x_4930_);
v___x_4932_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4933_ = l_Lean_indentD(v___x_4932_);
v___x_4934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4931_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4934_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4936_);
lean_ctor_set(v___x_4937_, 1, v___x_4927_);
v___x_4938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4937_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4939_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4940_;
}
}
else
{
lean_object* v_val_4942_; lean_object* v___x_4944_; 
lean_del_object(v___x_4924_);
lean_dec(v___x_4911_);
lean_dec(v_stx_2331_);
v_val_4942_ = lean_ctor_get(v_fst_4922_, 0);
lean_inc(v_val_4942_);
lean_dec_ref_known(v_fst_4922_, 1);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v_val_4942_);
v___x_4944_ = v___x_4920_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_val_4942_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v___x_4911_);
lean_dec(v_stx_2331_);
v_a_4949_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4917_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4917_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
goto v___jp_2546_;
}
}
else
{
goto v___jp_2546_;
}
}
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; 
lean_del_object(v___x_2395_);
v___x_4957_ = lean_unsigned_to_nat(1u);
v___x_4958_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_4957_);
v___x_4959_ = l_Lean_Syntax_isNone(v___x_4958_);
if (v___x_4959_ == 0)
{
uint8_t v___x_4960_; 
v___x_4960_ = l_Lean_Syntax_matchesNull(v___x_4958_, v___x_4957_);
if (v___x_4960_ == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v_env_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
lean_inc_n(v_stx_2331_, 2);
v___x_4961_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_4962_ = lean_st_ref_get(v_a_2337_);
v_env_4963_ = lean_ctor_get(v___x_4962_, 0);
lean_inc_ref(v_env_4963_);
lean_dec(v___x_4962_);
v___x_4964_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4965_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4964_, v_env_4963_, v___x_4961_);
v___x_4966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4967_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_4965_, v___x_4966_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_4965_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4998_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_4998_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4998_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v_fst_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4996_; 
v_fst_4972_ = lean_ctor_get(v_a_4968_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_a_4968_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v_a_4968_, 1);
lean_dec(v_unused_4997_);
v___x_4974_ = v_a_4968_;
v_isShared_4975_ = v_isSharedCheck_4996_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_fst_4972_);
lean_dec(v_a_4968_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4996_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
if (lean_obj_tag(v_fst_4972_) == 0)
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4979_; 
lean_del_object(v___x_4970_);
v___x_4976_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4977_ = l_Lean_MessageData_ofName(v___x_4961_);
lean_inc_ref(v___x_4977_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set_tag(v___x_4974_, 7);
lean_ctor_set(v___x_4974_, 1, v___x_4977_);
lean_ctor_set(v___x_4974_, 0, v___x_4976_);
v___x_4979_ = v___x_4974_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4976_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v___x_4977_);
v___x_4979_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4980_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_4983_ = l_Lean_indentD(v___x_4982_);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4981_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4986_, 0, v___x_4984_);
lean_ctor_set(v___x_4986_, 1, v___x_4985_);
v___x_4987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v___x_4977_);
v___x_4988_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___x_4987_);
lean_ctor_set(v___x_4989_, 1, v___x_4988_);
v___x_4990_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4989_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_4990_;
}
}
else
{
lean_object* v_val_4992_; lean_object* v___x_4994_; 
lean_del_object(v___x_4974_);
lean_dec(v___x_4961_);
lean_dec(v_stx_2331_);
v_val_4992_ = lean_ctor_get(v_fst_4972_, 0);
lean_inc(v_val_4992_);
lean_dec_ref_known(v_fst_4972_, 1);
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 0, v_val_4992_);
v___x_4994_ = v___x_4970_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_val_4992_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec(v___x_4961_);
lean_dec(v_stx_2331_);
v_a_4999_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4967_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4967_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
else
{
v___y_2488_ = v_a_2332_;
v___y_2489_ = v_a_2333_;
v___y_2490_ = v_a_2334_;
v___y_2491_ = v_a_2335_;
v___y_2492_ = v_a_2336_;
v___y_2493_ = v_a_2337_;
goto v___jp_2487_;
}
}
else
{
lean_dec(v___x_4958_);
v___y_2488_ = v_a_2332_;
v___y_2489_ = v_a_2333_;
v___y_2490_ = v_a_2334_;
v___y_2491_ = v_a_2335_;
v___y_2492_ = v_a_2336_;
v___y_2493_ = v_a_2337_;
goto v___jp_2487_;
}
}
v___jp_2546_:
{
if (v___x_2545_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2547_ = lean_unsigned_to_nat(2u);
v___x_2548_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2550_ = l_Lean_Syntax_isOfKind(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_env_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2551_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2552_ = lean_st_ref_get(v_a_2337_);
v_env_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref(v_env_2553_);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2555_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2554_, v_env_2553_, v___x_2551_);
v___x_2556_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2557_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2555_, v___x_2556_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_2555_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2588_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2588_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v_fst_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2586_; 
v_fst_2562_ = lean_ctor_get(v_a_2558_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2558_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v_a_2558_, 1);
lean_dec(v_unused_2587_);
v___x_2564_ = v_a_2558_;
v_isShared_2565_ = v_isSharedCheck_2586_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_fst_2562_);
lean_dec(v_a_2558_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2586_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
if (lean_obj_tag(v_fst_2562_) == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_del_object(v___x_2560_);
v___x_2566_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2567_ = l_Lean_MessageData_ofName(v___x_2551_);
lean_inc_ref(v___x_2567_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 7);
lean_ctor_set(v___x_2564_, 1, v___x_2567_);
lean_ctor_set(v___x_2564_, 0, v___x_2566_);
v___x_2569_ = v___x_2564_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2570_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2573_ = l_Lean_indentD(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2567_);
v___x_2578_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2579_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2580_;
}
}
else
{
lean_object* v_val_2582_; lean_object* v___x_2584_; 
lean_del_object(v___x_2564_);
lean_dec(v___x_2551_);
lean_dec(v_stx_2331_);
v_val_2582_ = lean_ctor_get(v_fst_2562_, 0);
lean_inc(v_val_2582_);
lean_dec_ref_known(v_fst_2562_, 1);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v_val_2582_);
v___x_2584_ = v___x_2560_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_val_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v___x_2551_);
lean_dec(v_stx_2331_);
v_a_2589_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2557_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2557_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2402_;
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2402_;
}
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
lean_del_object(v___x_2395_);
v___x_5007_ = lean_unsigned_to_nat(1u);
v___x_5008_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_5007_);
lean_dec(v_stx_2331_);
v___x_5009_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_5008_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_5009_;
}
v___jp_2430_:
{
if (v___x_2429_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2437_ = lean_unsigned_to_nat(3u);
v___x_2438_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2440_ = l_Lean_Syntax_isOfKind(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_env_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2441_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2442_ = lean_st_ref_get(v___y_2431_);
v_env_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc_ref(v_env_2443_);
lean_dec(v___x_2442_);
v___x_2444_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2445_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2444_, v_env_2443_, v___x_2441_);
v___x_2446_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2447_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2445_, v___x_2446_, v___y_2436_, v___y_2434_, v___y_2435_, v___y_2432_, v___y_2433_, v___y_2431_);
lean_dec(v___x_2445_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2478_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2478_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2478_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2476_; 
v_fst_2452_ = lean_ctor_get(v_a_2448_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_a_2448_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v_a_2448_, 1);
lean_dec(v_unused_2477_);
v___x_2454_ = v_a_2448_;
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_fst_2452_);
lean_dec(v_a_2448_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
if (lean_obj_tag(v_fst_2452_) == 0)
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
lean_del_object(v___x_2450_);
v___x_2456_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2457_ = l_Lean_MessageData_ofName(v___x_2441_);
lean_inc_ref(v___x_2457_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set_tag(v___x_2454_, 7);
lean_ctor_set(v___x_2454_, 1, v___x_2457_);
lean_ctor_set(v___x_2454_, 0, v___x_2456_);
v___x_2459_ = v___x_2454_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2460_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2463_ = l_Lean_indentD(v___x_2462_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2461_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2464_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v___x_2457_);
v___x_2468_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2469_, v___y_2436_, v___y_2434_, v___y_2435_, v___y_2432_, v___y_2433_, v___y_2431_);
return v___x_2470_;
}
}
else
{
lean_object* v_val_2472_; lean_object* v___x_2474_; 
lean_del_object(v___x_2454_);
lean_dec(v___x_2441_);
lean_dec(v_stx_2331_);
v_val_2472_ = lean_ctor_get(v_fst_2452_, 0);
lean_inc(v_val_2472_);
lean_dec_ref_known(v_fst_2452_, 1);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_val_2472_);
v___x_2474_ = v___x_2450_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_val_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v___x_2441_);
lean_dec(v_stx_2331_);
v_a_2479_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2447_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2447_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2378_;
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_2378_;
}
}
v___jp_2487_:
{
if (v___x_2429_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = lean_unsigned_to_nat(2u);
v___x_2495_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2494_);
v___x_2496_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2497_ = l_Lean_Syntax_isOfKind(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_env_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_inc_n(v_stx_2331_, 2);
v___x_2498_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_2499_ = lean_st_ref_get(v___y_2493_);
v_env_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_ref(v_env_2500_);
lean_dec(v___x_2499_);
v___x_2501_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2502_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2501_, v_env_2500_, v___x_2498_);
v___x_2503_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2504_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_2502_, v___x_2503_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___x_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2535_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2535_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2535_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v_fst_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2533_; 
v_fst_2509_ = lean_ctor_get(v_a_2505_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2505_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v_a_2505_, 1);
lean_dec(v_unused_2534_);
v___x_2511_ = v_a_2505_;
v_isShared_2512_ = v_isSharedCheck_2533_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_fst_2509_);
lean_dec(v_a_2505_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2533_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
if (lean_obj_tag(v_fst_2509_) == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_del_object(v___x_2507_);
v___x_2513_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2514_ = l_Lean_MessageData_ofName(v___x_2498_);
lean_inc_ref(v___x_2514_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 7);
lean_ctor_set(v___x_2511_, 1, v___x_2514_);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2517_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_2520_ = l_Lean_indentD(v___x_2519_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2518_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2514_);
v___x_2525_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2526_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2527_;
}
}
else
{
lean_object* v_val_2529_; lean_object* v___x_2531_; 
lean_del_object(v___x_2511_);
lean_dec(v___x_2498_);
lean_dec(v_stx_2331_);
v_val_2529_ = lean_ctor_get(v_fst_2509_, 0);
lean_inc(v_val_2529_);
lean_dec_ref_known(v_fst_2509_, 1);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v_val_2529_);
v___x_2531_ = v___x_2507_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_val_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v___x_2498_);
lean_dec(v_stx_2331_);
v_a_2536_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2504_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2504_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
v___y_2431_ = v___y_2493_;
v___y_2432_ = v___y_2491_;
v___y_2433_ = v___y_2492_;
v___y_2434_ = v___y_2489_;
v___y_2435_ = v___y_2490_;
v___y_2436_ = v___y_2488_;
goto v___jp_2430_;
}
}
else
{
v___y_2431_ = v___y_2493_;
v___y_2432_ = v___y_2491_;
v___y_2433_ = v___y_2492_;
v___y_2434_ = v___y_2489_;
v___y_2435_ = v___y_2490_;
v___y_2436_ = v___y_2488_;
goto v___jp_2430_;
}
}
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
lean_del_object(v___x_2395_);
v___x_5010_ = lean_unsigned_to_nat(0u);
v___x_5011_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_5010_);
lean_dec(v_stx_2331_);
v___x_5012_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_5011_);
if (lean_obj_tag(v___x_5012_) == 1)
{
lean_object* v_val_5013_; lean_object* v_snd_5014_; lean_object* v_body_5015_; lean_object* v___x_5016_; 
v_val_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_val_5013_);
lean_dec_ref_known(v___x_5012_, 1);
v_snd_5014_ = lean_ctor_get(v_val_5013_, 1);
lean_inc(v_snd_5014_);
lean_dec(v_val_5013_);
v_body_5015_ = lean_ctor_get(v_snd_5014_, 1);
lean_inc(v_body_5015_);
lean_dec(v_snd_5014_);
v___x_5016_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_5015_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5037_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5019_ = v___x_5016_;
v_isShared_5020_ = v_isSharedCheck_5037_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5016_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5037_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
uint8_t v_breaks_5021_; uint8_t v_continues_5022_; uint8_t v_returnsEarly_5023_; lean_object* v_reassigns_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5035_; 
v_breaks_5021_ = lean_ctor_get_uint8(v_a_5017_, sizeof(void*)*2);
v_continues_5022_ = lean_ctor_get_uint8(v_a_5017_, sizeof(void*)*2 + 1);
v_returnsEarly_5023_ = lean_ctor_get_uint8(v_a_5017_, sizeof(void*)*2 + 2);
v_reassigns_5024_ = lean_ctor_get(v_a_5017_, 1);
v_isSharedCheck_5035_ = !lean_is_exclusive(v_a_5017_);
if (v_isSharedCheck_5035_ == 0)
{
lean_object* v_unused_5036_; 
v_unused_5036_ = lean_ctor_get(v_a_5017_, 0);
lean_dec(v_unused_5036_);
v___x_5026_ = v_a_5017_;
v_isShared_5027_ = v_isSharedCheck_5035_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_reassigns_5024_);
lean_dec(v_a_5017_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5035_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5028_ = lean_unsigned_to_nat(1u);
if (v_isShared_5027_ == 0)
{
lean_ctor_set(v___x_5026_, 0, v___x_5028_);
v___x_5030_ = v___x_5026_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5028_);
lean_ctor_set(v_reuseFailAlloc_5034_, 1, v_reassigns_5024_);
lean_ctor_set_uint8(v_reuseFailAlloc_5034_, sizeof(void*)*2, v_breaks_5021_);
lean_ctor_set_uint8(v_reuseFailAlloc_5034_, sizeof(void*)*2 + 1, v_continues_5022_);
lean_ctor_set_uint8(v_reuseFailAlloc_5034_, sizeof(void*)*2 + 2, v_returnsEarly_5023_);
v___x_5030_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5032_; 
lean_ctor_set_uint8(v___x_5030_, sizeof(void*)*2 + 3, v___x_2425_);
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 0, v___x_5030_);
v___x_5032_ = v___x_5019_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5030_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
else
{
return v___x_5016_;
}
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
lean_dec(v___x_5012_);
v___x_5038_ = lean_unsigned_to_nat(1u);
v___x_5039_ = l_Lean_NameSet_empty;
v___x_5040_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5040_, 0, v___x_5038_);
lean_ctor_set(v___x_5040_, 1, v___x_5039_);
lean_ctor_set_uint8(v___x_5040_, sizeof(void*)*2, v___x_2425_);
lean_ctor_set_uint8(v___x_5040_, sizeof(void*)*2 + 1, v___x_2425_);
lean_ctor_set_uint8(v___x_5040_, sizeof(void*)*2 + 2, v___x_2425_);
lean_ctor_set_uint8(v___x_5040_, sizeof(void*)*2 + 3, v___x_2425_);
v___x_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5041_, 0, v___x_5040_);
return v___x_5041_;
}
}
}
else
{
lean_object* v___x_5042_; lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
lean_del_object(v___x_2395_);
v___x_5042_ = lean_unsigned_to_nat(0u);
v___x_5047_ = lean_unsigned_to_nat(1u);
v___x_5048_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_5047_);
v___x_5049_ = l_Lean_Syntax_isNone(v___x_5048_);
if (v___x_5049_ == 0)
{
uint8_t v___x_5050_; 
v___x_5050_ = l_Lean_Syntax_matchesNull(v___x_5048_, v___x_5047_);
if (v___x_5050_ == 0)
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v_env_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
lean_inc_n(v_stx_2331_, 2);
v___x_5051_ = l_Lean_Syntax_getKind(v_stx_2331_);
v___x_5052_ = lean_st_ref_get(v_a_2337_);
v_env_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc_ref(v_env_5053_);
lean_dec(v___x_5052_);
v___x_5054_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_5055_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_5054_, v_env_5053_, v___x_5051_);
v___x_5056_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_5057_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2331_, v___x_5055_, v___x_5056_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v___x_5055_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5088_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5060_ = v___x_5057_;
v_isShared_5061_ = v_isSharedCheck_5088_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5057_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5088_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v_fst_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5086_; 
v_fst_5062_ = lean_ctor_get(v_a_5058_, 0);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_a_5058_);
if (v_isSharedCheck_5086_ == 0)
{
lean_object* v_unused_5087_; 
v_unused_5087_ = lean_ctor_get(v_a_5058_, 1);
lean_dec(v_unused_5087_);
v___x_5064_ = v_a_5058_;
v_isShared_5065_ = v_isSharedCheck_5086_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_fst_5062_);
lean_dec(v_a_5058_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5086_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
if (lean_obj_tag(v_fst_5062_) == 0)
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5069_; 
lean_del_object(v___x_5060_);
v___x_5066_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_5067_ = l_Lean_MessageData_ofName(v___x_5051_);
lean_inc_ref(v___x_5067_);
if (v_isShared_5065_ == 0)
{
lean_ctor_set_tag(v___x_5064_, 7);
lean_ctor_set(v___x_5064_, 1, v___x_5067_);
lean_ctor_set(v___x_5064_, 0, v___x_5066_);
v___x_5069_ = v___x_5064_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5066_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5070_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_5071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5069_);
lean_ctor_set(v___x_5071_, 1, v___x_5070_);
v___x_5072_ = l_Lean_MessageData_ofSyntax(v_stx_2331_);
v___x_5073_ = l_Lean_indentD(v___x_5072_);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5071_);
lean_ctor_set(v___x_5074_, 1, v___x_5073_);
v___x_5075_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
lean_ctor_set(v___x_5077_, 1, v___x_5067_);
v___x_5078_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_5079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5079_, 0, v___x_5077_);
lean_ctor_set(v___x_5079_, 1, v___x_5078_);
v___x_5080_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_5079_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_5080_;
}
}
else
{
lean_object* v_val_5082_; lean_object* v___x_5084_; 
lean_del_object(v___x_5064_);
lean_dec(v___x_5051_);
lean_dec(v_stx_2331_);
v_val_5082_ = lean_ctor_get(v_fst_5062_, 0);
lean_inc(v_val_5082_);
lean_dec_ref_known(v_fst_5062_, 1);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 0, v_val_5082_);
v___x_5084_ = v___x_5060_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_val_5082_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
lean_dec(v___x_5051_);
lean_dec(v_stx_2331_);
v_a_5089_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5057_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5057_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
else
{
lean_dec(v_stx_2331_);
goto v___jp_5043_;
}
}
else
{
lean_dec(v___x_5048_);
lean_dec(v_stx_2331_);
goto v___jp_5043_;
}
v___jp_5043_:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5044_ = l_Lean_NameSet_empty;
v___x_5045_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5045_, 0, v___x_5042_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2, v___x_2423_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 1, v___x_2423_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 2, v___x_2421_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*2 + 3, v___x_2421_);
v___x_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5045_);
return v___x_5046_;
}
}
}
else
{
lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
lean_del_object(v___x_2395_);
lean_dec(v_stx_2331_);
v___x_5097_ = lean_unsigned_to_nat(0u);
v___x_5098_ = l_Lean_NameSet_empty;
v___x_5099_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
lean_ctor_set_uint8(v___x_5099_, sizeof(void*)*2, v___x_2420_);
lean_ctor_set_uint8(v___x_5099_, sizeof(void*)*2 + 1, v___x_2421_);
lean_ctor_set_uint8(v___x_5099_, sizeof(void*)*2 + 2, v___x_2420_);
lean_ctor_set_uint8(v___x_5099_, sizeof(void*)*2 + 3, v___x_2421_);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
return v___x_5100_;
}
}
else
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
lean_del_object(v___x_2395_);
lean_dec(v_stx_2331_);
v___x_5101_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__95);
v___x_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
return v___x_5102_;
}
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2398_);
v___x_2400_ = v___x_2395_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
v___jp_2402_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
return v___x_2404_;
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec(v_stx_2331_);
v_a_5104_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_2392_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_2392_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
v___jp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2340_, v_bodyInfo_2341_);
v___x_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
v___jp_2344_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2353_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___y_2350_);
v___x_2356_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2353_, v___x_2354_, v___x_2355_, v___y_2352_, v___y_2349_, v___y_2348_, v___y_2347_, v___y_2346_, v___y_2351_, v___y_2345_);
return v___x_2356_;
}
v___jp_2357_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2364_ = lean_unsigned_to_nat(7u);
v___x_2365_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2364_);
v___x_2366_ = lean_unsigned_to_nat(8u);
v___x_2367_ = l_Lean_Syntax_getArg(v_stx_2331_, v___x_2366_);
lean_dec(v_stx_2331_);
v___x_2368_ = l_Lean_Syntax_getOptional_x3f(v___x_2367_);
lean_dec(v___x_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2369_; 
v___x_2369_ = lean_box(0);
v___y_2345_ = v___y_2360_;
v___y_2346_ = v___y_2359_;
v___y_2347_ = v___y_2358_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___x_2365_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v___x_2369_;
goto v___jp_2344_;
}
else
{
lean_object* v_val_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_val_2370_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2368_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_val_2370_);
lean_dec(v___x_2368_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_val_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
v___y_2345_ = v___y_2360_;
v___y_2346_ = v___y_2359_;
v___y_2347_ = v___y_2358_;
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___x_2365_;
v___y_2351_ = v___y_2363_;
v___y_2352_ = v___x_2375_;
goto v___jp_2344_;
}
}
}
}
v___jp_2378_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
v___jp_2381_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
v___jp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2385_, v_bodyInfo_2386_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_5112_, size_t v_sz_5113_, size_t v_i_5114_, lean_object* v_b_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
uint8_t v___x_5123_; 
v___x_5123_ = lean_usize_dec_lt(v_i_5114_, v_sz_5113_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
v___x_5124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5124_, 0, v_b_5115_);
return v___x_5124_;
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5126_; 
v_a_5125_ = lean_array_uget_borrowed(v_as_5112_, v_i_5114_);
lean_inc(v_a_5125_);
v___x_5126_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_5125_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___x_5128_; size_t v___x_5129_; size_t v___x_5130_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5126_, 1);
v___x_5128_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_5115_, v_a_5127_);
v___x_5129_ = ((size_t)1ULL);
v___x_5130_ = lean_usize_add(v_i_5114_, v___x_5129_);
v_i_5114_ = v___x_5130_;
v_b_5115_ = v___x_5128_;
goto _start;
}
else
{
lean_dec_ref(v_b_5115_);
return v___x_5126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_info_5140_; lean_object* v___x_5141_; size_t v_sz_5142_; size_t v___x_5143_; lean_object* v___x_5144_; 
v_info_5140_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_5141_ = l_Lean_Parser_Term_getDoElems(v_stx_5132_);
v_sz_5142_ = lean_array_size(v___x_5141_);
v___x_5143_ = ((size_t)0ULL);
v___x_5144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_5141_, v_sz_5142_, v___x_5143_, v_info_5140_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_);
lean_dec_ref(v___x_5141_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
lean_object* v_res_5162_; 
v_res_5162_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_5163_, lean_object* v_sz_5164_, lean_object* v_i_5165_, lean_object* v_b_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
size_t v_sz_boxed_5174_; size_t v_i_boxed_5175_; lean_object* v_res_5176_; 
v_sz_boxed_5174_ = lean_unbox_usize(v_sz_5164_);
lean_dec(v_sz_5164_);
v_i_boxed_5175_ = lean_unbox_usize(v_i_5165_);
lean_dec(v_i_5165_);
v_res_5176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_5163_, v_sz_boxed_5174_, v_i_boxed_5175_, v_b_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec_ref(v_as_5163_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_5177_, lean_object* v_sz_5178_, lean_object* v_i_5179_, lean_object* v_b_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
size_t v_sz_boxed_5188_; size_t v_i_boxed_5189_; lean_object* v_res_5190_; 
v_sz_boxed_5188_ = lean_unbox_usize(v_sz_5178_);
lean_dec(v_sz_5178_);
v_i_boxed_5189_ = lean_unbox_usize(v_i_5179_);
lean_dec(v_i_5179_);
v_res_5190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_5177_, v_sz_boxed_5188_, v_i_boxed_5189_, v_b_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec_ref(v_as_5177_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_5191_, lean_object* v_as_5192_, lean_object* v_sz_5193_, lean_object* v_i_5194_, lean_object* v_b_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
uint8_t v___x_178299__boxed_5203_; size_t v_sz_boxed_5204_; size_t v_i_boxed_5205_; lean_object* v_res_5206_; 
v___x_178299__boxed_5203_ = lean_unbox(v___x_5191_);
v_sz_boxed_5204_ = lean_unbox_usize(v_sz_5193_);
lean_dec(v_sz_5193_);
v_i_boxed_5205_ = lean_unbox_usize(v_i_5194_);
lean_dec(v_i_5194_);
v_res_5206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_178299__boxed_5203_, v_as_5192_, v_sz_boxed_5204_, v_i_boxed_5205_, v_b_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec_ref(v_as_5192_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_5207_, lean_object* v_as_5208_, lean_object* v_sz_5209_, lean_object* v_i_5210_, lean_object* v_b_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
uint8_t v___x_178346__boxed_5219_; size_t v_sz_boxed_5220_; size_t v_i_boxed_5221_; lean_object* v_res_5222_; 
v___x_178346__boxed_5219_ = lean_unbox(v___x_5207_);
v_sz_boxed_5220_ = lean_unbox_usize(v_sz_5209_);
lean_dec(v_sz_5209_);
v_i_boxed_5221_ = lean_unbox_usize(v_i_5210_);
lean_dec(v_i_5210_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_178346__boxed_5219_, v_as_5208_, v_sz_boxed_5220_, v_i_boxed_5221_, v_b_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec_ref(v_as_5208_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5223_, lean_object* v_rhs_x3f_5224_, lean_object* v_otherwise_x3f_5225_, lean_object* v_body_x3f_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5223_, v_rhs_x3f_5224_, v_otherwise_x3f_5225_, v_body_x3f_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5235_, lean_object* v_sz_5236_, lean_object* v_i_5237_, lean_object* v_b_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
size_t v_sz_boxed_5246_; size_t v_i_boxed_5247_; lean_object* v_res_5248_; 
v_sz_boxed_5246_ = lean_unbox_usize(v_sz_5236_);
lean_dec(v_sz_5236_);
v_i_boxed_5247_ = lean_unbox_usize(v_i_5237_);
lean_dec(v_i_5237_);
v_res_5248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5235_, v_sz_boxed_5246_, v_i_boxed_5247_, v_b_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec_ref(v_as_5235_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5249_, lean_object* v_decl_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_){
_start:
{
uint8_t v_reassignment_boxed_5258_; lean_object* v_res_5259_; 
v_reassignment_boxed_5258_ = lean_unbox(v_reassignment_5249_);
v_res_5259_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5258_, v_decl_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_);
lean_dec(v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5252_);
lean_dec_ref(v_a_5251_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec_ref(v___y_5279_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5287_, lean_object* v_ref_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5288_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5297_, lean_object* v_ref_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5297_, v_ref_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5307_, lean_object* v_x_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5317_, lean_object* v_x_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v_res_5326_; 
v_res_5326_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5317_, v_x_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
return v_res_5326_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5327_, lean_object* v_as_5328_, lean_object* v_as_x27_5329_, lean_object* v_b_5330_, lean_object* v_a_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5327_, v_as_x27_5329_, v_b_5330_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5340_, lean_object* v_as_5341_, lean_object* v_as_x27_5342_, lean_object* v_b_5343_, lean_object* v_a_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5340_, v_as_5341_, v_as_x27_5342_, v_b_5343_, v_a_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v_as_x27_5342_);
lean_dec(v_as_5341_);
return v_res_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5353_, lean_object* v_msg_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5363_, lean_object* v_msg_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5363_, v_msg_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
lean_dec(v___y_5368_);
lean_dec_ref(v___y_5367_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5373_, lean_object* v_msg_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5373_, v_msg_5374_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5383_, lean_object* v_msg_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5383_, v_msg_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5393_, lean_object* v_as_x27_5394_, lean_object* v_b_5395_, lean_object* v_a_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5394_, v_b_5395_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5405_, lean_object* v_as_x27_5406_, lean_object* v_b_5407_, lean_object* v_a_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v_res_5416_; 
v_res_5416_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5405_, v_as_x27_5406_, v_b_5407_, v_a_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v_as_x27_5406_);
lean_dec(v_as_5405_);
return v_res_5416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5417_, lean_object* v_ref_5418_, lean_object* v_msg_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5418_, v_msg_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5428_, lean_object* v_ref_5429_, lean_object* v_msg_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5428_, v_ref_5429_, v_msg_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v_ref_5429_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5439_, lean_object* v_macroStack_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
lean_object* v___x_5448_; 
v___x_5448_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5439_, v_macroStack_5440_, v___y_5445_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5449_, lean_object* v_macroStack_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5449_, v_macroStack_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5459_, lean_object* v_m_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5460_, v_a_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5463_, lean_object* v_m_5464_, lean_object* v_a_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5463_, v_m_5464_, v_a_5465_);
lean_dec(v_a_5465_);
lean_dec_ref(v_m_5464_);
return v_res_5466_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5467_, lean_object* v_x_5468_, lean_object* v_x_5469_){
_start:
{
uint8_t v___x_5470_; 
v___x_5470_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5468_, v_x_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5471_, lean_object* v_x_5472_, lean_object* v_x_5473_){
_start:
{
uint8_t v_res_5474_; lean_object* v_r_5475_; 
v_res_5474_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5471_, v_x_5472_, v_x_5473_);
lean_dec_ref(v_x_5473_);
lean_dec_ref(v_x_5472_);
v_r_5475_ = lean_box(v_res_5474_);
return v_r_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5476_, lean_object* v_a_5477_, lean_object* v_x_5478_){
_start:
{
lean_object* v___x_5479_; 
v___x_5479_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5477_, v_x_5478_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5480_, lean_object* v_a_5481_, lean_object* v_x_5482_){
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5480_, v_a_5481_, v_x_5482_);
lean_dec(v_x_5482_);
lean_dec(v_a_5481_);
return v_res_5483_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5484_, lean_object* v_x_5485_, size_t v_x_5486_, lean_object* v_x_5487_){
_start:
{
uint8_t v___x_5488_; 
v___x_5488_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5485_, v_x_5486_, v_x_5487_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5489_, lean_object* v_x_5490_, lean_object* v_x_5491_, lean_object* v_x_5492_){
_start:
{
size_t v_x_185485__boxed_5493_; uint8_t v_res_5494_; lean_object* v_r_5495_; 
v_x_185485__boxed_5493_ = lean_unbox_usize(v_x_5491_);
lean_dec(v_x_5491_);
v_res_5494_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5489_, v_x_5490_, v_x_185485__boxed_5493_, v_x_5492_);
lean_dec_ref(v_x_5492_);
lean_dec_ref(v_x_5490_);
v_r_5495_ = lean_box(v_res_5494_);
return v_r_5495_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5496_, lean_object* v_keys_5497_, lean_object* v_vals_5498_, lean_object* v_heq_5499_, lean_object* v_i_5500_, lean_object* v_k_5501_){
_start:
{
uint8_t v___x_5502_; 
v___x_5502_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5497_, v_i_5500_, v_k_5501_);
return v___x_5502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5503_, lean_object* v_keys_5504_, lean_object* v_vals_5505_, lean_object* v_heq_5506_, lean_object* v_i_5507_, lean_object* v_k_5508_){
_start:
{
uint8_t v_res_5509_; lean_object* v_r_5510_; 
v_res_5509_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5503_, v_keys_5504_, v_vals_5505_, v_heq_5506_, v_i_5507_, v_k_5508_);
lean_dec_ref(v_k_5508_);
lean_dec_ref(v_vals_5505_);
lean_dec_ref(v_keys_5504_);
v_r_5510_ = lean_box(v_res_5509_);
return v_r_5510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_){
_start:
{
lean_object* v___x_5519_; 
v___x_5519_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_, v_a_5517_);
return v___x_5519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_);
lean_dec(v_a_5526_);
lean_dec_ref(v_a_5525_);
lean_dec(v_a_5524_);
lean_dec_ref(v_a_5523_);
lean_dec(v_a_5522_);
lean_dec_ref(v_a_5521_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___x_5537_; 
v___x_5537_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_, lean_object* v_a_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
lean_dec(v_a_5544_);
lean_dec_ref(v_a_5543_);
lean_dec(v_a_5542_);
lean_dec_ref(v_a_5541_);
lean_dec(v_a_5540_);
lean_dec_ref(v_a_5539_);
return v_res_5546_;
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
