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
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 239, .m_capacity = 239, .m_length = 236, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `DoElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(118) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(126) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Do_InferControlInfo_0__Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(125) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
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
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doSkip"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InternalSyntax"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(117, 4, 119, 3, 13, 160, 149, 47)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value_aux_3),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value),LEAN_SCALAR_PTR_LITERAL(125, 157, 182, 149, 109, 63, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doAssertion"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value),LEAN_SCALAR_PTR_LITERAL(144, 179, 243, 245, 156, 230, 227, 142)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
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
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__77_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__79_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__81_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__83_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__85_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__87_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89;
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
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 1);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_box(1);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__2));
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_336_; 
v_head_313_ = lean_ctor_get(v_x_312_, 0);
v_tail_314_ = lean_ctor_get(v_x_312_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_312_);
if (v_isSharedCheck_336_ == 0)
{
v___x_316_ = v_x_312_;
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_tail_314_);
lean_inc(v_head_313_);
lean_dec(v_x_312_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_336_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v_before_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_334_; 
v_before_318_ = lean_ctor_get(v_head_313_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_head_313_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_head_313_, 1);
lean_dec(v_unused_335_);
v___x_320_ = v_head_313_;
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_before_318_);
lean_dec(v_head_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_334_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 7);
lean_ctor_set(v___x_320_, 1, v___x_322_);
lean_ctor_set(v___x_320_, 0, v_x_311_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_x_311_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_333_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__3);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 7);
lean_ctor_set(v___x_316_, 1, v___x_325_);
lean_ctor_set(v___x_316_, 0, v___x_324_);
v___x_327_ = v___x_316_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_332_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_MessageData_ofSyntax(v_before_318_);
v___x_329_ = l_Lean_indentD(v___x_328_);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_327_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v_x_311_ = v___x_330_;
v_x_312_ = v_tail_314_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(lean_object* v_opts_337_, lean_object* v_opt_338_){
_start:
{
lean_object* v_name_339_; lean_object* v_defValue_340_; lean_object* v_map_341_; lean_object* v___x_342_; 
v_name_339_ = lean_ctor_get(v_opt_338_, 0);
v_defValue_340_ = lean_ctor_get(v_opt_338_, 1);
v_map_341_ = lean_ctor_get(v_opts_337_, 0);
v___x_342_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_341_, v_name_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
uint8_t v___x_343_; 
v___x_343_ = lean_unbox(v_defValue_340_);
return v___x_343_;
}
else
{
lean_object* v_val_344_; 
v_val_344_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_344_);
lean_dec_ref_known(v___x_342_, 1);
if (lean_obj_tag(v_val_344_) == 1)
{
uint8_t v_v_345_; 
v_v_345_ = lean_ctor_get_uint8(v_val_344_, 0);
lean_dec_ref_known(v_val_344_, 0);
return v_v_345_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_val_344_);
v___x_346_ = lean_unbox(v_defValue_340_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19___boxed(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_opts_347_, v_opt_348_);
lean_dec_ref(v_opt_348_);
lean_dec_ref(v_opts_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__1));
v___x_355_ = l_Lean_MessageData_ofFormat(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(lean_object* v_msgData_356_, lean_object* v_macroStack_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_options_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_options_360_ = lean_ctor_get(v___y_358_, 1);
v___x_361_ = l_Lean_Elab_pp_macroStack;
v___x_362_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__19(v_options_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v_macroStack_357_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_msgData_356_);
return v___x_363_;
}
else
{
if (lean_obj_tag(v_macroStack_357_) == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_msgData_356_);
return v___x_364_;
}
else
{
lean_object* v_head_365_; lean_object* v_after_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_381_; 
v_head_365_ = lean_ctor_get(v_macroStack_357_, 0);
lean_inc(v_head_365_);
v_after_366_ = lean_ctor_get(v_head_365_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_head_365_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_head_365_, 0);
lean_dec(v_unused_382_);
v___x_368_ = v_head_365_;
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_after_366_);
lean_dec(v_head_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_381_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20___closed__0);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 7);
lean_ctor_set(v___x_368_, 1, v___x_370_);
lean_ctor_set(v___x_368_, 0, v_msgData_356_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_msgData_356_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_380_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_msgData_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_373_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___closed__2);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_MessageData_ofSyntax(v_after_366_);
v___x_376_ = l_Lean_indentD(v___x_375_);
v_msgData_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_377_, 0, v___x_374_);
lean_ctor_set(v_msgData_377_, 1, v___x_376_);
v___x_378_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11_spec__20(v_msgData_377_, v_macroStack_357_);
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg___boxed(lean_object* v_msgData_383_, lean_object* v_macroStack_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_383_, v_macroStack_384_, v___y_385_);
lean_dec_ref(v___y_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v_macroStack_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 4);
v___x_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_388_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
v_macroStack_399_ = lean_ctor_get(v___y_389_, 1);
v___x_400_ = l_Lean_Elab_getBetterRef(v_ref_396_, v_macroStack_399_);
lean_inc(v_macroStack_399_);
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_a_398_, v_macroStack_399_, v___y_393_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_400_);
lean_ctor_set(v___x_406_, 1, v_a_402_);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v_b_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_eq(v_i_421_, v_stop_422_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
v___x_425_ = lean_array_uget_borrowed(v_as_420_, v_i_421_);
lean_inc(v___x_425_);
v___x_426_ = l_Lean_NameSet_insert(v_b_423_, v___x_425_);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_421_, v___x_427_);
v_i_421_ = v___x_428_;
v_b_423_ = v___x_426_;
goto _start;
}
else
{
return v_b_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* v_as_430_, lean_object* v_i_431_, lean_object* v_stop_432_, lean_object* v_b_433_){
_start:
{
size_t v_i_boxed_434_; size_t v_stop_boxed_435_; lean_object* v_res_436_; 
v_i_boxed_434_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_stop_boxed_435_ = lean_unbox_usize(v_stop_432_);
lean_dec(v_stop_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v_as_430_, v_i_boxed_434_, v_stop_boxed_435_, v_b_433_);
lean_dec_ref(v_as_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t v_sz_437_, size_t v_i_438_, lean_object* v_bs_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_440_ == 0)
{
return v_bs_439_;
}
else
{
lean_object* v_v_441_; lean_object* v___x_442_; lean_object* v_bs_x27_443_; lean_object* v___x_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_v_441_ = lean_array_uget(v_bs_439_, v_i_438_);
v___x_442_ = lean_unsigned_to_nat(0u);
v_bs_x27_443_ = lean_array_uset(v_bs_439_, v_i_438_, v___x_442_);
v___x_444_ = l_Lean_TSyntax_getId(v_v_441_);
lean_dec(v_v_441_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_438_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_443_, v_i_438_, v___x_444_);
v_i_438_ = v___x_446_;
v_bs_439_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* v_sz_449_, lean_object* v_i_450_, lean_object* v_bs_451_){
_start:
{
size_t v_sz_boxed_452_; size_t v_i_boxed_453_; lean_object* v_res_454_; 
v_sz_boxed_452_ = lean_unbox_usize(v_sz_449_);
lean_dec(v_sz_449_);
v_i_boxed_453_ = lean_unbox_usize(v_i_450_);
lean_dec(v_i_450_);
v_res_454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_boxed_452_, v_i_boxed_453_, v_bs_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___closed__0);
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg___boxed(lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_bs_465_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v_bs_x27_469_; lean_object* v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v_bs_x27_469_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_468_);
v___x_470_ = lean_box(0);
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_464_, v___x_471_);
v___x_473_ = lean_array_uset(v_bs_x27_469_, v_i_464_, v___x_470_);
v_i_464_ = v___x_472_;
v_bs_465_ = v___x_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t v___x_481_, uint8_t v___x_482_, lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___y_488_; uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_492_ == 0)
{
lean_object* v_fst_493_; uint8_t v___x_494_; 
v_fst_493_ = lean_ctor_get(v_b_486_, 0);
v___x_494_ = lean_unbox(v_fst_493_);
if (v___x_494_ == 0)
{
lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_snd_495_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_504_);
v___x_497_ = v_b_486_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_dec(v_b_486_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_box(v___x_481_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_499_);
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_snd_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
v___y_488_ = v___x_501_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_snd_505_ = lean_ctor_get(v_b_486_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_b_486_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_b_486_, 0);
lean_dec(v_unused_516_);
v___x_507_ = v_b_486_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_dec(v_b_486_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
lean_inc(v___x_509_);
v___x_510_ = lean_array_push(v_snd_505_, v___x_509_);
v___x_511_ = lean_box(v___x_482_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_510_);
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_510_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_488_ = v___x_513_;
goto v___jp_487_;
}
}
}
}
else
{
return v_b_486_;
}
v___jp_487_:
{
size_t v___x_489_; size_t v___x_490_; 
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_484_, v___x_489_);
v_i_484_ = v___x_490_;
v_b_486_ = v___y_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* v___x_517_, lean_object* v___x_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_, lean_object* v_b_522_){
_start:
{
uint8_t v___x_163656__boxed_523_; uint8_t v___x_163657__boxed_524_; size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v___x_163656__boxed_523_ = lean_unbox(v___x_517_);
v___x_163657__boxed_524_ = lean_unbox(v___x_518_);
v_i_boxed_525_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_163656__boxed_523_, v___x_163657__boxed_524_, v_as_519_, v_i_boxed_525_, v_stop_boxed_526_, v_b_522_);
lean_dec_ref(v_as_519_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* v_env_528_, lean_object* v_declName_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_532_; lean_object* v_env_533_; lean_object* v___x_534_; uint8_t v___x_535_; uint8_t v___x_536_; 
v___x_532_ = 0;
v_env_533_ = l_Lean_Environment_setExporting(v_env_528_, v___x_532_);
lean_inc(v_declName_529_);
v___x_534_ = l_Lean_mkPrivateName(v_env_533_, v_declName_529_);
v___x_535_ = 1;
lean_inc_ref(v_env_533_);
v___x_536_ = l_Lean_Environment_contains(v_env_533_, v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = l_Lean_privateToUserName(v_declName_529_);
v___x_538_ = l_Lean_Environment_contains(v_env_533_, v___x_537_, v___x_535_);
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___y_531_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_env_533_);
lean_dec(v_declName_529_);
v___x_541_ = lean_box(v___x_536_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___y_531_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* v_env_543_, lean_object* v_declName_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(v_env_543_, v_declName_544_, v___y_545_, v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = l_Lean_maxRecDepthErrorMessage;
v___x_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__3);
v___x_556_ = l_Lean_MessageData_ofFormat(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__4);
v___x_558_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__2));
v___x_559_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* v_ref_560_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___closed__5);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_ref_560_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* v_ref_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_570_);
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v_a_570_);
lean_ctor_set(v___x_571_, 1, v___y_569_);
return v___x_571_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; 
v_a_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_572_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_572_);
lean_ctor_set(v___x_573_, 1, v___y_569_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_574_, v___y_575_);
lean_dec_ref(v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* v_env_577_, lean_object* v_stx_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_577_, v_stx_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
if (lean_obj_tag(v_a_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
v_a_583_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_581_, 0);
lean_dec(v_unused_592_);
v___x_585_ = v___x_581_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_587_);
v___x_589_ = v___x_585_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_a_583_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_val_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_621_; 
v_val_593_ = lean_ctor_get(v_a_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_595_ = v_a_582_;
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_val_593_);
lean_dec(v_a_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_621_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_snd_597_; 
v_snd_597_ = lean_ctor_get(v_val_593_, 1);
lean_inc(v_snd_597_);
lean_dec(v_val_593_);
if (lean_obj_tag(v_snd_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_del_object(v___x_595_);
v_a_598_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_581_, 2);
v_a_599_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_snd_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_snd_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_604_, v_a_598_);
lean_dec_ref(v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_620_; 
v_a_608_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_581_, 2);
v_a_609_ = lean_ctor_get(v_snd_597_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_snd_597_);
if (v_isSharedCheck_620_ == 0)
{
v___x_611_ = v_snd_597_;
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v_snd_597_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_620_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_a_609_);
v___x_614_ = v___x_595_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_618_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v___x_616_, v_a_608_);
lean_dec_ref(v___x_616_);
return v___x_617_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_622_ = lean_ctor_get(v___x_581_, 0);
v_a_623_ = lean_ctor_get(v___x_581_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_581_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_inc(v_a_622_);
lean_dec(v___x_581_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* v_env_631_, lean_object* v_stx_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(v_env_631_, v_stx_632_, v___y_633_, v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(lean_object* v_ref_636_, lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_toCold_645_; lean_object* v_options_646_; lean_object* v_currRecDepth_647_; lean_object* v_maxRecDepth_648_; lean_object* v_ref_649_; lean_object* v_currNamespace_650_; lean_object* v_openDecls_651_; lean_object* v_initHeartbeats_652_; lean_object* v_maxHeartbeats_653_; lean_object* v_currMacroScope_654_; uint8_t v_diag_655_; uint8_t v_suppressElabErrors_656_; lean_object* v_ref_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_toCold_645_ = lean_ctor_get(v___y_642_, 0);
v_options_646_ = lean_ctor_get(v___y_642_, 1);
v_currRecDepth_647_ = lean_ctor_get(v___y_642_, 2);
v_maxRecDepth_648_ = lean_ctor_get(v___y_642_, 3);
v_ref_649_ = lean_ctor_get(v___y_642_, 4);
v_currNamespace_650_ = lean_ctor_get(v___y_642_, 5);
v_openDecls_651_ = lean_ctor_get(v___y_642_, 6);
v_initHeartbeats_652_ = lean_ctor_get(v___y_642_, 7);
v_maxHeartbeats_653_ = lean_ctor_get(v___y_642_, 8);
v_currMacroScope_654_ = lean_ctor_get(v___y_642_, 9);
v_diag_655_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*10);
v_suppressElabErrors_656_ = lean_ctor_get_uint8(v___y_642_, sizeof(void*)*10 + 1);
v_ref_657_ = l_Lean_replaceRef(v_ref_636_, v_ref_649_);
lean_inc(v_currMacroScope_654_);
lean_inc(v_maxHeartbeats_653_);
lean_inc(v_initHeartbeats_652_);
lean_inc(v_openDecls_651_);
lean_inc(v_currNamespace_650_);
lean_inc(v_maxRecDepth_648_);
lean_inc(v_currRecDepth_647_);
lean_inc_ref(v_options_646_);
lean_inc_ref(v_toCold_645_);
v___x_658_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_658_, 0, v_toCold_645_);
lean_ctor_set(v___x_658_, 1, v_options_646_);
lean_ctor_set(v___x_658_, 2, v_currRecDepth_647_);
lean_ctor_set(v___x_658_, 3, v_maxRecDepth_648_);
lean_ctor_set(v___x_658_, 4, v_ref_657_);
lean_ctor_set(v___x_658_, 5, v_currNamespace_650_);
lean_ctor_set(v___x_658_, 6, v_openDecls_651_);
lean_ctor_set(v___x_658_, 7, v_initHeartbeats_652_);
lean_ctor_set(v___x_658_, 8, v_maxHeartbeats_653_);
lean_ctor_set(v___x_658_, 9, v_currMacroScope_654_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*10, v_diag_655_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*10 + 1, v_suppressElabErrors_656_);
v___x_659_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___x_658_, v___y_643_);
lean_dec_ref_known(v___x_658_, 10);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg___boxed(lean_object* v_ref_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_660_, v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v_ref_660_);
return v_res_669_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_670_; double v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_float_of_nat(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* v_cls_675_, lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_ref_682_; lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_728_; 
v_ref_682_ = lean_ctor_get(v___y_679_, 4);
v___x_683_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__10(v_msg_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_728_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_728_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_728_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v_traceState_689_; lean_object* v_env_690_; lean_object* v_nextMacroScope_691_; lean_object* v_ngen_692_; lean_object* v_auxDeclNGen_693_; lean_object* v_cache_694_; lean_object* v_messages_695_; lean_object* v_infoState_696_; lean_object* v_snapshotTasks_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_727_; 
v___x_688_ = lean_st_ref_take(v___y_680_);
v_traceState_689_ = lean_ctor_get(v___x_688_, 4);
v_env_690_ = lean_ctor_get(v___x_688_, 0);
v_nextMacroScope_691_ = lean_ctor_get(v___x_688_, 1);
v_ngen_692_ = lean_ctor_get(v___x_688_, 2);
v_auxDeclNGen_693_ = lean_ctor_get(v___x_688_, 3);
v_cache_694_ = lean_ctor_get(v___x_688_, 5);
v_messages_695_ = lean_ctor_get(v___x_688_, 6);
v_infoState_696_ = lean_ctor_get(v___x_688_, 7);
v_snapshotTasks_697_ = lean_ctor_get(v___x_688_, 8);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_727_ == 0)
{
v___x_699_ = v___x_688_;
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_snapshotTasks_697_);
lean_inc(v_infoState_696_);
lean_inc(v_messages_695_);
lean_inc(v_cache_694_);
lean_inc(v_traceState_689_);
lean_inc(v_auxDeclNGen_693_);
lean_inc(v_ngen_692_);
lean_inc(v_nextMacroScope_691_);
lean_inc(v_env_690_);
lean_dec(v___x_688_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint64_t v_tid_701_; lean_object* v_traces_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_726_; 
v_tid_701_ = lean_ctor_get_uint64(v_traceState_689_, sizeof(void*)*1);
v_traces_702_ = lean_ctor_get(v_traceState_689_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v_traceState_689_);
if (v_isSharedCheck_726_ == 0)
{
v___x_704_ = v_traceState_689_;
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_traces_702_);
lean_dec(v_traceState_689_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; double v___x_707_; uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0);
v___x_708_ = 0;
v___x_709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_710_, 0, v_cls_675_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_709_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3, v___x_707_);
lean_ctor_set_float(v___x_710_, sizeof(void*)*3 + 8, v___x_707_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*3 + 16, v___x_708_);
v___x_711_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__2));
v___x_712_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v_a_684_);
lean_ctor_set(v___x_712_, 2, v___x_711_);
lean_inc(v_ref_682_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_ref_682_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_traces_702_, v___x_713_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_714_);
v___x_716_ = v___x_704_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_714_);
lean_ctor_set_uint64(v_reuseFailAlloc_725_, sizeof(void*)*1, v_tid_701_);
v___x_716_ = v_reuseFailAlloc_725_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 4, v___x_716_);
v___x_718_ = v___x_699_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_env_690_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_nextMacroScope_691_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_ngen_692_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_auxDeclNGen_693_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_724_, 5, v_cache_694_);
lean_ctor_set(v_reuseFailAlloc_724_, 6, v_messages_695_);
lean_ctor_set(v_reuseFailAlloc_724_, 7, v_infoState_696_);
lean_ctor_set(v_reuseFailAlloc_724_, 8, v_snapshotTasks_697_);
v___x_718_ = v_reuseFailAlloc_724_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = lean_st_ref_put(v___y_680_, v___x_718_);
v___x_720_ = lean_box(0);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_720_);
v___x_722_ = v___x_686_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* v_cls_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_729_, v_msg_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* v_as_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
if (lean_obj_tag(v_as_740_) == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
else
{
lean_object* v_options_750_; uint8_t v_hasTrace_751_; 
v_options_750_ = lean_ctor_get(v___y_745_, 1);
v_hasTrace_751_ = lean_ctor_get_uint8(v_options_750_, sizeof(void*)*1);
if (v_hasTrace_751_ == 0)
{
lean_object* v_tail_752_; 
v_tail_752_ = lean_ctor_get(v_as_740_, 1);
lean_inc(v_tail_752_);
lean_dec_ref_known(v_as_740_, 2);
v_as_740_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v_head_754_; lean_object* v_toCold_755_; lean_object* v_tail_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v_inheritedTraceOptions_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_head_754_ = lean_ctor_get(v_as_740_, 0);
v_toCold_755_ = lean_ctor_get(v___y_745_, 0);
lean_inc(v_head_754_);
v_tail_756_ = lean_ctor_get(v_as_740_, 1);
lean_inc(v_tail_756_);
lean_dec_ref_known(v_as_740_, 2);
v_fst_757_ = lean_ctor_get(v_head_754_, 0);
lean_inc_n(v_fst_757_, 2);
v_snd_758_ = lean_ctor_get(v_head_754_, 1);
lean_inc(v_snd_758_);
lean_dec(v_head_754_);
v_inheritedTraceOptions_759_ = lean_ctor_get(v_toCold_755_, 4);
v___x_760_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_761_ = l_Lean_Name_append(v___x_760_, v_fst_757_);
v___x_762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_759_, v_options_750_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v_snd_758_);
lean_dec(v_fst_757_);
v_as_740_ = v_tail_756_;
goto _start;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_764_, 0, v_snd_758_);
v___x_765_ = l_Lean_MessageData_ofFormat(v___x_764_);
v___x_766_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_fst_757_, v___x_765_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_dec_ref_known(v___x_766_, 1);
v_as_740_ = v_tail_756_;
goto _start;
}
else
{
lean_dec(v_tail_756_);
return v___x_766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* v_as_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v_as_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(lean_object* v_a_777_, lean_object* v_x_778_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_box(0);
return v___x_779_;
}
else
{
lean_object* v_key_780_; lean_object* v_value_781_; lean_object* v_tail_782_; uint8_t v___x_783_; 
v_key_780_ = lean_ctor_get(v_x_778_, 0);
v_value_781_ = lean_ctor_get(v_x_778_, 1);
v_tail_782_ = lean_ctor_get(v_x_778_, 2);
v___x_783_ = lean_name_eq(v_key_780_, v_a_777_);
if (v___x_783_ == 0)
{
v_x_778_ = v_tail_782_;
goto _start;
}
else
{
lean_object* v___x_785_; 
lean_inc(v_value_781_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_value_781_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg___boxed(lean_object* v_a_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_786_, v_x_787_);
lean_dec(v_x_787_);
lean_dec(v_a_786_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_buckets_791_; lean_object* v___x_792_; uint64_t v___y_794_; 
v_buckets_791_ = lean_ctor_get(v_m_789_, 1);
v___x_792_ = lean_array_get_size(v_buckets_791_);
if (lean_obj_tag(v_a_790_) == 0)
{
uint64_t v___x_808_; 
v___x_808_ = 1723ULL;
v___y_794_ = v___x_808_;
goto v___jp_793_;
}
else
{
uint64_t v_hash_809_; 
v_hash_809_ = lean_ctor_get_uint64(v_a_790_, sizeof(void*)*2);
v___y_794_ = v_hash_809_;
goto v___jp_793_;
}
v___jp_793_:
{
uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_795_ = 32ULL;
v___x_796_ = lean_uint64_shift_right(v___y_794_, v___x_795_);
v_fold_797_ = lean_uint64_xor(v___y_794_, v___x_796_);
v___x_798_ = 16ULL;
v___x_799_ = lean_uint64_shift_right(v_fold_797_, v___x_798_);
v___x_800_ = lean_uint64_xor(v_fold_797_, v___x_799_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = lean_usize_of_nat(v___x_792_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_sub(v___x_802_, v___x_803_);
v___x_805_ = lean_usize_land(v___x_801_, v___x_804_);
v___x_806_ = lean_array_uget_borrowed(v_buckets_791_, v___x_805_);
v___x_807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_790_, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg___boxed(lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_m_810_);
return v_res_812_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(lean_object* v_keys_813_, lean_object* v_i_814_, lean_object* v_k_815_){
_start:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_array_get_size(v_keys_813_);
v___x_817_ = lean_nat_dec_lt(v_i_814_, v___x_816_);
if (v___x_817_ == 0)
{
lean_dec(v_i_814_);
return v___x_817_;
}
else
{
lean_object* v_k_x27_818_; uint8_t v___x_819_; 
v_k_x27_818_ = lean_array_fget_borrowed(v_keys_813_, v_i_814_);
v___x_819_ = l_Lean_instBEqExtraModUse_beq(v_k_815_, v_k_x27_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(1u);
v___x_821_ = lean_nat_add(v_i_814_, v___x_820_);
lean_dec(v_i_814_);
v_i_814_ = v___x_821_;
goto _start;
}
else
{
lean_dec(v_i_814_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg___boxed(lean_object* v_keys_823_, lean_object* v_i_824_, lean_object* v_k_825_){
_start:
{
uint8_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_823_, v_i_824_, v_k_825_);
lean_dec_ref(v_k_825_);
lean_dec_ref(v_keys_823_);
v_r_827_ = lean_box(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(lean_object* v_x_828_, size_t v_x_829_, lean_object* v_x_830_){
_start:
{
if (lean_obj_tag(v_x_828_) == 0)
{
lean_object* v_es_831_; lean_object* v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v_j_835_; lean_object* v___x_836_; 
v_es_831_ = lean_ctor_get(v_x_828_, 0);
v___x_832_ = lean_box(2);
v___x_833_ = ((size_t)31ULL);
v___x_834_ = lean_usize_land(v_x_829_, v___x_833_);
v_j_835_ = lean_usize_to_nat(v___x_834_);
v___x_836_ = lean_array_get_borrowed(v___x_832_, v_es_831_, v_j_835_);
lean_dec(v_j_835_);
switch(lean_obj_tag(v___x_836_))
{
case 0:
{
lean_object* v_key_837_; uint8_t v___x_838_; 
v_key_837_ = lean_ctor_get(v___x_836_, 0);
v___x_838_ = l_Lean_instBEqExtraModUse_beq(v_x_830_, v_key_837_);
return v___x_838_;
}
case 1:
{
lean_object* v_node_839_; size_t v___x_840_; size_t v___x_841_; 
v_node_839_ = lean_ctor_get(v___x_836_, 0);
v___x_840_ = ((size_t)5ULL);
v___x_841_ = lean_usize_shift_right(v_x_829_, v___x_840_);
v_x_828_ = v_node_839_;
v_x_829_ = v___x_841_;
goto _start;
}
default: 
{
uint8_t v___x_843_; 
v___x_843_ = 0;
return v___x_843_;
}
}
}
else
{
lean_object* v_ks_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_ks_844_ = lean_ctor_get(v_x_828_, 0);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_ks_844_, v___x_845_, v_x_830_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg___boxed(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
size_t v_x_164168__boxed_850_; uint8_t v_res_851_; lean_object* v_r_852_; 
v_x_164168__boxed_850_ = lean_unbox_usize(v_x_848_);
lean_dec(v_x_848_);
v_res_851_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_847_, v_x_164168__boxed_850_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_847_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
uint64_t v___x_855_; size_t v___x_856_; uint8_t v___x_857_; 
v___x_855_ = l_Lean_instHashableExtraModUse_hash(v_x_854_);
v___x_856_ = lean_uint64_to_usize(v___x_855_);
v___x_857_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_853_, v___x_856_, v_x_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg___boxed(lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_858_, v_x_859_);
lean_dec_ref(v_x_859_);
lean_dec_ref(v_x_858_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__1));
v___x_865_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__0));
v___x_866_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3(void){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_867_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__3);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__4);
v___x_873_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
lean_ctor_set(v___x_873_, 3, v___x_872_);
lean_ctor_set(v___x_873_, 4, v___x_872_);
lean_ctor_set(v___x_873_, 5, v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__9));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__11));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14(void){
_start:
{
lean_object* v_cls_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_cls_885_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_886_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___closed__1));
v___x_887_ = l_Lean_Name_append(v___x_886_, v_cls_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__15));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__17));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(lean_object* v_mod_898_, uint8_t v_isMeta_899_, lean_object* v_hint_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_env_909_; uint8_t v_isExporting_910_; lean_object* v___x_911_; lean_object* v_env_912_; lean_object* v___x_913_; lean_object* v_entry_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_908_ = lean_st_ref_get(v___y_906_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_908_);
v_isExporting_910_ = lean_ctor_get_uint8(v_env_909_, sizeof(void*)*8);
lean_dec_ref(v_env_909_);
v___x_911_ = lean_st_ref_get(v___y_906_);
v_env_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_env_912_);
lean_dec(v___x_911_);
v___x_913_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__2);
lean_inc(v_mod_898_);
v_entry_914_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_914_, 0, v_mod_898_);
lean_ctor_set_uint8(v_entry_914_, sizeof(void*)*1, v_isExporting_910_);
lean_ctor_set_uint8(v_entry_914_, sizeof(void*)*1 + 1, v_isMeta_899_);
v___x_915_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_916_ = lean_box(1);
v___x_917_ = lean_box(0);
v___x_960_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_913_, v___x_915_, v_env_912_, v___x_916_, v___x_917_);
v___x_961_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v___x_960_, v_entry_914_);
lean_dec(v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v_options_962_; uint8_t v_hasTrace_963_; 
v_options_962_ = lean_ctor_get(v___y_905_, 1);
v_hasTrace_963_ = lean_ctor_get_uint8(v_options_962_, sizeof(void*)*1);
if (v_hasTrace_963_ == 0)
{
lean_dec(v_hint_900_);
lean_dec(v_mod_898_);
v___y_919_ = v___y_904_;
v___y_920_ = v___y_906_;
goto v___jp_918_;
}
else
{
lean_object* v_toCold_964_; lean_object* v_inheritedTraceOptions_965_; lean_object* v_cls_966_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_toCold_964_ = lean_ctor_get(v___y_905_, 0);
v_inheritedTraceOptions_965_ = lean_ctor_get(v_toCold_964_, 4);
v_cls_966_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__8));
v___x_986_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__14);
v___x_987_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_965_, v_options_962_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec(v_hint_900_);
lean_dec(v_mod_898_);
v___y_919_ = v___y_904_;
v___y_920_ = v___y_906_;
goto v___jp_918_;
}
else
{
lean_object* v___x_988_; lean_object* v___y_990_; 
v___x_988_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__16);
if (v_isExporting_910_ == 0)
{
lean_object* v___x_997_; 
v___x_997_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__21));
v___y_990_ = v___x_997_;
goto v___jp_989_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__22));
v___y_990_ = v___x_998_;
goto v___jp_989_;
}
v___jp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc_ref(v___y_990_);
v___x_991_ = l_Lean_stringToMessageData(v___y_990_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_988_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__18);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
if (v_isMeta_899_ == 0)
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__19));
v___y_973_ = v___x_994_;
v___y_974_ = v___x_995_;
goto v___jp_972_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__20));
v___y_973_ = v___x_994_;
v___y_974_ = v___x_996_;
goto v___jp_972_;
}
}
}
v___jp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_968_);
lean_ctor_set(v___x_970_, 1, v___y_969_);
v___x_971_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_966_, v___x_970_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref_known(v___x_971_, 1);
v___y_919_ = v___y_904_;
v___y_920_ = v___y_906_;
goto v___jp_918_;
}
else
{
lean_dec_ref_known(v_entry_914_, 1);
return v___x_971_;
}
}
v___jp_972_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
lean_inc_ref(v___y_974_);
v___x_975_ = l_Lean_stringToMessageData(v___y_974_);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___y_973_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__10);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_MessageData_ofName(v_mod_898_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Name_isAnonymous(v_hint_900_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__12);
v___x_983_ = l_Lean_MessageData_ofName(v_hint_900_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___y_968_ = v___x_980_;
v___y_969_ = v___x_984_;
goto v___jp_967_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v_hint_900_);
v___x_985_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__13);
v___y_968_ = v___x_980_;
v___y_969_ = v___x_985_;
goto v___jp_967_;
}
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec_ref_known(v_entry_914_, 1);
lean_dec(v_hint_900_);
lean_dec(v_mod_898_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
v___jp_918_:
{
lean_object* v___x_921_; lean_object* v_toEnvExtension_922_; lean_object* v_env_923_; lean_object* v_nextMacroScope_924_; lean_object* v_ngen_925_; lean_object* v_auxDeclNGen_926_; lean_object* v_traceState_927_; lean_object* v_messages_928_; lean_object* v_infoState_929_; lean_object* v_snapshotTasks_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_958_; 
v___x_921_ = lean_st_ref_take(v___y_920_);
v_toEnvExtension_922_ = lean_ctor_get(v___x_915_, 0);
v_env_923_ = lean_ctor_get(v___x_921_, 0);
v_nextMacroScope_924_ = lean_ctor_get(v___x_921_, 1);
v_ngen_925_ = lean_ctor_get(v___x_921_, 2);
v_auxDeclNGen_926_ = lean_ctor_get(v___x_921_, 3);
v_traceState_927_ = lean_ctor_get(v___x_921_, 4);
v_messages_928_ = lean_ctor_get(v___x_921_, 6);
v_infoState_929_ = lean_ctor_get(v___x_921_, 7);
v_snapshotTasks_930_ = lean_ctor_get(v___x_921_, 8);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v___x_921_, 5);
lean_dec(v_unused_959_);
v___x_932_ = v___x_921_;
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snapshotTasks_930_);
lean_inc(v_infoState_929_);
lean_inc(v_messages_928_);
lean_inc(v_traceState_927_);
lean_inc(v_auxDeclNGen_926_);
lean_inc(v_ngen_925_);
lean_inc(v_nextMacroScope_924_);
lean_inc(v_env_923_);
lean_dec(v___x_921_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_958_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_asyncMode_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v_asyncMode_934_ = lean_ctor_get(v_toEnvExtension_922_, 2);
v___x_935_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_915_, v_env_923_, v_entry_914_, v_asyncMode_934_, v___x_917_);
v___x_936_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__5);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 5, v___x_936_);
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_nextMacroScope_924_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_ngen_925_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_auxDeclNGen_926_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_traceState_927_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_957_, 6, v_messages_928_);
lean_ctor_set(v_reuseFailAlloc_957_, 7, v_infoState_929_);
lean_ctor_set(v_reuseFailAlloc_957_, 8, v_snapshotTasks_930_);
v___x_938_ = v_reuseFailAlloc_957_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_mctx_941_; lean_object* v_zetaDeltaFVarIds_942_; lean_object* v_postponed_943_; lean_object* v_diag_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_955_; 
v___x_939_ = lean_st_ref_put(v___y_920_, v___x_938_);
v___x_940_ = lean_st_ref_take(v___y_919_);
v_mctx_941_ = lean_ctor_get(v___x_940_, 0);
v_zetaDeltaFVarIds_942_ = lean_ctor_get(v___x_940_, 2);
v_postponed_943_ = lean_ctor_get(v___x_940_, 3);
v_diag_944_ = lean_ctor_get(v___x_940_, 4);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v___x_940_, 1);
lean_dec(v_unused_956_);
v___x_946_ = v___x_940_;
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_diag_944_);
lean_inc(v_postponed_943_);
lean_inc(v_zetaDeltaFVarIds_942_);
lean_inc(v_mctx_941_);
lean_dec(v___x_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___closed__6);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_mctx_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_zetaDeltaFVarIds_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v_postponed_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v_diag_944_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_st_ref_put(v___y_919_, v___x_950_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8___boxed(lean_object* v_mod_1001_, lean_object* v_isMeta_1002_, lean_object* v_hint_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_isMeta_boxed_1011_; lean_object* v_res_1012_; 
v_isMeta_boxed_1011_ = lean_unbox(v_isMeta_1002_);
v_res_1012_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_mod_1001_, v_isMeta_boxed_1011_, v_hint_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(lean_object* v___x_1013_, lean_object* v_declName_1014_, lean_object* v_as_1015_, size_t v_sz_1016_, size_t v_i_1017_, lean_object* v_b_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_usize_dec_lt(v_i_1017_, v_sz_1016_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec(v_declName_1014_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_b_1018_);
return v___x_1027_;
}
else
{
lean_object* v___x_1028_; lean_object* v_modules_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v_toImport_1033_; lean_object* v_module_1034_; uint8_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1028_ = l_Lean_Environment_header(v___x_1013_);
v_modules_1029_ = lean_ctor_get(v___x_1028_, 3);
lean_inc_ref(v_modules_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1031_ = lean_array_uget_borrowed(v_as_1015_, v_i_1017_);
v___x_1032_ = lean_array_get(v___x_1030_, v_modules_1029_, v_a_1031_);
lean_dec_ref(v_modules_1029_);
v_toImport_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_ref(v_toImport_1033_);
lean_dec(v___x_1032_);
v_module_1034_ = lean_ctor_get(v_toImport_1033_, 0);
lean_inc(v_module_1034_);
lean_dec_ref(v_toImport_1033_);
v___x_1035_ = 0;
lean_inc(v_declName_1014_);
v___x_1036_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1034_, v___x_1035_, v_declName_1014_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; 
lean_dec_ref_known(v___x_1036_, 1);
v___x_1037_ = lean_box(0);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_add(v_i_1017_, v___x_1038_);
v_i_1017_ = v___x_1039_;
v_b_1018_ = v___x_1037_;
goto _start;
}
else
{
lean_dec(v_declName_1014_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9___boxed(lean_object* v___x_1041_, lean_object* v_declName_1042_, lean_object* v_as_1043_, lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_sz_boxed_1054_; size_t v_i_boxed_1055_; lean_object* v_res_1056_; 
v_sz_boxed_1054_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1055_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v___x_1041_, v_declName_1042_, v_as_1043_, v_sz_boxed_1054_, v_i_boxed_1055_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_as_1043_);
lean_dec_ref(v___x_1041_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__1));
v___x_1060_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__0));
v___x_1061_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1060_, v___x_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* v_declName_1064_, uint8_t v_isMeta_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_env_1077_; lean_object* v___y_1079_; lean_object* v___x_1092_; 
v___x_1073_ = lean_st_ref_get(v___y_1071_);
v_env_1077_ = lean_ctor_get(v___x_1073_, 0);
lean_inc_ref(v_env_1077_);
lean_dec(v___x_1073_);
v___x_1092_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1077_, v_declName_1064_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1064_);
goto v___jp_1074_;
}
else
{
lean_object* v_val_1093_; lean_object* v___x_1094_; lean_object* v_modules_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_val_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_val_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Lean_Environment_header(v_env_1077_);
v_modules_1095_ = lean_ctor_get(v___x_1094_, 3);
lean_inc_ref(v_modules_1095_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = lean_array_get_size(v_modules_1095_);
v___x_1097_ = lean_nat_dec_lt(v_val_1093_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v_modules_1095_);
lean_dec(v_val_1093_);
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1064_);
goto v___jp_1074_;
}
else
{
lean_object* v___x_1098_; lean_object* v_env_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___y_1103_; 
v___x_1098_ = lean_st_ref_get(v___y_1071_);
v_env_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_ref(v_env_1099_);
lean_dec(v___x_1098_);
v___x_1100_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__2);
v___x_1101_ = lean_array_fget(v_modules_1095_, v_val_1093_);
lean_dec(v_val_1093_);
lean_dec_ref(v_modules_1095_);
if (v_isMeta_1065_ == 0)
{
lean_dec_ref(v_env_1099_);
v___y_1103_ = v_isMeta_1065_;
goto v___jp_1102_;
}
else
{
uint8_t v___x_1114_; 
lean_inc(v_declName_1064_);
v___x_1114_ = l_Lean_isMarkedMeta(v_env_1099_, v_declName_1064_);
if (v___x_1114_ == 0)
{
v___y_1103_ = v_isMeta_1065_;
goto v___jp_1102_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = 0;
v___y_1103_ = v___x_1115_;
goto v___jp_1102_;
}
}
v___jp_1102_:
{
lean_object* v_toImport_1104_; lean_object* v_module_1105_; lean_object* v___x_1106_; 
v_toImport_1104_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_toImport_1104_);
lean_dec(v___x_1101_);
v_module_1105_ = lean_ctor_get(v_toImport_1104_, 0);
lean_inc(v_module_1105_);
lean_dec_ref(v_toImport_1104_);
lean_inc(v_declName_1064_);
v___x_1106_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8(v_module_1105_, v___y_1103_, v_declName_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref_known(v___x_1106_, 1);
v___x_1107_ = l_Lean_indirectModUseExt;
v___x_1108_ = lean_box(1);
v___x_1109_ = lean_box(0);
lean_inc_ref(v_env_1077_);
v___x_1110_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1100_, v___x_1107_, v_env_1077_, v___x_1108_, v___x_1109_);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v___x_1110_, v_declName_1064_);
lean_dec(v___x_1110_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___closed__3));
v___y_1079_ = v___x_1112_;
goto v___jp_1078_;
}
else
{
lean_object* v_val_1113_; 
v_val_1113_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1111_, 1);
v___y_1079_ = v_val_1113_;
goto v___jp_1078_;
}
}
else
{
lean_dec_ref(v_env_1077_);
lean_dec(v_declName_1064_);
return v___x_1106_;
}
}
}
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
v___jp_1078_:
{
lean_object* v___x_1080_; size_t v_sz_1081_; size_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = lean_box(0);
v_sz_1081_ = lean_array_size(v___y_1079_);
v___x_1082_ = ((size_t)0ULL);
v___x_1083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__9(v_env_1077_, v_declName_1064_, v___y_1079_, v_sz_1081_, v___x_1082_, v___x_1080_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v_env_1077_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1091_);
v___x_1085_ = v___x_1083_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v___x_1083_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1080_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* v_declName_1116_, lean_object* v_isMeta_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v_isMeta_boxed_1125_; lean_object* v_res_1126_; 
v_isMeta_boxed_1125_ = lean_unbox(v_isMeta_1117_);
v_res_1126_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_declName_1116_, v_isMeta_boxed_1125_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(lean_object* v_as_x27_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
if (lean_obj_tag(v_as_x27_1127_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_b_1128_);
return v___x_1136_;
}
else
{
lean_object* v_head_1137_; lean_object* v_tail_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; 
v_head_1137_ = lean_ctor_get(v_as_x27_1127_, 0);
v_tail_1138_ = lean_ctor_get(v_as_x27_1127_, 1);
v___x_1139_ = 1;
lean_inc(v_head_1137_);
v___x_1140_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(v_head_1137_, v___x_1139_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1140_, 1);
v___x_1141_ = lean_box(0);
v_as_x27_1127_ = v_tail_1138_;
v_b_1128_ = v___x_1141_;
goto _start;
}
else
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_1143_, v_b_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v_as_x27_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* v_env_1153_, lean_object* v_currNamespace_1154_, lean_object* v_openDecls_1155_, lean_object* v_n_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = l_Lean_ResolveName_resolveNamespace(v_env_1153_, v_currNamespace_1154_, v_openDecls_1155_, v_n_1156_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* v_env_1161_, lean_object* v_currNamespace_1162_, lean_object* v_openDecls_1163_, lean_object* v_n_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(v_env_1161_, v_currNamespace_1162_, v_openDecls_1163_, v_n_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* v_currNamespace_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_currNamespace_1168_);
lean_ctor_set(v___x_1171_, 1, v___y_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(v_currNamespace_1172_, v___y_1173_, v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* v_env_1176_, lean_object* v_options_1177_, lean_object* v_currNamespace_1178_, lean_object* v_openDecls_1179_, lean_object* v_n_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = l_Lean_ResolveName_resolveGlobalName(v_env_1176_, v_options_1177_, v_currNamespace_1178_, v_openDecls_1179_, v_n_1180_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* v_env_1185_, lean_object* v_options_1186_, lean_object* v_currNamespace_1187_, lean_object* v_openDecls_1188_, lean_object* v_n_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(v_env_1185_, v_options_1186_, v_currNamespace_1187_, v_openDecls_1188_, v_n_1189_, v___y_1190_, v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec_ref(v_options_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v_toCold_1203_; lean_object* v_env_1204_; lean_object* v_options_1205_; lean_object* v_currRecDepth_1206_; lean_object* v_maxRecDepth_1207_; lean_object* v_ref_1208_; lean_object* v_currNamespace_1209_; lean_object* v_openDecls_1210_; lean_object* v_currMacroScope_1211_; lean_object* v_quotContext_1212_; lean_object* v___x_1213_; lean_object* v_nextMacroScope_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v_methods_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1202_ = lean_st_ref_get(v___y_1200_);
v_toCold_1203_ = lean_ctor_get(v___y_1199_, 0);
v_env_1204_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_ref_n(v_env_1204_, 4);
lean_dec(v___x_1202_);
v_options_1205_ = lean_ctor_get(v___y_1199_, 1);
v_currRecDepth_1206_ = lean_ctor_get(v___y_1199_, 2);
v_maxRecDepth_1207_ = lean_ctor_get(v___y_1199_, 3);
v_ref_1208_ = lean_ctor_get(v___y_1199_, 4);
v_currNamespace_1209_ = lean_ctor_get(v___y_1199_, 5);
v_openDecls_1210_ = lean_ctor_get(v___y_1199_, 6);
v_currMacroScope_1211_ = lean_ctor_get(v___y_1199_, 9);
v_quotContext_1212_ = lean_ctor_get(v_toCold_1203_, 2);
v___x_1213_ = lean_st_ref_get(v___y_1200_);
v_nextMacroScope_1214_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_nextMacroScope_1214_);
lean_dec(v___x_1213_);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1215_, 0, v_env_1204_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1216_, 0, v_env_1204_);
lean_inc_n(v_openDecls_1210_, 2);
lean_inc_n(v_currNamespace_1209_, 3);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1217_, 0, v_env_1204_);
lean_closure_set(v___f_1217_, 1, v_currNamespace_1209_);
lean_closure_set(v___f_1217_, 2, v_openDecls_1210_);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1218_, 0, v_currNamespace_1209_);
lean_inc_ref(v_options_1205_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1219_, 0, v_env_1204_);
lean_closure_set(v___f_1219_, 1, v_options_1205_);
lean_closure_set(v___f_1219_, 2, v_currNamespace_1209_);
lean_closure_set(v___f_1219_, 3, v_openDecls_1210_);
v_methods_1220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1220_, 0, v___f_1215_);
lean_ctor_set(v_methods_1220_, 1, v___f_1218_);
lean_ctor_set(v_methods_1220_, 2, v___f_1216_);
lean_ctor_set(v_methods_1220_, 3, v___f_1217_);
lean_ctor_set(v_methods_1220_, 4, v___f_1219_);
lean_inc(v_ref_1208_);
lean_inc(v_maxRecDepth_1207_);
lean_inc(v_currRecDepth_1206_);
lean_inc(v_currMacroScope_1211_);
lean_inc(v_quotContext_1212_);
v___x_1221_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1221_, 0, v_methods_1220_);
lean_ctor_set(v___x_1221_, 1, v_quotContext_1212_);
lean_ctor_set(v___x_1221_, 2, v_currMacroScope_1211_);
lean_ctor_set(v___x_1221_, 3, v_currRecDepth_1206_);
lean_ctor_set(v___x_1221_, 4, v_maxRecDepth_1207_);
lean_ctor_set(v___x_1221_, 5, v_ref_1208_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1223_, 0, v_nextMacroScope_1214_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
v___x_1224_ = lean_apply_2(v_x_1194_, v___x_1221_, v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_a_1226_; lean_object* v_macroScope_1227_; lean_object* v_traceMsgs_1228_; lean_object* v_expandedMacroDecls_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_a_1225_);
v_a_1226_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1224_, 2);
v_macroScope_1227_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_macroScope_1227_);
v_traceMsgs_1228_ = lean_ctor_get(v_a_1225_, 1);
lean_inc(v_traceMsgs_1228_);
v_expandedMacroDecls_1229_ = lean_ctor_get(v_a_1225_, 2);
lean_inc(v_expandedMacroDecls_1229_);
lean_dec(v_a_1225_);
v___x_1230_ = lean_box(0);
v___x_1231_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_expandedMacroDecls_1229_, v___x_1230_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v_expandedMacroDecls_1229_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; lean_object* v_env_1233_; lean_object* v_ngen_1234_; lean_object* v_auxDeclNGen_1235_; lean_object* v_traceState_1236_; lean_object* v_cache_1237_; lean_object* v_messages_1238_; lean_object* v_infoState_1239_; lean_object* v_snapshotTasks_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref_known(v___x_1231_, 1);
v___x_1232_ = lean_st_ref_take(v___y_1200_);
v_env_1233_ = lean_ctor_get(v___x_1232_, 0);
v_ngen_1234_ = lean_ctor_get(v___x_1232_, 2);
v_auxDeclNGen_1235_ = lean_ctor_get(v___x_1232_, 3);
v_traceState_1236_ = lean_ctor_get(v___x_1232_, 4);
v_cache_1237_ = lean_ctor_get(v___x_1232_, 5);
v_messages_1238_ = lean_ctor_get(v___x_1232_, 6);
v_infoState_1239_ = lean_ctor_get(v___x_1232_, 7);
v_snapshotTasks_1240_ = lean_ctor_get(v___x_1232_, 8);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1232_, 1);
lean_dec(v_unused_1267_);
v___x_1242_ = v___x_1232_;
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snapshotTasks_1240_);
lean_inc(v_infoState_1239_);
lean_inc(v_messages_1238_);
lean_inc(v_cache_1237_);
lean_inc(v_traceState_1236_);
lean_inc(v_auxDeclNGen_1235_);
lean_inc(v_ngen_1234_);
lean_inc(v_env_1233_);
lean_dec(v___x_1232_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1266_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_macroScope_1227_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_env_1233_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_macroScope_1227_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_ngen_1234_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_auxDeclNGen_1235_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_traceState_1236_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v_cache_1237_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_messages_1238_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_infoState_1239_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_snapshotTasks_1240_);
v___x_1245_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_st_ref_put(v___y_1200_, v___x_1245_);
v___x_1247_ = l_List_reverse___redArg(v_traceMsgs_1228_);
v___x_1248_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(v___x_1247_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1256_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v_a_1226_);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1226_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1226_);
v_a_1257_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1248_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1248_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_traceMsgs_1228_);
lean_dec(v_macroScope_1227_);
lean_dec(v_a_1226_);
v_a_1268_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1231_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1231_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_a_1276_; 
v_a_1276_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1224_, 2);
if (lean_obj_tag(v_a_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_a_1277_ = lean_ctor_get(v_a_1276_, 0);
lean_inc(v_a_1277_);
v_a_1278_ = lean_ctor_get(v_a_1276_, 1);
lean_inc_ref(v_a_1278_);
lean_dec_ref_known(v_a_1276_, 2);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
v___x_1280_ = lean_string_dec_eq(v_a_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_a_1278_);
v___x_1282_ = l_Lean_MessageData_ofFormat(v___x_1281_);
v___x_1283_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_a_1277_, v___x_1282_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v_a_1277_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
lean_dec_ref(v_a_1278_);
v___x_1284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_a_1277_);
return v___x_1284_;
}
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t v_sz_1298_, size_t v_i_1299_, lean_object* v_bs_1300_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1299_, v_sz_1298_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_bs_1300_);
return v___x_1302_;
}
else
{
lean_object* v_v_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_v_1303_ = lean_array_uget(v_bs_1300_, v_i_1299_);
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(v_v_1303_);
v___x_1305_ = l_Lean_Syntax_isOfKind(v_v_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_dec(v_v_1303_);
lean_dec_ref(v_bs_1300_);
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = l_Lean_Syntax_getArg(v_v_1303_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_isOfKind(v___x_1308_, v___x_1304_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec(v_v_1303_);
lean_dec_ref(v_bs_1300_);
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v_bs_x27_1312_; lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v___x_1311_ = lean_unsigned_to_nat(3u);
v_bs_x27_1312_ = lean_array_uset(v_bs_1300_, v_i_1299_, v___x_1307_);
v___x_1313_ = l_Lean_Syntax_getArg(v_v_1303_, v___x_1311_);
lean_dec(v_v_1303_);
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1299_, v___x_1314_);
v___x_1316_ = lean_array_uset(v_bs_x27_1312_, v_i_1299_, v___x_1313_);
v_i_1299_ = v___x_1315_;
v_bs_1300_ = v___x_1316_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* v_sz_1318_, lean_object* v_i_1319_, lean_object* v_bs_1320_){
_start:
{
size_t v_sz_boxed_1321_; size_t v_i_boxed_1322_; lean_object* v_res_1323_; 
v_sz_boxed_1321_ = lean_unbox_usize(v_sz_1318_);
lean_dec(v_sz_1318_);
v_i_boxed_1322_ = lean_unbox_usize(v_i_1319_);
lean_dec(v_i_1319_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_boxed_1321_, v_i_boxed_1322_, v_bs_1320_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(uint8_t v___x_1336_, size_t v_sz_1337_, size_t v_i_1338_, lean_object* v_bs_1339_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_usize_dec_lt(v_i_1338_, v_sz_1337_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_bs_1339_);
return v___x_1341_;
}
else
{
lean_object* v_v_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_v_1342_ = lean_array_uget(v_bs_1339_, v_i_1338_);
v___x_1343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(v_v_1342_);
v___x_1344_ = l_Lean_Syntax_isOfKind(v_v_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
lean_dec(v_v_1342_);
lean_dec_ref(v_bs_1339_);
v___x_1345_ = lean_box(0);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_bs_x27_1348_; 
v___x_1346_ = lean_unsigned_to_nat(3u);
v___x_1347_ = lean_unsigned_to_nat(0u);
v_bs_x27_1348_ = lean_array_uset(v_bs_1339_, v_i_1338_, v___x_1347_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = l_Lean_Syntax_getArg(v_v_1342_, v___x_1355_);
v___x_1357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
v___x_1358_ = l_Lean_Syntax_isOfKind(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v_bs_x27_1348_);
lean_dec(v_v_1342_);
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
else
{
goto v___jp_1349_;
}
}
else
{
goto v___jp_1349_;
}
v___jp_1349_:
{
lean_object* v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1350_ = l_Lean_Syntax_getArg(v_v_1342_, v___x_1346_);
lean_dec(v_v_1342_);
v___x_1351_ = ((size_t)1ULL);
v___x_1352_ = lean_usize_add(v_i_1338_, v___x_1351_);
v___x_1353_ = lean_array_uset(v_bs_x27_1348_, v_i_1338_, v___x_1350_);
v_i_1338_ = v___x_1352_;
v_bs_1339_ = v___x_1353_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* v___x_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_bs_1363_){
_start:
{
uint8_t v___x_164956__boxed_1364_; size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v___x_164956__boxed_1364_ = lean_unbox(v___x_1360_);
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_164956__boxed_1364_, v_sz_boxed_1365_, v_i_boxed_1366_, v_bs_1363_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t v_sz_1374_, size_t v_i_1375_, lean_object* v_bs_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_lt(v_i_1375_, v_sz_1374_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_bs_1376_);
return v___x_1378_;
}
else
{
lean_object* v_v_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v_v_1379_ = lean_array_uget(v_bs_1376_, v_i_1375_);
v___x_1380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(v_v_1379_);
v___x_1381_ = l_Lean_Syntax_isOfKind(v_v_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_dec(v_v_1379_);
lean_dec_ref(v_bs_1376_);
v___x_1382_ = lean_box(0);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v_bs_x27_1384_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v_bs_x27_1384_ = lean_array_uset(v_bs_1376_, v_i_1375_, v___x_1383_);
v___x_1391_ = l_Lean_Syntax_getArg(v_v_1379_, v___x_1383_);
lean_dec(v_v_1379_);
v___x_1392_ = l_Lean_Syntax_isNone(v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(2u);
v___x_1394_ = l_Lean_Syntax_matchesNull(v___x_1391_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
lean_dec_ref(v_bs_x27_1384_);
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
else
{
goto v___jp_1385_;
}
}
else
{
lean_dec(v___x_1391_);
goto v___jp_1385_;
}
v___jp_1385_:
{
lean_object* v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = ((size_t)1ULL);
v___x_1388_ = lean_usize_add(v_i_1375_, v___x_1387_);
v___x_1389_ = lean_array_uset(v_bs_x27_1384_, v_i_1375_, v___x_1386_);
v_i_1375_ = v___x_1388_;
v_bs_1376_ = v___x_1389_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_bs_1398_){
_start:
{
size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_boxed_1399_, v_i_boxed_1400_, v_bs_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t v_sz_1402_, size_t v_i_1403_, lean_object* v_bs_1404_){
_start:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_lt(v_i_1403_, v_sz_1402_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_bs_1404_);
return v___x_1406_;
}
else
{
lean_object* v_v_1407_; lean_object* v___x_1408_; lean_object* v_bs_x27_1409_; size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; 
v_v_1407_ = lean_array_uget(v_bs_1404_, v_i_1403_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v_bs_x27_1409_ = lean_array_uset(v_bs_1404_, v_i_1403_, v___x_1408_);
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_add(v_i_1403_, v___x_1410_);
v___x_1412_ = lean_array_uset(v_bs_x27_1409_, v_i_1403_, v_v_1407_);
v_i_1403_ = v___x_1411_;
v_bs_1404_ = v___x_1412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* v_sz_1414_, lean_object* v_i_1415_, lean_object* v_bs_1416_){
_start:
{
size_t v_sz_boxed_1417_; size_t v_i_boxed_1418_; lean_object* v_res_1419_; 
v_sz_boxed_1417_ = lean_unbox_usize(v_sz_1414_);
lean_dec(v_sz_1414_);
v_i_boxed_1418_ = lean_unbox_usize(v_i_1415_);
lean_dec(v_i_1415_);
v_res_1419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_boxed_1417_, v_i_boxed_1418_, v_bs_1416_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* v_00_u03b1_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(v_x_1421_, v___y_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* v_00_u03b1_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(v_00_u03b1_1425_, v_x_1426_, v___y_1427_, v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec_ref(v_x_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* v_stx_1433_, lean_object* v_as_x27_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
if (lean_obj_tag(v_as_x27_1434_) == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_stx_1433_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_b_1435_);
return v___x_1443_;
}
else
{
lean_object* v_head_1444_; lean_object* v_tail_1445_; lean_object* v_value_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_b_1435_);
v_head_1444_ = lean_ctor_get(v_as_x27_1434_, 0);
v_tail_1445_ = lean_ctor_get(v_as_x27_1434_, 1);
v_value_1446_ = lean_ctor_get(v_head_1444_, 1);
v___x_1447_ = lean_box(0);
lean_inc(v_value_1446_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v_stx_1433_);
v___x_1448_ = lean_apply_8(v_value_1446_, v_stx_1433_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, lean_box(0));
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_stx_1433_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1458_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1449_);
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1447_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1481_; 
v_a_1459_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1461_ = v___x_1448_;
v_isShared_1462_ = v_isSharedCheck_1481_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1448_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1481_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___y_1466_; uint8_t v___x_1479_; 
v___x_1463_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_1464_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1479_ = l_Lean_Exception_isInterrupt(v_a_1459_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; 
lean_inc(v_a_1459_);
v___x_1480_ = l_Lean_Exception_isRuntime(v_a_1459_);
v___y_1466_ = v___x_1480_;
goto v___jp_1465_;
}
else
{
v___y_1466_ = v___x_1479_;
goto v___jp_1465_;
}
v___jp_1465_:
{
if (v___y_1466_ == 0)
{
if (lean_obj_tag(v_a_1459_) == 0)
{
lean_object* v___x_1468_; 
lean_dec(v_stx_1433_);
if (v_isShared_1462_ == 0)
{
v___x_1468_ = v___x_1461_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1459_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
else
{
lean_object* v_id_1470_; uint8_t v___x_1471_; 
v_id_1470_ = lean_ctor_get(v_a_1459_, 0);
v___x_1471_ = l_Lean_instBEqInternalExceptionId_beq(v___x_1464_, v_id_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_stx_1433_);
if (v_isShared_1462_ == 0)
{
v___x_1473_ = v___x_1461_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1459_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_dec_ref_known(v_a_1459_, 2);
lean_del_object(v___x_1461_);
v_as_x27_1434_ = v_tail_1445_;
v_b_1435_ = v___x_1463_;
goto _start;
}
}
}
else
{
lean_object* v___x_1477_; 
lean_dec(v_stx_1433_);
if (v_isShared_1462_ == 0)
{
v___x_1477_ = v___x_1461_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1459_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* v_stx_1482_, lean_object* v_as_x27_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_1482_, v_as_x27_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v_as_x27_1483_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* v_reassigned_1495_, lean_object* v_rhs_x3f_1496_, lean_object* v_otherwise_x3f_1497_, lean_object* v_body_x3f_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
uint8_t v___y_1507_; uint8_t v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; uint8_t v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v_body_1518_; lean_object* v___y_1539_; lean_object* v_otherwise_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_rhs_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; 
if (lean_obj_tag(v_rhs_x3f_1496_) == 0)
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v_rhs_1552_ = v___x_1563_;
v___y_1553_ = v_a_1499_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
v___y_1558_ = v_a_1504_;
goto v___jp_1551_;
}
else
{
lean_object* v_val_1564_; lean_object* v___x_1565_; 
v_val_1564_ = lean_ctor_get(v_rhs_x3f_1496_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_rhs_x3f_1496_, 1);
v___x_1565_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_val_1564_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v_rhs_1552_ = v_a_1566_;
v___y_1553_ = v_a_1499_;
v___y_1554_ = v_a_1500_;
v___y_1555_ = v_a_1501_;
v___y_1556_ = v_a_1502_;
v___y_1557_ = v_a_1503_;
v___y_1558_ = v_a_1504_;
goto v___jp_1551_;
}
else
{
lean_dec(v_body_x3f_1498_);
lean_dec(v_otherwise_x3f_1497_);
lean_dec_ref(v_reassigned_1495_);
return v___x_1565_;
}
}
v___jp_1506_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_1513_, 0, v___y_1509_);
lean_ctor_set(v___x_1513_, 1, v___y_1512_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*2, v___y_1507_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*2 + 1, v___y_1510_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*2 + 2, v___y_1511_);
lean_ctor_set_uint8(v___x_1513_, sizeof(void*)*2 + 3, v___y_1508_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
v___jp_1515_:
{
lean_object* v___x_1519_; lean_object* v_info_1520_; uint8_t v_breaks_1521_; uint8_t v_continues_1522_; uint8_t v_returnsEarly_1523_; lean_object* v_numRegularExits_1524_; uint8_t v_noFallthrough_1525_; lean_object* v_reassigns_1526_; size_t v_sz_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1519_ = l_Lean_Elab_Do_ControlInfo_alternative(v_body_1518_, v___y_1517_);
v_info_1520_ = l_Lean_Elab_Do_ControlInfo_sequence(v___y_1516_, v___x_1519_);
v_breaks_1521_ = lean_ctor_get_uint8(v_info_1520_, sizeof(void*)*2);
v_continues_1522_ = lean_ctor_get_uint8(v_info_1520_, sizeof(void*)*2 + 1);
v_returnsEarly_1523_ = lean_ctor_get_uint8(v_info_1520_, sizeof(void*)*2 + 2);
v_numRegularExits_1524_ = lean_ctor_get(v_info_1520_, 0);
lean_inc(v_numRegularExits_1524_);
v_noFallthrough_1525_ = lean_ctor_get_uint8(v_info_1520_, sizeof(void*)*2 + 3);
v_reassigns_1526_ = lean_ctor_get(v_info_1520_, 1);
lean_inc(v_reassigns_1526_);
lean_dec_ref(v_info_1520_);
v_sz_1527_ = lean_array_size(v_reassigned_1495_);
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(v_sz_1527_, v___x_1528_, v_reassigned_1495_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_array_get_size(v___x_1529_);
v___x_1532_ = lean_nat_dec_lt(v___x_1530_, v___x_1531_);
if (v___x_1532_ == 0)
{
lean_dec_ref(v___x_1529_);
v___y_1507_ = v_breaks_1521_;
v___y_1508_ = v_noFallthrough_1525_;
v___y_1509_ = v_numRegularExits_1524_;
v___y_1510_ = v_continues_1522_;
v___y_1511_ = v_returnsEarly_1523_;
v___y_1512_ = v_reassigns_1526_;
goto v___jp_1506_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_le(v___x_1531_, v___x_1531_);
if (v___x_1533_ == 0)
{
if (v___x_1532_ == 0)
{
lean_dec_ref(v___x_1529_);
v___y_1507_ = v_breaks_1521_;
v___y_1508_ = v_noFallthrough_1525_;
v___y_1509_ = v_numRegularExits_1524_;
v___y_1510_ = v_continues_1522_;
v___y_1511_ = v_returnsEarly_1523_;
v___y_1512_ = v_reassigns_1526_;
goto v___jp_1506_;
}
else
{
size_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_usize_of_nat(v___x_1531_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1529_, v___x_1528_, v___x_1534_, v_reassigns_1526_);
lean_dec_ref(v___x_1529_);
v___y_1507_ = v_breaks_1521_;
v___y_1508_ = v_noFallthrough_1525_;
v___y_1509_ = v_numRegularExits_1524_;
v___y_1510_ = v_continues_1522_;
v___y_1511_ = v_returnsEarly_1523_;
v___y_1512_ = v___x_1535_;
goto v___jp_1506_;
}
}
else
{
size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_usize_of_nat(v___x_1531_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(v___x_1529_, v___x_1528_, v___x_1536_, v_reassigns_1526_);
lean_dec_ref(v___x_1529_);
v___y_1507_ = v_breaks_1521_;
v___y_1508_ = v_noFallthrough_1525_;
v___y_1509_ = v_numRegularExits_1524_;
v___y_1510_ = v_continues_1522_;
v___y_1511_ = v_returnsEarly_1523_;
v___y_1512_ = v___x_1537_;
goto v___jp_1506_;
}
}
}
v___jp_1538_:
{
if (lean_obj_tag(v_body_x3f_1498_) == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1516_ = v___y_1539_;
v___y_1517_ = v_otherwise_1540_;
v_body_1518_ = v___x_1547_;
goto v___jp_1515_;
}
else
{
lean_object* v_val_1548_; lean_object* v___x_1549_; 
v_val_1548_ = lean_ctor_get(v_body_x3f_1498_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_body_x3f_1498_, 1);
v___x_1549_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1548_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___y_1516_ = v___y_1539_;
v___y_1517_ = v_otherwise_1540_;
v_body_1518_ = v_a_1550_;
goto v___jp_1515_;
}
else
{
lean_dec_ref(v_otherwise_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v_reassigned_1495_);
return v___x_1549_;
}
}
}
v___jp_1551_:
{
if (lean_obj_tag(v_otherwise_x3f_1497_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___y_1539_ = v_rhs_1552_;
v_otherwise_1540_ = v___x_1559_;
v___y_1541_ = v___y_1553_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
v___y_1546_ = v___y_1558_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1561_; 
v_val_1560_ = lean_ctor_get(v_otherwise_x3f_1497_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v_otherwise_x3f_1497_, 1);
v___x_1561_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_1560_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v___y_1539_ = v_rhs_1552_;
v_otherwise_1540_ = v_a_1562_;
v___y_1541_ = v___y_1553_;
v___y_1542_ = v___y_1554_;
v___y_1543_ = v___y_1555_;
v___y_1544_ = v___y_1556_;
v___y_1545_ = v___y_1557_;
v___y_1546_ = v___y_1558_;
goto v___jp_1538_;
}
else
{
lean_dec_ref(v_rhs_1552_);
lean_dec(v_body_x3f_1498_);
lean_dec_ref(v_reassigned_1495_);
return v___x_1561_;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t v_reassignment_1669_, lean_object* v_decl_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v_reassigns_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v_decl_1670_);
v___x_1707_ = l_Lean_Syntax_isOfKind(v_decl_1670_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v_decl_1670_);
v___x_1709_ = l_Lean_Syntax_isOfKind(v_decl_1670_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1710_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1711_ = lean_box(0);
v___x_1712_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1711_, v___x_1709_);
v___x_1713_ = l_Std_Format_defWidth;
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = l_Std_Format_pretty(v___x_1712_, v___x_1713_, v___x_1714_, v___x_1714_);
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1710_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1717_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v_pattern_1720_; lean_object* v___y_1722_; lean_object* v_otherwise_x3f_1723_; lean_object* v_body_x3f_x3f_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v_body_x3f_x3f_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___x_1754_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1719_ = lean_unsigned_to_nat(0u);
v_pattern_1720_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1719_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1793_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1754_);
v___x_1794_ = l_Lean_Syntax_isNone(v___x_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
lean_inc(v___x_1793_);
v___x_1795_ = l_Lean_Syntax_matchesNull(v___x_1793_, v___x_1754_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec(v___x_1793_);
lean_dec(v_pattern_1720_);
v___x_1796_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1797_, v___x_1795_);
v___x_1799_ = l_Std_Format_defWidth;
v___x_1800_ = l_Std_Format_pretty(v___x_1798_, v___x_1799_, v___x_1719_, v___x_1719_);
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1796_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1802_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1719_);
lean_dec(v___x_1793_);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1806_ = l_Lean_Syntax_isOfKind(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v_pattern_1720_);
v___x_1807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1808_ = lean_box(0);
v___x_1809_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1808_, v___x_1806_);
v___x_1810_ = l_Std_Format_defWidth;
v___x_1811_ = l_Std_Format_pretty(v___x_1809_, v___x_1810_, v___x_1719_, v___x_1719_);
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1807_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1813_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1814_;
}
else
{
v___y_1756_ = v_a_1671_;
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
v___y_1761_ = v_a_1676_;
goto v___jp_1755_;
}
}
}
else
{
lean_dec(v___x_1793_);
v___y_1756_ = v_a_1671_;
v___y_1757_ = v_a_1672_;
v___y_1758_ = v_a_1673_;
v___y_1759_ = v_a_1674_;
v___y_1760_ = v_a_1675_;
v___y_1761_ = v_a_1676_;
goto v___jp_1755_;
}
v___jp_1721_:
{
if (v_reassignment_1669_ == 0)
{
lean_object* v___x_1731_; 
lean_dec(v_pattern_1720_);
v___x_1731_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1691_ = v___y_1722_;
v___y_1692_ = v_otherwise_x3f_1723_;
v___y_1693_ = v_body_x3f_x3f_1724_;
v_reassigns_1694_ = v___x_1731_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
goto v___jp_1690_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Elab_Do_getPatternVarsEx(v_pattern_1720_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___y_1691_ = v___y_1722_;
v___y_1692_ = v_otherwise_x3f_1723_;
v___y_1693_ = v_body_x3f_x3f_1724_;
v_reassigns_1694_ = v_a_1733_;
v___y_1695_ = v___y_1725_;
v___y_1696_ = v___y_1726_;
v___y_1697_ = v___y_1727_;
v___y_1698_ = v___y_1728_;
v___y_1699_ = v___y_1729_;
v___y_1700_ = v___y_1730_;
goto v___jp_1690_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_body_x3f_x3f_1724_);
lean_dec(v_otherwise_x3f_1723_);
lean_dec(v___y_1722_);
v_a_1734_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1732_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
v___jp_1742_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___y_1744_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_body_x3f_x3f_1745_);
v___y_1722_ = v___y_1743_;
v_otherwise_x3f_1723_ = v___x_1752_;
v_body_x3f_x3f_1724_ = v___x_1753_;
v___y_1725_ = v___y_1746_;
v___y_1726_ = v___y_1747_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1749_;
v___y_1729_ = v___y_1750_;
v___y_1730_ = v___y_1751_;
goto v___jp_1721_;
}
v___jp_1755_:
{
lean_object* v___x_1762_; lean_object* v_rhs_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1762_ = lean_unsigned_to_nat(3u);
v_rhs_1763_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1762_);
v___x_1764_ = lean_unsigned_to_nat(4u);
v___x_1765_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1764_);
v___x_1766_ = l_Lean_Syntax_isNone(v___x_1765_);
if (v___x_1766_ == 0)
{
uint8_t v___x_1767_; 
lean_inc(v___x_1765_);
v___x_1767_ = l_Lean_Syntax_matchesNull(v___x_1765_, v___x_1762_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v___x_1765_);
lean_dec(v_rhs_1763_);
lean_dec(v_pattern_1720_);
v___x_1768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1769_ = lean_box(0);
v___x_1770_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1769_, v___x_1767_);
v___x_1771_ = l_Std_Format_defWidth;
v___x_1772_ = l_Std_Format_pretty(v___x_1770_, v___x_1771_, v___x_1719_, v___x_1719_);
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1768_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1774_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v_otherwise_x3f_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1776_ = lean_unsigned_to_nat(2u);
v_otherwise_x3f_1777_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1754_);
v___x_1778_ = l_Lean_Syntax_getArg(v___x_1765_, v___x_1776_);
lean_dec(v___x_1765_);
v___x_1779_ = l_Lean_Syntax_isNone(v___x_1778_);
if (v___x_1779_ == 0)
{
uint8_t v___x_1780_; 
lean_inc(v___x_1778_);
v___x_1780_ = l_Lean_Syntax_matchesNull(v___x_1778_, v___x_1754_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v___x_1778_);
lean_dec(v_otherwise_x3f_1777_);
lean_dec(v_rhs_1763_);
lean_dec(v_pattern_1720_);
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1782_ = lean_box(0);
v___x_1783_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1782_, v___x_1780_);
v___x_1784_ = l_Std_Format_defWidth;
v___x_1785_ = l_Std_Format_pretty(v___x_1783_, v___x_1784_, v___x_1719_, v___x_1719_);
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1781_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1787_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1788_;
}
else
{
lean_object* v_body_x3f_x3f_1789_; lean_object* v___x_1790_; 
lean_dec(v_decl_1670_);
v_body_x3f_x3f_1789_ = l_Lean_Syntax_getArg(v___x_1778_, v___x_1719_);
lean_dec(v___x_1778_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_body_x3f_x3f_1789_);
v___y_1743_ = v_rhs_1763_;
v___y_1744_ = v_otherwise_x3f_1777_;
v_body_x3f_x3f_1745_ = v___x_1790_;
v___y_1746_ = v___y_1756_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
v___y_1751_ = v___y_1761_;
goto v___jp_1742_;
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v___x_1778_);
lean_dec(v_decl_1670_);
v___x_1791_ = lean_box(0);
v___y_1743_ = v_rhs_1763_;
v___y_1744_ = v_otherwise_x3f_1777_;
v_body_x3f_x3f_1745_ = v___x_1791_;
v___y_1746_ = v___y_1756_;
v___y_1747_ = v___y_1757_;
v___y_1748_ = v___y_1758_;
v___y_1749_ = v___y_1759_;
v___y_1750_ = v___y_1760_;
v___y_1751_ = v___y_1761_;
goto v___jp_1742_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v___x_1765_);
lean_dec(v_decl_1670_);
v___x_1792_ = lean_box(0);
v___y_1722_ = v_rhs_1763_;
v_otherwise_x3f_1723_ = v___x_1792_;
v_body_x3f_x3f_1724_ = v___x_1792_;
v___y_1725_ = v___y_1756_;
v___y_1726_ = v___y_1757_;
v___y_1727_ = v___y_1758_;
v___y_1728_ = v___y_1759_;
v___y_1729_ = v___y_1760_;
v___y_1730_ = v___y_1761_;
goto v___jp_1721_;
}
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v_x_1816_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v_x_1816_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1815_);
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10));
lean_inc(v_x_1816_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v_x_1816_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec(v_x_1816_);
v___x_1832_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1833_ = lean_box(0);
v___x_1834_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1833_, v___x_1831_);
v___x_1835_ = l_Std_Format_defWidth;
v___x_1836_ = l_Std_Format_pretty(v___x_1834_, v___x_1835_, v___x_1815_, v___x_1815_);
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1832_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1838_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1840_);
v___x_1842_ = l_Lean_Syntax_isNone(v___x_1841_);
if (v___x_1842_ == 0)
{
uint8_t v___x_1843_; 
lean_inc(v___x_1841_);
v___x_1843_ = l_Lean_Syntax_matchesNull(v___x_1841_, v___x_1840_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec(v___x_1841_);
lean_dec(v_x_1816_);
v___x_1844_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1845_, v___x_1843_);
v___x_1847_ = l_Std_Format_defWidth;
v___x_1848_ = l_Std_Format_pretty(v___x_1846_, v___x_1847_, v___x_1815_, v___x_1815_);
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1844_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1850_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = l_Lean_Syntax_getArg(v___x_1841_, v___x_1815_);
lean_dec(v___x_1841_);
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8));
v___x_1854_ = l_Lean_Syntax_isOfKind(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec(v_x_1816_);
v___x_1855_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
v___x_1856_ = lean_box(0);
v___x_1857_ = l_Lean_Syntax_formatStx(v_decl_1670_, v___x_1856_, v___x_1854_);
v___x_1858_ = l_Std_Format_defWidth;
v___x_1859_ = l_Std_Format_pretty(v___x_1857_, v___x_1858_, v___x_1815_, v___x_1815_);
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1855_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_1861_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v___x_1862_;
}
else
{
v___y_1818_ = v_a_1671_;
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
v___y_1823_ = v_a_1676_;
goto v___jp_1817_;
}
}
}
else
{
lean_dec(v___x_1841_);
v___y_1818_ = v_a_1671_;
v___y_1819_ = v_a_1672_;
v___y_1820_ = v_a_1673_;
v___y_1821_ = v_a_1674_;
v___y_1822_ = v_a_1675_;
v___y_1823_ = v_a_1676_;
goto v___jp_1817_;
}
}
v___jp_1817_:
{
lean_object* v___x_1824_; lean_object* v_rhs_1825_; 
v___x_1824_ = lean_unsigned_to_nat(3u);
v_rhs_1825_ = l_Lean_Syntax_getArg(v_decl_1670_, v___x_1824_);
lean_dec(v_decl_1670_);
if (v_reassignment_1669_ == 0)
{
lean_object* v___x_1826_; 
lean_dec(v_x_1816_);
v___x_1826_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___y_1679_ = v___y_1823_;
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1821_;
v___y_1682_ = v___y_1818_;
v___y_1683_ = v___y_1822_;
v___y_1684_ = v___y_1819_;
v___y_1685_ = v_rhs_1825_;
v___y_1686_ = v___x_1826_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_mk_empty_array_with_capacity(v___x_1827_);
v___x_1829_ = lean_array_push(v___x_1828_, v_x_1816_);
v___y_1679_ = v___y_1823_;
v___y_1680_ = v___y_1820_;
v___y_1681_ = v___y_1821_;
v___y_1682_ = v___y_1818_;
v___y_1683_ = v___y_1822_;
v___y_1684_ = v___y_1819_;
v___y_1685_ = v_rhs_1825_;
v___y_1686_ = v___x_1829_;
goto v___jp_1678_;
}
}
}
v___jp_1678_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___y_1685_);
v___x_1688_ = lean_box(0);
v___x_1689_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___y_1686_, v___x_1687_, v___x_1688_, v___x_1688_, v___y_1682_, v___y_1684_, v___y_1680_, v___y_1681_, v___y_1683_, v___y_1679_);
return v___x_1689_;
}
v___jp_1690_:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___y_1691_);
if (lean_obj_tag(v___y_1693_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1694_, v___x_1701_, v___y_1692_, v___x_1702_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1703_;
}
else
{
lean_object* v_val_1704_; lean_object* v___x_1705_; 
v_val_1704_ = lean_ctor_get(v___y_1693_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v___y_1693_, 1);
v___x_1705_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigns_1694_, v___x_1701_, v___y_1692_, v_val_1704_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* v_as_1985_, size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_usize_dec_lt(v_i_1987_, v_sz_1986_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1988_);
return v___x_1997_;
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; 
v_a_1998_ = lean_array_uget_borrowed(v_as_1985_, v_i_1987_);
lean_inc(v_a_1998_);
v___x_1999_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_a_1998_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2000_, v_b_1988_);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1987_, v___x_2002_);
v_i_1987_ = v___x_2003_;
v_b_1988_ = v___x_2001_;
goto _start;
}
else
{
lean_dec_ref(v_b_1988_);
return v___x_1999_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
v___x_2019_ = l_Lean_stringToMessageData(v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t v___x_2034_, lean_object* v_as_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_a_2047_; uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2037_, v_sz_2036_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_b_2038_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; lean_object* v_a_2054_; uint8_t v___x_2055_; 
v___x_2053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2054_ = lean_array_uget_borrowed(v_as_2035_, v_i_2037_);
lean_inc(v_a_2054_);
v___x_2055_ = l_Lean_Syntax_isOfKind(v_a_2054_, v___x_2053_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
v_a_2047_ = v_b_2038_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_b_2038_);
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = l_Lean_Syntax_getArg(v_a_2054_, v___x_2084_);
v___x_2086_ = l_Lean_Syntax_getArgs(v___x_2085_);
lean_dec(v___x_2085_);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2089_ = lean_array_get_size(v___x_2086_);
v___x_2090_ = lean_nat_dec_lt(v___x_2087_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v___x_2086_);
v___y_2067_ = v___x_2088_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v_snd_2096_; 
v___x_2091_ = lean_box(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2088_);
v___x_2093_ = ((size_t)0ULL);
v___x_2094_ = lean_usize_of_nat(v___x_2089_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2055_, v___x_2034_, v___x_2086_, v___x_2093_, v___x_2094_, v___x_2092_);
lean_dec_ref(v___x_2086_);
v_snd_2096_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_snd_2096_);
lean_dec_ref(v___x_2095_);
v___y_2067_ = v_snd_2096_;
goto v___jp_2066_;
}
v___jp_2066_:
{
size_t v_sz_2068_; size_t v___x_2069_; lean_object* v___x_2070_; 
v_sz_2068_ = lean_array_size(v___y_2067_);
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2068_, v___x_2069_, v___y_2067_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref_known(v___x_2071_, 1);
v_a_2047_ = v_b_2038_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_b_2038_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec_ref_known(v___x_2070_, 1);
v___x_2080_ = l_Lean_Syntax_getArg(v_a_2054_, v___x_2065_);
v___x_2081_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2080_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2038_, v_a_2082_);
v_a_2047_ = v___x_2083_;
goto v___jp_2046_;
}
else
{
lean_dec_ref(v_b_2038_);
return v___x_2081_;
}
}
}
}
}
v___jp_2046_:
{
size_t v___x_2048_; size_t v___x_2049_; 
v___x_2048_ = ((size_t)1ULL);
v___x_2049_ = lean_usize_add(v_i_2037_, v___x_2048_);
v_i_2037_ = v___x_2049_;
v_b_2038_ = v_a_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* v_as_2097_, size_t v_sz_2098_, size_t v_i_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_a_2109_; uint8_t v___x_2113_; 
v___x_2113_ = lean_usize_dec_lt(v_i_2099_, v_sz_2098_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_b_2100_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v_a_2116_ = lean_array_uget_borrowed(v_as_2097_, v_i_2099_);
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(v_a_2116_);
v___x_2130_ = l_Lean_Syntax_isOfKind(v_a_2116_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(v_a_2116_);
v___x_2132_ = l_Lean_Syntax_isOfKind(v_a_2116_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2134_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2135_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2134_, v___x_2132_);
v___x_2136_ = l_Std_Format_defWidth;
v___x_2137_ = l_Std_Format_pretty(v___x_2135_, v___x_2136_, v___x_2115_, v___x_2115_);
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2133_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2139_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref_known(v___x_2140_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_b_2100_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2149_);
v___x_2151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_2150_);
v___x_2152_ = l_Lean_Syntax_isOfKind(v___x_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v___x_2150_);
v___x_2153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2154_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2155_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2154_, v___x_2152_);
v___x_2156_ = l_Std_Format_defWidth;
v___x_2157_ = l_Std_Format_pretty(v___x_2155_, v___x_2156_, v___x_2115_, v___x_2115_);
v___x_2158_ = l_Lean_stringToMessageData(v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2153_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2159_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_dec_ref_known(v___x_2160_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v_b_2100_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2169_ = l_Lean_Syntax_getArg(v___x_2150_, v___x_2115_);
lean_dec(v___x_2150_);
v___x_2170_ = l_Lean_Syntax_getArgs(v___x_2169_);
lean_dec(v___x_2169_);
v_sz_2171_ = lean_array_size(v___x_2170_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_2130_, v___x_2170_, v_sz_2171_, v___x_2172_, v_b_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec_ref(v___x_2170_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v_a_2109_ = v_a_2174_;
goto v___jp_2108_;
}
else
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_unsigned_to_nat(2u);
v___x_2176_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2175_);
v___x_2177_ = l_Lean_Syntax_isNone(v___x_2176_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_Syntax_matchesNull(v___x_2176_, v___x_2175_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2179_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
v___x_2180_ = lean_box(0);
lean_inc(v_a_2116_);
v___x_2181_ = l_Lean_Syntax_formatStx(v_a_2116_, v___x_2180_, v___x_2178_);
v___x_2182_ = l_Std_Format_defWidth;
v___x_2183_ = l_Std_Format_pretty(v___x_2181_, v___x_2182_, v___x_2115_, v___x_2115_);
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2179_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2185_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_dec_ref_known(v___x_2186_, 1);
v_a_2109_ = v_b_2100_;
goto v___jp_2108_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_b_2100_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
v___y_2118_ = v___y_2101_;
v___y_2119_ = v___y_2102_;
v___y_2120_ = v___y_2103_;
v___y_2121_ = v___y_2104_;
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
goto v___jp_2117_;
}
}
else
{
lean_dec(v___x_2176_);
v___y_2118_ = v___y_2101_;
v___y_2119_ = v___y_2102_;
v___y_2120_ = v___y_2103_;
v___y_2121_ = v___y_2104_;
v___y_2122_ = v___y_2105_;
v___y_2123_ = v___y_2106_;
goto v___jp_2117_;
}
}
v___jp_2117_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = lean_unsigned_to_nat(4u);
v___x_2125_ = l_Lean_Syntax_getArg(v_a_2116_, v___x_2124_);
v___x_2126_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2125_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_2127_, v_b_2100_);
v_a_2109_ = v___x_2128_;
goto v___jp_2108_;
}
else
{
lean_dec_ref(v_b_2100_);
return v___x_2126_;
}
}
}
v___jp_2108_:
{
size_t v___x_2110_; size_t v___x_2111_; 
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_add(v_i_2099_, v___x_2110_);
v_i_2099_ = v___x_2111_;
v_b_2100_ = v_a_2109_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* v_stx_x3f_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
if (lean_obj_tag(v_stx_x3f_2195_) == 0)
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
else
{
lean_object* v_val_2205_; lean_object* v___x_2206_; 
v_val_2205_ = lean_ctor_get(v_stx_x3f_2195_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v_stx_x3f_2195_, 1);
v___x_2206_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2205_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t v___x_2225_, lean_object* v_as_2226_, size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_b_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_a_2238_; uint8_t v___x_2242_; 
v___x_2242_ = lean_usize_dec_lt(v_i_2228_, v_sz_2227_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_b_2229_);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; lean_object* v_a_2245_; uint8_t v___x_2246_; 
v___x_2244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
v_a_2245_ = lean_array_uget_borrowed(v_as_2226_, v_i_2228_);
lean_inc(v_a_2245_);
v___x_2246_ = l_Lean_Syntax_isOfKind(v_a_2245_, v___x_2244_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_dec_ref_known(v___x_2247_, 1);
v_a_2238_ = v_b_2229_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_b_2229_);
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___y_2258_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2256_ = lean_unsigned_to_nat(3u);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = l_Lean_Syntax_getArg(v_a_2245_, v___x_2275_);
v___x_2277_ = l_Lean_Syntax_getArgs(v___x_2276_);
lean_dec(v___x_2276_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_2280_ = lean_array_get_size(v___x_2277_);
v___x_2281_ = lean_nat_dec_lt(v___x_2278_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec_ref(v___x_2277_);
v___y_2258_ = v___x_2279_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; lean_object* v___x_2286_; lean_object* v_snd_2287_; 
v___x_2282_ = lean_box(v___x_2281_);
v___x_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
lean_ctor_set(v___x_2283_, 1, v___x_2279_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = lean_usize_of_nat(v___x_2280_);
v___x_2286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2246_, v___x_2225_, v___x_2277_, v___x_2284_, v___x_2285_, v___x_2283_);
lean_dec_ref(v___x_2277_);
v_snd_2287_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_snd_2287_);
lean_dec_ref(v___x_2286_);
v___y_2258_ = v_snd_2287_;
goto v___jp_2257_;
}
v___jp_2257_:
{
size_t v_sz_2259_; size_t v___x_2260_; lean_object* v___x_2261_; 
v_sz_2259_ = lean_array_size(v___y_2258_);
v___x_2260_ = ((size_t)0ULL);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(v_sz_2259_, v___x_2260_, v___y_2258_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_dec_ref_known(v___x_2262_, 1);
v_a_2238_ = v_b_2229_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v_b_2229_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref_known(v___x_2261_, 1);
v___x_2271_ = l_Lean_Syntax_getArg(v_a_2245_, v___x_2256_);
v___x_2272_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2271_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v___x_2274_ = l_Lean_Elab_Do_ControlInfo_alternative(v_b_2229_, v_a_2273_);
v_a_2238_ = v___x_2274_;
goto v___jp_2237_;
}
else
{
lean_dec_ref(v_b_2229_);
return v___x_2272_;
}
}
}
}
}
v___jp_2237_:
{
size_t v___x_2239_; size_t v___x_2240_; 
v___x_2239_ = ((size_t)1ULL);
v___x_2240_ = lean_usize_add(v_i_2228_, v___x_2239_);
v_i_2228_ = v___x_2240_;
v_b_2229_ = v_a_2238_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2324_ = l_Lean_NameSet_empty;
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = 0;
v___x_2327_ = 1;
v___x_2328_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___x_2324_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*2, v___x_2327_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*2 + 1, v___x_2326_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*2 + 2, v___x_2326_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*2 + 3, v___x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* v_stx_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___y_2338_; lean_object* v_bodyInfo_2339_; lean_object* v___y_2343_; lean_object* v_bodyInfo_2344_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___x_2384_; lean_object* v_env_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2384_ = lean_st_ref_get(v_a_2335_);
v_env_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc_ref(v_env_2385_);
lean_dec(v___x_2384_);
lean_inc(v_stx_2329_);
v___x_2386_ = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(v___x_2386_, 0, v_env_2385_);
lean_closure_set(v___x_2386_, 1, v_stx_2329_);
v___x_2387_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2386_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_4891_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_4891_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_4891_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
if (lean_obj_tag(v_a_2388_) == 1)
{
lean_object* v_val_2400_; lean_object* v_snd_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_del_object(v___x_2390_);
lean_dec(v_stx_2329_);
v_val_2400_ = lean_ctor_get(v_a_2388_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v_a_2388_, 1);
v_snd_2401_ = lean_ctor_get(v_val_2400_, 1);
lean_inc(v_snd_2401_);
lean_dec(v_val_2400_);
v___x_2402_ = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(v___x_2402_, 0, lean_box(0));
lean_closure_set(v___x_2402_, 1, v_snd_2401_);
v___x_2403_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v___x_2402_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v_stx_2329_ = v_a_2404_;
goto _start;
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_a_2406_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2403_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2403_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v___x_2414_; uint8_t v___x_2415_; uint8_t v___x_2416_; 
lean_dec(v_a_2388_);
v___x_2414_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
lean_inc(v_stx_2329_);
v___x_2415_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2414_);
v___x_2416_ = 1;
if (v___x_2415_ == 0)
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3));
lean_inc(v_stx_2329_);
v___x_2418_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5));
lean_inc(v_stx_2329_);
v___x_2420_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7));
lean_inc(v_stx_2329_);
v___x_2422_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; 
v___x_2423_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9));
lean_inc(v_stx_2329_);
v___x_2424_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(v_stx_2329_);
v___x_2540_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(v_stx_2329_);
v___x_2593_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; uint8_t v___x_2595_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; 
v___x_2594_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(v_stx_2329_);
v___x_2595_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___y_2656_; lean_object* v___y_2657_; lean_object* v___y_2658_; lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2666_; lean_object* v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; 
lean_del_object(v___x_2390_);
v___x_2653_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(v_stx_2329_);
v___x_2654_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2722_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(v_stx_2329_);
v___x_2723_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(v_stx_2329_);
v___x_2725_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(v_stx_2329_);
v___x_2727_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(v_stx_2329_);
v___x_2729_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(v_stx_2329_);
v___x_2731_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(v_stx_2329_);
v___x_2733_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; uint8_t v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; uint8_t v___y_2740_; 
v___x_2734_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(v_stx_2329_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(v_stx_2329_);
v___x_2744_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(v_stx_2329_);
v___x_2746_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50));
lean_inc(v_stx_2329_);
v___x_2748_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52));
lean_inc(v_stx_2329_);
v___x_2750_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54));
lean_inc(v_stx_2329_);
v___x_2752_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56));
lean_inc(v_stx_2329_);
v___x_2754_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58));
lean_inc(v_stx_2329_);
v___x_2756_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60));
lean_inc(v_stx_2329_);
v___x_2758_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62));
lean_inc(v_stx_2329_);
v___x_2760_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64));
lean_inc(v_stx_2329_);
v___x_2762_ = l_Lean_Syntax_isOfKind(v_stx_2329_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; lean_object* v_env_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2763_ = lean_st_ref_get(v_a_2335_);
v_env_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc_ref(v_env_2764_);
lean_dec(v___x_2763_);
lean_inc_n(v_stx_2329_, 2);
v___x_2765_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2766_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2767_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2766_, v_env_2764_, v___x_2765_);
v___x_2768_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2769_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2767_, v___x_2768_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_2767_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2800_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2800_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_fst_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2798_; 
v_fst_2774_ = lean_ctor_get(v_a_2770_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v_a_2770_, 1);
lean_dec(v_unused_2799_);
v___x_2776_ = v_a_2770_;
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_fst_2774_);
lean_dec(v_a_2770_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
if (lean_obj_tag(v_fst_2774_) == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_del_object(v___x_2772_);
v___x_2778_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2779_ = l_Lean_MessageData_ofName(v___x_2765_);
lean_inc_ref(v___x_2779_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2779_);
lean_ctor_set(v___x_2776_, 0, v___x_2778_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2782_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2781_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
v___x_2784_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2785_ = l_Lean_indentD(v___x_2784_);
v___x_2786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2783_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2779_);
v___x_2790_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2791_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2792_;
}
}
else
{
lean_object* v_val_2794_; lean_object* v___x_2796_; 
lean_del_object(v___x_2776_);
lean_dec(v___x_2765_);
lean_dec(v_stx_2329_);
v_val_2794_ = lean_ctor_get(v_fst_2774_, 0);
lean_inc(v_val_2794_);
lean_dec_ref_known(v_fst_2774_, 1);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v_val_2794_);
v___x_2796_ = v___x_2772_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_val_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v___x_2765_);
lean_dec(v_stx_2329_);
v_a_2801_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2769_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2769_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___y_2813_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_unsigned_to_nat(5u);
v___x_2811_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2810_);
v___x_2822_ = lean_unsigned_to_nat(6u);
v___x_2823_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2822_);
lean_dec(v_stx_2329_);
v___x_2824_ = l_Lean_Syntax_getOptional_x3f(v___x_2823_);
lean_dec(v___x_2823_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_box(0);
v___y_2813_ = v___x_2825_;
goto v___jp_2812_;
}
else
{
lean_object* v_val_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
v_val_2826_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2824_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_val_2826_);
lean_dec(v___x_2824_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_val_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
v___y_2813_ = v___x_2831_;
goto v___jp_2812_;
}
}
}
v___jp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2811_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2814_) == 0)
{
if (lean_obj_tag(v___y_2813_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = l_Lean_NameSet_empty;
v___x_2817_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2817_, 0, v___x_2809_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2, v___x_2760_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2 + 1, v___x_2760_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2 + 2, v___x_2760_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2 + 3, v___x_2760_);
v___y_2338_ = v_a_2815_;
v_bodyInfo_2339_ = v___x_2817_;
goto v___jp_2337_;
}
else
{
lean_object* v_a_2818_; lean_object* v_val_2819_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2814_, 1);
v_val_2819_ = lean_ctor_get(v___y_2813_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v___y_2813_, 1);
v___x_2820_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2819_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___y_2338_ = v_a_2818_;
v_bodyInfo_2339_ = v_a_2821_;
goto v___jp_2337_;
}
else
{
lean_dec(v_a_2818_);
return v___x_2820_;
}
}
}
else
{
lean_dec(v___y_2813_);
return v___x_2814_;
}
}
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___y_2838_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2834_ = lean_unsigned_to_nat(1u);
v___x_2835_ = lean_unsigned_to_nat(5u);
v___x_2836_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2835_);
v___x_2847_ = lean_unsigned_to_nat(6u);
v___x_2848_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2847_);
lean_dec(v_stx_2329_);
v___x_2849_ = l_Lean_Syntax_getOptional_x3f(v___x_2848_);
lean_dec(v___x_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_box(0);
v___y_2838_ = v___x_2850_;
goto v___jp_2837_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_val_2851_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2849_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_val_2851_);
lean_dec(v___x_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_val_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v___y_2838_ = v___x_2856_;
goto v___jp_2837_;
}
}
}
v___jp_2837_:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_2836_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2839_) == 0)
{
if (lean_obj_tag(v___y_2838_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Lean_NameSet_empty;
v___x_2842_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2842_, 0, v___x_2834_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*2, v___x_2758_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*2 + 1, v___x_2758_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*2 + 2, v___x_2758_);
lean_ctor_set_uint8(v___x_2842_, sizeof(void*)*2 + 3, v___x_2758_);
v___y_2343_ = v_a_2840_;
v_bodyInfo_2344_ = v___x_2842_;
goto v___jp_2342_;
}
else
{
lean_object* v_a_2843_; lean_object* v_val_2844_; lean_object* v___x_2845_; 
v_a_2843_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2839_, 1);
v_val_2844_ = lean_ctor_get(v___y_2838_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v___y_2838_, 1);
v___x_2845_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_val_2844_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v___y_2343_ = v_a_2843_;
v_bodyInfo_2344_ = v_a_2846_;
goto v___jp_2342_;
}
else
{
lean_dec(v_a_2843_);
return v___x_2845_;
}
}
}
else
{
lean_dec(v___y_2838_);
return v___x_2839_;
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = lean_unsigned_to_nat(1u);
v___x_3074_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2860_);
v___x_3075_ = l_Lean_Syntax_isNone(v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3076_ = lean_unsigned_to_nat(5u);
v___x_3077_ = l_Lean_Syntax_matchesNull(v___x_3074_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v_env_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3078_ = lean_st_ref_get(v_a_2335_);
v_env_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc_ref(v_env_3079_);
lean_dec(v___x_3078_);
lean_inc_n(v_stx_2329_, 2);
v___x_3080_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3081_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3082_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3081_, v_env_3079_, v___x_3080_);
v___x_3083_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3084_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3082_, v___x_3083_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3082_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3115_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3115_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3115_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_fst_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3113_; 
v_fst_3089_ = lean_ctor_get(v_a_3085_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_a_3085_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_a_3085_, 1);
lean_dec(v_unused_3114_);
v___x_3091_ = v_a_3085_;
v_isShared_3092_ = v_isSharedCheck_3113_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_fst_3089_);
lean_dec(v_a_3085_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3113_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
if (lean_obj_tag(v_fst_3089_) == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_del_object(v___x_3087_);
v___x_3093_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3094_ = l_Lean_MessageData_ofName(v___x_3080_);
lean_inc_ref(v___x_3094_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 7);
lean_ctor_set(v___x_3091_, 1, v___x_3094_);
lean_ctor_set(v___x_3091_, 0, v___x_3093_);
v___x_3096_ = v___x_3091_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3097_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3100_ = l_Lean_indentD(v___x_3099_);
v___x_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3098_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v___x_3094_);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3106_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3107_;
}
}
else
{
lean_object* v_val_3109_; lean_object* v___x_3111_; 
lean_del_object(v___x_3091_);
lean_dec(v___x_3080_);
lean_dec(v_stx_2329_);
v_val_3109_ = lean_ctor_get(v_fst_3089_, 0);
lean_inc(v_val_3109_);
lean_dec_ref_known(v_fst_3089_, 1);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v_val_3109_);
v___x_3111_ = v___x_3087_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_val_3109_);
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
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v___x_3080_);
lean_dec(v_stx_2329_);
v_a_3116_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3084_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3084_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
v___y_2862_ = v_a_2330_;
v___y_2863_ = v_a_2331_;
v___y_2864_ = v_a_2332_;
v___y_2865_ = v_a_2333_;
v___y_2866_ = v_a_2334_;
v___y_2867_ = v_a_2335_;
goto v___jp_2861_;
}
}
else
{
lean_dec(v___x_3074_);
v___y_2862_ = v_a_2330_;
v___y_2863_ = v_a_2331_;
v___y_2864_ = v_a_2332_;
v___y_2865_ = v_a_2333_;
v___y_2866_ = v_a_2334_;
v___y_2867_ = v_a_2335_;
goto v___jp_2861_;
}
v___jp_2861_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2868_ = lean_unsigned_to_nat(4u);
v___x_2869_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2868_);
v___x_2870_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66));
lean_inc(v___x_2869_);
v___x_2871_ = l_Lean_Syntax_isOfKind(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v_env_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec(v___x_2869_);
v___x_2872_ = lean_st_ref_get(v___y_2867_);
v_env_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc_ref(v_env_2873_);
lean_dec(v___x_2872_);
lean_inc_n(v_stx_2329_, 2);
v___x_2874_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2875_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2876_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2875_, v_env_2873_, v___x_2874_);
v___x_2877_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2878_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2876_, v___x_2877_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___x_2876_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2909_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2909_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2909_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_fst_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2907_; 
v_fst_2883_ = lean_ctor_get(v_a_2879_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v_a_2879_);
if (v_isSharedCheck_2907_ == 0)
{
lean_object* v_unused_2908_; 
v_unused_2908_ = lean_ctor_get(v_a_2879_, 1);
lean_dec(v_unused_2908_);
v___x_2885_ = v_a_2879_;
v_isShared_2886_ = v_isSharedCheck_2907_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_fst_2883_);
lean_dec(v_a_2879_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2907_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
if (lean_obj_tag(v_fst_2883_) == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
lean_del_object(v___x_2881_);
v___x_2887_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2888_ = l_Lean_MessageData_ofName(v___x_2874_);
lean_inc_ref(v___x_2888_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 7);
lean_ctor_set(v___x_2885_, 1, v___x_2888_);
lean_ctor_set(v___x_2885_, 0, v___x_2887_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2891_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2894_ = l_Lean_indentD(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2892_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v___x_2888_);
v___x_2899_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2900_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_2901_;
}
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2905_; 
lean_del_object(v___x_2885_);
lean_dec(v___x_2874_);
lean_dec(v_stx_2329_);
v_val_2903_ = lean_ctor_get(v_fst_2883_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v_fst_2883_, 1);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v_val_2903_);
v___x_2905_ = v___x_2881_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_val_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v___x_2874_);
lean_dec(v_stx_2329_);
v_a_2910_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2878_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2878_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; size_t v_sz_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___x_2918_ = l_Lean_Syntax_getArg(v___x_2869_, v___x_2859_);
v___x_2919_ = l_Lean_Syntax_getArgs(v___x_2918_);
lean_dec(v___x_2918_);
v_sz_2920_ = lean_array_size(v___x_2919_);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(v___x_2756_, v_sz_2920_, v___x_2921_, v___x_2919_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v_env_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v___x_2869_);
v___x_2923_ = lean_st_ref_get(v___y_2867_);
v_env_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref(v_env_2924_);
lean_dec(v___x_2923_);
lean_inc_n(v_stx_2329_, 2);
v___x_2925_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2926_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2927_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2926_, v_env_2924_, v___x_2925_);
v___x_2928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2929_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2927_, v___x_2928_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___x_2927_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2960_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2960_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2960_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_fst_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2958_; 
v_fst_2934_ = lean_ctor_get(v_a_2930_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v_a_2930_, 1);
lean_dec(v_unused_2959_);
v___x_2936_ = v_a_2930_;
v_isShared_2937_ = v_isSharedCheck_2958_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_fst_2934_);
lean_dec(v_a_2930_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2958_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
if (lean_obj_tag(v_fst_2934_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_del_object(v___x_2932_);
v___x_2938_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2939_ = l_Lean_MessageData_ofName(v___x_2925_);
lean_inc_ref(v___x_2939_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 7);
lean_ctor_set(v___x_2936_, 1, v___x_2939_);
lean_ctor_set(v___x_2936_, 0, v___x_2938_);
v___x_2941_ = v___x_2936_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2942_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2945_ = l_Lean_indentD(v___x_2944_);
v___x_2946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2943_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2939_);
v___x_2950_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2951_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_2952_;
}
}
else
{
lean_object* v_val_2954_; lean_object* v___x_2956_; 
lean_del_object(v___x_2936_);
lean_dec(v___x_2925_);
lean_dec(v_stx_2329_);
v_val_2954_ = lean_ctor_get(v_fst_2934_, 0);
lean_inc(v_val_2954_);
lean_dec_ref_known(v_fst_2934_, 1);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v_val_2954_);
v___x_2956_ = v___x_2932_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_val_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v___x_2925_);
lean_dec(v_stx_2329_);
v_a_2961_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2929_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2929_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_val_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_val_2969_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_val_2969_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2970_ = l_Lean_Syntax_getArg(v___x_2869_, v___x_2860_);
lean_dec(v___x_2869_);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68));
lean_inc(v___x_2970_);
v___x_2972_ = l_Lean_Syntax_isOfKind(v___x_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v_env_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec(v___x_2970_);
lean_dec(v_val_2969_);
v___x_2973_ = lean_st_ref_get(v___y_2867_);
v_env_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_ref(v_env_2974_);
lean_dec(v___x_2973_);
lean_inc_n(v_stx_2329_, 2);
v___x_2975_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2976_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2977_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2976_, v_env_2974_, v___x_2975_);
v___x_2978_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2979_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2977_, v___x_2978_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___x_2977_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3010_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_3010_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3010_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_fst_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3008_; 
v_fst_2984_ = lean_ctor_get(v_a_2980_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v_a_2980_, 1);
lean_dec(v_unused_3009_);
v___x_2986_ = v_a_2980_;
v_isShared_2987_ = v_isSharedCheck_3008_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_fst_2984_);
lean_dec(v_a_2980_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3008_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
if (lean_obj_tag(v_fst_2984_) == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
lean_del_object(v___x_2982_);
v___x_2988_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2989_ = l_Lean_MessageData_ofName(v___x_2975_);
lean_inc_ref(v___x_2989_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 7);
lean_ctor_set(v___x_2986_, 1, v___x_2989_);
lean_ctor_set(v___x_2986_, 0, v___x_2988_);
v___x_2991_ = v___x_2986_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2992_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2995_ = l_Lean_indentD(v___x_2994_);
v___x_2996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2993_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v___x_2989_);
v___x_3000_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3001_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_3002_;
}
}
else
{
lean_object* v_val_3004_; lean_object* v___x_3006_; 
lean_del_object(v___x_2986_);
lean_dec(v___x_2975_);
lean_dec(v_stx_2329_);
v_val_3004_ = lean_ctor_get(v_fst_2984_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v_fst_2984_, 1);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v_val_3004_);
v___x_3006_ = v___x_2982_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_val_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v___x_2975_);
lean_dec(v_stx_2329_);
v_a_3011_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2979_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2979_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; 
v___x_3019_ = l_Lean_Syntax_getArg(v___x_2970_, v___x_2860_);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70));
v___x_3021_ = l_Lean_Syntax_isOfKind(v___x_3019_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v_env_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec(v___x_2970_);
lean_dec(v_val_2969_);
v___x_3022_ = lean_st_ref_get(v___y_2867_);
v_env_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_env_3023_);
lean_dec(v___x_3022_);
lean_inc_n(v_stx_2329_, 2);
v___x_3024_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3025_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3026_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3025_, v_env_3023_, v___x_3024_);
v___x_3027_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3028_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3026_, v___x_3027_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___x_3026_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3059_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3059_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3059_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_fst_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3057_; 
v_fst_3033_ = lean_ctor_get(v_a_3029_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_a_3029_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v_a_3029_, 1);
lean_dec(v_unused_3058_);
v___x_3035_ = v_a_3029_;
v_isShared_3036_ = v_isSharedCheck_3057_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_fst_3033_);
lean_dec(v_a_3029_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3057_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
if (lean_obj_tag(v_fst_3033_) == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
lean_del_object(v___x_3031_);
v___x_3037_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3038_ = l_Lean_MessageData_ofName(v___x_3024_);
lean_inc_ref(v___x_3038_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set_tag(v___x_3035_, 7);
lean_ctor_set(v___x_3035_, 1, v___x_3038_);
lean_ctor_set(v___x_3035_, 0, v___x_3037_);
v___x_3040_ = v___x_3035_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3041_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3044_ = l_Lean_indentD(v___x_3043_);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3042_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
lean_ctor_set(v___x_3048_, 1, v___x_3038_);
v___x_3049_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3050_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_3051_;
}
}
else
{
lean_object* v_val_3053_; lean_object* v___x_3055_; 
lean_del_object(v___x_3035_);
lean_dec(v___x_3024_);
lean_dec(v_stx_2329_);
v_val_3053_ = lean_ctor_get(v_fst_3033_, 0);
lean_inc(v_val_3053_);
lean_dec_ref_known(v_fst_3033_, 1);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_val_3053_);
v___x_3055_ = v___x_3031_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_val_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v___x_3024_);
lean_dec(v_stx_2329_);
v_a_3060_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3028_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3028_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec(v_stx_2329_);
v___x_3068_ = lean_unsigned_to_nat(3u);
v___x_3069_ = l_Lean_Syntax_getArg(v___x_2970_, v___x_3068_);
lean_dec(v___x_2970_);
v___x_3070_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3069_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; size_t v_sz_3072_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v_sz_3072_ = lean_array_size(v_val_2969_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_val_2969_, v_sz_3072_, v___x_2921_, v_a_3071_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v_val_2969_);
return v___x_3073_;
}
else
{
lean_dec(v_val_2969_);
return v___x_3070_;
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
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_dec(v_stx_2329_);
v___x_3124_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
return v___x_3125_;
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_stx_2329_);
v___x_3126_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_dec(v_stx_2329_);
v___x_3128_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
return v___x_3129_;
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v_stx_2329_);
v___x_3130_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_stx_2329_);
v___x_3132_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
}
else
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; size_t v_sz_3137_; size_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3134_ = lean_unsigned_to_nat(2u);
v___x_3135_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3134_);
v___x_3136_ = l_Lean_Syntax_getArgs(v___x_3135_);
lean_dec(v___x_3135_);
v_sz_3137_ = lean_array_size(v___x_3136_);
v___x_3138_ = ((size_t)0ULL);
v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(v_sz_3137_, v___x_3138_, v___x_3136_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v___x_3140_; lean_object* v_env_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3140_ = lean_st_ref_get(v_a_2335_);
v_env_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc_ref(v_env_3141_);
lean_dec(v___x_3140_);
lean_inc_n(v_stx_2329_, 2);
v___x_3142_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3143_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3144_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3143_, v_env_3141_, v___x_3142_);
v___x_3145_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3146_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3144_, v___x_3145_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3144_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3177_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_fst_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3175_; 
v_fst_3151_ = lean_ctor_get(v_a_3147_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3147_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v_a_3147_, 1);
lean_dec(v_unused_3176_);
v___x_3153_ = v_a_3147_;
v_isShared_3154_ = v_isSharedCheck_3175_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_fst_3151_);
lean_dec(v_a_3147_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3175_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
if (lean_obj_tag(v_fst_3151_) == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
lean_del_object(v___x_3149_);
v___x_3155_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3156_ = l_Lean_MessageData_ofName(v___x_3142_);
lean_inc_ref(v___x_3156_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 7);
lean_ctor_set(v___x_3153_, 1, v___x_3156_);
lean_ctor_set(v___x_3153_, 0, v___x_3155_);
v___x_3158_ = v___x_3153_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3159_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3162_ = l_Lean_indentD(v___x_3161_);
v___x_3163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3160_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3163_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3156_);
v___x_3167_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3168_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3169_;
}
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3173_; 
lean_del_object(v___x_3153_);
lean_dec(v___x_3142_);
lean_dec(v_stx_2329_);
v_val_3171_ = lean_ctor_get(v_fst_3151_, 0);
lean_inc(v_val_3171_);
lean_dec_ref_known(v_fst_3151_, 1);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v_val_3171_);
v___x_3173_ = v___x_3149_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_val_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v___x_3142_);
lean_dec(v_stx_2329_);
v_a_3178_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3146_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3146_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_val_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3320_; 
v_val_3186_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3188_ = v___x_3139_;
v_isShared_3189_ = v_isSharedCheck_3320_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_val_3186_);
lean_dec(v___x_3139_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3320_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v_finSeq_x3f_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3190_ = lean_unsigned_to_nat(1u);
v___x_3191_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3190_);
v___x_3215_ = lean_unsigned_to_nat(3u);
v___x_3216_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3215_);
v___x_3217_ = l_Lean_Syntax_isNone(v___x_3216_);
if (v___x_3217_ == 0)
{
uint8_t v___x_3218_; 
lean_inc(v___x_3216_);
v___x_3218_ = l_Lean_Syntax_matchesNull(v___x_3216_, v___x_3190_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v_env_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_dec(v___x_3216_);
lean_dec(v___x_3191_);
lean_del_object(v___x_3188_);
lean_dec(v_val_3186_);
v___x_3219_ = lean_st_ref_get(v_a_2335_);
v_env_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc_ref(v_env_3220_);
lean_dec(v___x_3219_);
lean_inc_n(v_stx_2329_, 2);
v___x_3221_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3222_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3223_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3222_, v_env_3220_, v___x_3221_);
v___x_3224_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3225_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3223_, v___x_3224_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3223_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3256_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3256_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_fst_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3254_; 
v_fst_3230_ = lean_ctor_get(v_a_3226_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3226_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v_a_3226_, 1);
lean_dec(v_unused_3255_);
v___x_3232_ = v_a_3226_;
v_isShared_3233_ = v_isSharedCheck_3254_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_fst_3230_);
lean_dec(v_a_3226_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3254_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
if (lean_obj_tag(v_fst_3230_) == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
lean_del_object(v___x_3228_);
v___x_3234_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3235_ = l_Lean_MessageData_ofName(v___x_3221_);
lean_inc_ref(v___x_3235_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 7);
lean_ctor_set(v___x_3232_, 1, v___x_3235_);
lean_ctor_set(v___x_3232_, 0, v___x_3234_);
v___x_3237_ = v___x_3232_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3237_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3241_ = l_Lean_indentD(v___x_3240_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3239_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v___x_3235_);
v___x_3246_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3247_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3248_;
}
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3252_; 
lean_del_object(v___x_3232_);
lean_dec(v___x_3221_);
lean_dec(v_stx_2329_);
v_val_3250_ = lean_ctor_get(v_fst_3230_, 0);
lean_inc(v_val_3250_);
lean_dec_ref_known(v_fst_3230_, 1);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_val_3250_);
v___x_3252_ = v___x_3228_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v___x_3221_);
lean_dec(v_stx_2329_);
v_a_3257_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3225_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3225_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = l_Lean_Syntax_getArg(v___x_3216_, v___x_3265_);
lean_dec(v___x_3216_);
v___x_3267_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72));
lean_inc(v___x_3266_);
v___x_3268_ = l_Lean_Syntax_isOfKind(v___x_3266_, v___x_3267_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v_env_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v___x_3266_);
lean_dec(v___x_3191_);
lean_del_object(v___x_3188_);
lean_dec(v_val_3186_);
v___x_3269_ = lean_st_ref_get(v_a_2335_);
v_env_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3269_);
lean_inc_n(v_stx_2329_, 2);
v___x_3271_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3272_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3273_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3272_, v_env_3270_, v___x_3271_);
v___x_3274_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3275_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3273_, v___x_3274_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3273_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3306_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3306_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3306_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v_fst_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3304_; 
v_fst_3280_ = lean_ctor_get(v_a_3276_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_a_3276_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v_a_3276_, 1);
lean_dec(v_unused_3305_);
v___x_3282_ = v_a_3276_;
v_isShared_3283_ = v_isSharedCheck_3304_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_fst_3280_);
lean_dec(v_a_3276_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3304_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
if (lean_obj_tag(v_fst_3280_) == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
lean_del_object(v___x_3278_);
v___x_3284_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3285_ = l_Lean_MessageData_ofName(v___x_3271_);
lean_inc_ref(v___x_3285_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 7);
lean_ctor_set(v___x_3282_, 1, v___x_3285_);
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3287_ = v___x_3282_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3288_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3291_ = l_Lean_indentD(v___x_3290_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3289_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___x_3285_);
v___x_3296_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3297_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3298_;
}
}
else
{
lean_object* v_val_3300_; lean_object* v___x_3302_; 
lean_del_object(v___x_3282_);
lean_dec(v___x_3271_);
lean_dec(v_stx_2329_);
v_val_3300_ = lean_ctor_get(v_fst_3280_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v_fst_3280_, 1);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v_val_3300_);
v___x_3302_ = v___x_3278_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_val_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v___x_3271_);
lean_dec(v_stx_2329_);
v_a_3307_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3275_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3275_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
lean_dec(v_stx_2329_);
v___x_3315_ = l_Lean_Syntax_getArg(v___x_3266_, v___x_3190_);
lean_dec(v___x_3266_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3315_);
v___x_3317_ = v___x_3188_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
v_finSeq_x3f_3193_ = v___x_3317_;
v___y_3194_ = v_a_2330_;
v___y_3195_ = v_a_2331_;
v___y_3196_ = v_a_2332_;
v___y_3197_ = v_a_2333_;
v___y_3198_ = v_a_2334_;
v___y_3199_ = v_a_2335_;
goto v___jp_3192_;
}
}
}
}
else
{
lean_object* v___x_3319_; 
lean_dec(v___x_3216_);
lean_del_object(v___x_3188_);
lean_dec(v_stx_2329_);
v___x_3319_ = lean_box(0);
v_finSeq_x3f_3193_ = v___x_3319_;
v___y_3194_ = v_a_2330_;
v___y_3195_ = v_a_2331_;
v___y_3196_ = v_a_2332_;
v___y_3197_ = v_a_2333_;
v___y_3198_ = v_a_2334_;
v___y_3199_ = v_a_2335_;
goto v___jp_3192_;
}
v___jp_3192_:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3191_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; size_t v_sz_3202_; lean_object* v___x_3203_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref_known(v___x_3200_, 1);
v_sz_3202_ = lean_array_size(v_val_3186_);
v___x_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_val_3186_, v_sz_3202_, v___x_3138_, v_a_3201_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v_val_3186_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_finSeq_x3f_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3214_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = l_Lean_Elab_Do_ControlInfo_sequence(v_a_3204_, v_a_3206_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3210_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
else
{
lean_dec(v_a_3204_);
return v___x_3205_;
}
}
else
{
lean_dec(v_finSeq_x3f_3193_);
return v___x_3203_;
}
}
else
{
lean_dec(v_finSeq_x3f_3193_);
lean_dec(v_val_3186_);
return v___x_3200_;
}
}
}
}
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3445_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3322_);
v___x_3446_ = l_Lean_Syntax_isNone(v___x_3445_);
if (v___x_3446_ == 0)
{
uint8_t v___x_3447_; 
lean_inc(v___x_3445_);
v___x_3447_ = l_Lean_Syntax_matchesNull(v___x_3445_, v___x_3322_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v_env_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec(v___x_3445_);
v___x_3448_ = lean_st_ref_get(v_a_2335_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
lean_inc_n(v_stx_2329_, 2);
v___x_3450_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3451_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3452_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3451_, v_env_3449_, v___x_3450_);
v___x_3453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3454_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3452_, v___x_3453_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3452_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3485_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3485_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3485_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v_fst_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3483_; 
v_fst_3459_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_a_3455_, 1);
lean_dec(v_unused_3484_);
v___x_3461_ = v_a_3455_;
v_isShared_3462_ = v_isSharedCheck_3483_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_fst_3459_);
lean_dec(v_a_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3483_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
if (lean_obj_tag(v_fst_3459_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_del_object(v___x_3457_);
v___x_3463_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3464_ = l_Lean_MessageData_ofName(v___x_3450_);
lean_inc_ref(v___x_3464_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 7);
lean_ctor_set(v___x_3461_, 1, v___x_3464_);
lean_ctor_set(v___x_3461_, 0, v___x_3463_);
v___x_3466_ = v___x_3461_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3467_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3470_ = l_Lean_indentD(v___x_3469_);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3468_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___x_3464_);
v___x_3475_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3476_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3477_;
}
}
else
{
lean_object* v_val_3479_; lean_object* v___x_3481_; 
lean_del_object(v___x_3461_);
lean_dec(v___x_3450_);
lean_dec(v_stx_2329_);
v_val_3479_ = lean_ctor_get(v_fst_3459_, 0);
lean_inc(v_val_3479_);
lean_dec_ref_known(v_fst_3459_, 1);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v_val_3479_);
v___x_3481_ = v___x_3457_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_val_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v___x_3450_);
lean_dec(v_stx_2329_);
v_a_3486_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3454_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3454_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
if (v___x_3446_ == 0)
{
lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3494_ = l_Lean_Syntax_getArg(v___x_3445_, v___x_3321_);
lean_dec(v___x_3445_);
v___x_3495_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3496_ = l_Lean_Syntax_isOfKind(v___x_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v_env_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3497_ = lean_st_ref_get(v_a_2335_);
v_env_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc_ref(v_env_3498_);
lean_dec(v___x_3497_);
lean_inc_n(v_stx_2329_, 2);
v___x_3499_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3500_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3501_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3500_, v_env_3498_, v___x_3499_);
v___x_3502_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3503_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3501_, v___x_3502_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3501_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3534_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3534_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3534_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_fst_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3532_; 
v_fst_3508_ = lean_ctor_get(v_a_3504_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3504_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; 
v_unused_3533_ = lean_ctor_get(v_a_3504_, 1);
lean_dec(v_unused_3533_);
v___x_3510_ = v_a_3504_;
v_isShared_3511_ = v_isSharedCheck_3532_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_fst_3508_);
lean_dec(v_a_3504_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3532_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
if (lean_obj_tag(v_fst_3508_) == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
lean_del_object(v___x_3506_);
v___x_3512_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3513_ = l_Lean_MessageData_ofName(v___x_3499_);
lean_inc_ref(v___x_3513_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set_tag(v___x_3510_, 7);
lean_ctor_set(v___x_3510_, 1, v___x_3513_);
lean_ctor_set(v___x_3510_, 0, v___x_3512_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3516_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3519_ = l_Lean_indentD(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3517_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___x_3513_);
v___x_3524_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3525_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3526_;
}
}
else
{
lean_object* v_val_3528_; lean_object* v___x_3530_; 
lean_del_object(v___x_3510_);
lean_dec(v___x_3499_);
lean_dec(v_stx_2329_);
v_val_3528_ = lean_ctor_get(v_fst_3508_, 0);
lean_inc(v_val_3528_);
lean_dec_ref_known(v_fst_3508_, 1);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v_val_3528_);
v___x_3530_ = v___x_3506_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_val_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v___x_3499_);
lean_dec(v_stx_2329_);
v_a_3535_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3503_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3503_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
v___y_3340_ = v_a_2330_;
v___y_3341_ = v_a_2331_;
v___y_3342_ = v_a_2332_;
v___y_3343_ = v_a_2333_;
v___y_3344_ = v_a_2334_;
v___y_3345_ = v_a_2335_;
goto v___jp_3339_;
}
}
else
{
lean_dec(v___x_3445_);
v___y_3340_ = v_a_2330_;
v___y_3341_ = v_a_2331_;
v___y_3342_ = v_a_2332_;
v___y_3343_ = v_a_2333_;
v___y_3344_ = v_a_2334_;
v___y_3345_ = v_a_2335_;
goto v___jp_3339_;
}
}
}
else
{
lean_dec(v___x_3445_);
v___y_3340_ = v_a_2330_;
v___y_3341_ = v_a_2331_;
v___y_3342_ = v_a_2332_;
v___y_3343_ = v_a_2333_;
v___y_3344_ = v_a_2334_;
v___y_3345_ = v_a_2335_;
goto v___jp_3339_;
}
v___jp_3323_:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_unsigned_to_nat(3u);
v___x_3331_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3330_);
lean_dec(v_stx_2329_);
v___x_3332_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3331_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; uint8_t v_breaks_3334_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v_breaks_3334_ = lean_ctor_get_uint8(v_a_3333_, sizeof(void*)*2);
if (v_breaks_3334_ == 0)
{
uint8_t v_returnsEarly_3335_; lean_object* v_reassigns_3336_; 
v_returnsEarly_3335_ = lean_ctor_get_uint8(v_a_3333_, sizeof(void*)*2 + 2);
v_reassigns_3336_ = lean_ctor_get(v_a_3333_, 1);
lean_inc(v_reassigns_3336_);
lean_dec(v_a_3333_);
v___y_2737_ = v_returnsEarly_3335_;
v___y_2738_ = v___x_3321_;
v___y_2739_ = v_reassigns_3336_;
v___y_2740_ = v___x_2744_;
goto v___jp_2736_;
}
else
{
uint8_t v_returnsEarly_3337_; lean_object* v_reassigns_3338_; 
v_returnsEarly_3337_ = lean_ctor_get_uint8(v_a_3333_, sizeof(void*)*2 + 2);
v_reassigns_3338_ = lean_ctor_get(v_a_3333_, 1);
lean_inc(v_reassigns_3338_);
lean_dec(v_a_3333_);
v___y_2737_ = v_returnsEarly_3337_;
v___y_2738_ = v___x_3322_;
v___y_2739_ = v_reassigns_3338_;
v___y_2740_ = v___x_2735_;
goto v___jp_2736_;
}
}
else
{
return v___x_3332_;
}
}
v___jp_3339_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3346_ = lean_unsigned_to_nat(2u);
v___x_3347_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3346_);
v___x_3348_ = l_Lean_Syntax_isNone(v___x_3347_);
if (v___x_3348_ == 0)
{
uint8_t v___x_3349_; 
lean_inc(v___x_3347_);
v___x_3349_ = l_Lean_Syntax_matchesNull(v___x_3347_, v___x_3322_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v_env_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v___x_3347_);
v___x_3350_ = lean_st_ref_get(v___y_3345_);
v_env_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_ref(v_env_3351_);
lean_dec(v___x_3350_);
lean_inc_n(v_stx_2329_, 2);
v___x_3352_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3353_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3354_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3353_, v_env_3351_, v___x_3352_);
v___x_3355_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3356_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3354_, v___x_3355_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___x_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3387_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3387_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3387_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_fst_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3385_; 
v_fst_3361_ = lean_ctor_get(v_a_3357_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_a_3357_);
if (v_isSharedCheck_3385_ == 0)
{
lean_object* v_unused_3386_; 
v_unused_3386_ = lean_ctor_get(v_a_3357_, 1);
lean_dec(v_unused_3386_);
v___x_3363_ = v_a_3357_;
v_isShared_3364_ = v_isSharedCheck_3385_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_fst_3361_);
lean_dec(v_a_3357_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3385_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
if (lean_obj_tag(v_fst_3361_) == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
lean_del_object(v___x_3359_);
v___x_3365_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3366_ = l_Lean_MessageData_ofName(v___x_3352_);
lean_inc_ref(v___x_3366_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set_tag(v___x_3363_, 7);
lean_ctor_set(v___x_3363_, 1, v___x_3366_);
lean_ctor_set(v___x_3363_, 0, v___x_3365_);
v___x_3368_ = v___x_3363_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3369_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3368_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3372_ = l_Lean_indentD(v___x_3371_);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3370_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3373_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v___x_3366_);
v___x_3377_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3378_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3379_;
}
}
else
{
lean_object* v_val_3381_; lean_object* v___x_3383_; 
lean_del_object(v___x_3363_);
lean_dec(v___x_3352_);
lean_dec(v_stx_2329_);
v_val_3381_ = lean_ctor_get(v_fst_3361_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v_fst_3361_, 1);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v_val_3381_);
v___x_3383_ = v___x_3359_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_val_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v___x_3352_);
lean_dec(v_stx_2329_);
v_a_3388_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3356_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3356_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
if (v___x_3348_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3396_ = l_Lean_Syntax_getArg(v___x_3347_, v___x_3321_);
lean_dec(v___x_3347_);
v___x_3397_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3398_ = l_Lean_Syntax_isOfKind(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3399_; lean_object* v_env_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3399_ = lean_st_ref_get(v___y_3345_);
v_env_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc_ref(v_env_3400_);
lean_dec(v___x_3399_);
lean_inc_n(v_stx_2329_, 2);
v___x_3401_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3402_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3403_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3402_, v_env_3400_, v___x_3401_);
v___x_3404_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3405_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3403_, v___x_3404_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___x_3403_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3436_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3434_; 
v_fst_3410_ = lean_ctor_get(v_a_3406_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_a_3406_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v_a_3406_, 1);
lean_dec(v_unused_3435_);
v___x_3412_ = v_a_3406_;
v_isShared_3413_ = v_isSharedCheck_3434_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_fst_3410_);
lean_dec(v_a_3406_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3434_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
if (lean_obj_tag(v_fst_3410_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
lean_del_object(v___x_3408_);
v___x_3414_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3415_ = l_Lean_MessageData_ofName(v___x_3401_);
lean_inc_ref(v___x_3415_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 7);
lean_ctor_set(v___x_3412_, 1, v___x_3415_);
lean_ctor_set(v___x_3412_, 0, v___x_3414_);
v___x_3417_ = v___x_3412_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3418_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3421_ = l_Lean_indentD(v___x_3420_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3419_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___x_3415_);
v___x_3426_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3427_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3428_;
}
}
else
{
lean_object* v_val_3430_; lean_object* v___x_3432_; 
lean_del_object(v___x_3412_);
lean_dec(v___x_3401_);
lean_dec(v_stx_2329_);
v_val_3430_ = lean_ctor_get(v_fst_3410_, 0);
lean_inc(v_val_3430_);
lean_dec_ref_known(v_fst_3410_, 1);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_val_3430_);
v___x_3432_ = v___x_3408_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_val_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec(v___x_3401_);
lean_dec(v_stx_2329_);
v_a_3437_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3405_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3405_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
v___y_3324_ = v___y_3340_;
v___y_3325_ = v___y_3341_;
v___y_3326_ = v___y_3342_;
v___y_3327_ = v___y_3343_;
v___y_3328_ = v___y_3344_;
v___y_3329_ = v___y_3345_;
goto v___jp_3323_;
}
}
else
{
lean_dec(v___x_3347_);
v___y_3324_ = v___y_3340_;
v___y_3325_ = v___y_3341_;
v___y_3326_ = v___y_3342_;
v___y_3327_ = v___y_3343_;
v___y_3328_ = v___y_3344_;
v___y_3329_ = v___y_3345_;
goto v___jp_3323_;
}
}
}
else
{
lean_dec(v___x_3347_);
v___y_3324_ = v___y_3340_;
v___y_3325_ = v___y_3341_;
v___y_3326_ = v___y_3342_;
v___y_3327_ = v___y_3343_;
v___y_3328_ = v___y_3344_;
v___y_3329_ = v___y_3345_;
goto v___jp_3323_;
}
}
}
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3680_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3829_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3544_);
v___x_3830_ = l_Lean_Syntax_getArgs(v___x_3829_);
lean_dec(v___x_3829_);
v___x_3831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2));
v___x_3832_ = lean_array_get_size(v___x_3830_);
v___x_3833_ = lean_nat_dec_lt(v___x_3543_, v___x_3832_);
if (v___x_3833_ == 0)
{
lean_dec_ref(v___x_3830_);
v___y_3680_ = v___x_3831_;
goto v___jp_3679_;
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3835_; size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; lean_object* v_snd_3839_; 
v___x_3834_ = lean_box(v___x_3833_);
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
lean_ctor_set(v___x_3835_, 1, v___x_3831_);
v___x_3836_ = ((size_t)0ULL);
v___x_3837_ = lean_usize_of_nat(v___x_3832_);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(v___x_2735_, v___x_2733_, v___x_3830_, v___x_3836_, v___x_3837_, v___x_3835_);
lean_dec_ref(v___x_3830_);
v_snd_3839_ = lean_ctor_get(v___x_3838_, 1);
lean_inc(v_snd_3839_);
lean_dec_ref(v___x_3838_);
v___y_3680_ = v_snd_3839_;
goto v___jp_3679_;
}
v___jp_3545_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_unsigned_to_nat(5u);
v___x_3553_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3552_);
lean_dec(v_stx_2329_);
v___x_3554_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3553_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3572_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3572_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3572_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
uint8_t v_returnsEarly_3559_; lean_object* v_reassigns_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3570_; 
v_returnsEarly_3559_ = lean_ctor_get_uint8(v_a_3555_, sizeof(void*)*2 + 2);
v_reassigns_3560_ = lean_ctor_get(v_a_3555_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_a_3555_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_a_3555_, 0);
lean_dec(v_unused_3571_);
v___x_3562_ = v_a_3555_;
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_reassigns_3560_);
lean_dec(v_a_3555_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3570_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3544_);
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_reassigns_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*2 + 2, v_returnsEarly_3559_);
v___x_3565_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_object* v___x_3567_; 
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*2, v___x_2733_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*2 + 1, v___x_2733_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*2 + 3, v___x_2733_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3565_);
v___x_3567_ = v___x_3557_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
return v___x_3554_;
}
}
v___jp_3573_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3580_ = lean_unsigned_to_nat(3u);
v___x_3581_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3580_);
v___x_3582_ = l_Lean_Syntax_isNone(v___x_3581_);
if (v___x_3582_ == 0)
{
uint8_t v___x_3583_; 
lean_inc(v___x_3581_);
v___x_3583_ = l_Lean_Syntax_matchesNull(v___x_3581_, v___x_3544_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; lean_object* v_env_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec(v___x_3581_);
v___x_3584_ = lean_st_ref_get(v___y_3579_);
v_env_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc_ref(v_env_3585_);
lean_dec(v___x_3584_);
lean_inc_n(v_stx_2329_, 2);
v___x_3586_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3587_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3588_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3587_, v_env_3585_, v___x_3586_);
v___x_3589_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3590_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3588_, v___x_3589_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___x_3588_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3621_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3621_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3621_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_fst_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3619_; 
v_fst_3595_ = lean_ctor_get(v_a_3591_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_a_3591_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v_a_3591_, 1);
lean_dec(v_unused_3620_);
v___x_3597_ = v_a_3591_;
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_fst_3595_);
lean_dec(v_a_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3619_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
if (lean_obj_tag(v_fst_3595_) == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
lean_del_object(v___x_3593_);
v___x_3599_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3600_ = l_Lean_MessageData_ofName(v___x_3586_);
lean_inc_ref(v___x_3600_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set_tag(v___x_3597_, 7);
lean_ctor_set(v___x_3597_, 1, v___x_3600_);
lean_ctor_set(v___x_3597_, 0, v___x_3599_);
v___x_3602_ = v___x_3597_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3603_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3602_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3606_ = l_Lean_indentD(v___x_3605_);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3604_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___x_3600_);
v___x_3611_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3612_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3613_;
}
}
else
{
lean_object* v_val_3615_; lean_object* v___x_3617_; 
lean_del_object(v___x_3597_);
lean_dec(v___x_3586_);
lean_dec(v_stx_2329_);
v_val_3615_ = lean_ctor_get(v_fst_3595_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v_fst_3595_, 1);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_val_3615_);
v___x_3617_ = v___x_3593_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_val_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v___x_3586_);
lean_dec(v_stx_2329_);
v_a_3622_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3590_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3590_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
if (v___x_3582_ == 0)
{
lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3630_ = l_Lean_Syntax_getArg(v___x_3581_, v___x_3543_);
lean_dec(v___x_3581_);
v___x_3631_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74));
v___x_3632_ = l_Lean_Syntax_isOfKind(v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; lean_object* v_env_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3633_ = lean_st_ref_get(v___y_3579_);
v_env_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc_ref(v_env_3634_);
lean_dec(v___x_3633_);
lean_inc_n(v_stx_2329_, 2);
v___x_3635_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3636_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3637_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3636_, v_env_3634_, v___x_3635_);
v___x_3638_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3639_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3637_, v___x_3638_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___x_3637_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3670_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3670_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3670_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_fst_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3668_; 
v_fst_3644_ = lean_ctor_get(v_a_3640_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_a_3640_, 1);
lean_dec(v_unused_3669_);
v___x_3646_ = v_a_3640_;
v_isShared_3647_ = v_isSharedCheck_3668_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_fst_3644_);
lean_dec(v_a_3640_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3668_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
if (lean_obj_tag(v_fst_3644_) == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
lean_del_object(v___x_3642_);
v___x_3648_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3649_ = l_Lean_MessageData_ofName(v___x_3635_);
lean_inc_ref(v___x_3649_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 7);
lean_ctor_set(v___x_3646_, 1, v___x_3649_);
lean_ctor_set(v___x_3646_, 0, v___x_3648_);
v___x_3651_ = v___x_3646_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3652_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3655_ = l_Lean_indentD(v___x_3654_);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3653_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v___x_3649_);
v___x_3660_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3661_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3662_;
}
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3666_; 
lean_del_object(v___x_3646_);
lean_dec(v___x_3635_);
lean_dec(v_stx_2329_);
v_val_3664_ = lean_ctor_get(v_fst_3644_, 0);
lean_inc(v_val_3664_);
lean_dec_ref_known(v_fst_3644_, 1);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v_val_3664_);
v___x_3666_ = v___x_3642_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_val_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v___x_3635_);
lean_dec(v_stx_2329_);
v_a_3671_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3639_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3639_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
v___y_3546_ = v___y_3574_;
v___y_3547_ = v___y_3575_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
v___y_3550_ = v___y_3578_;
v___y_3551_ = v___y_3579_;
goto v___jp_3545_;
}
}
else
{
lean_dec(v___x_3581_);
v___y_3546_ = v___y_3574_;
v___y_3547_ = v___y_3575_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
v___y_3550_ = v___y_3578_;
v___y_3551_ = v___y_3579_;
goto v___jp_3545_;
}
}
}
else
{
lean_dec(v___x_3581_);
v___y_3546_ = v___y_3574_;
v___y_3547_ = v___y_3575_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
v___y_3550_ = v___y_3578_;
v___y_3551_ = v___y_3579_;
goto v___jp_3545_;
}
}
v___jp_3679_:
{
size_t v_sz_3681_; size_t v___x_3682_; lean_object* v___x_3683_; 
v_sz_3681_ = lean_array_size(v___y_3680_);
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(v_sz_3681_, v___x_3682_, v___y_3680_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3684_; lean_object* v_env_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3684_ = lean_st_ref_get(v_a_2335_);
v_env_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc_ref(v_env_3685_);
lean_dec(v___x_3684_);
lean_inc_n(v_stx_2329_, 2);
v___x_3686_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3687_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3688_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3687_, v_env_3685_, v___x_3686_);
v___x_3689_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3690_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3688_, v___x_3689_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3688_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3721_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3693_ = v___x_3690_;
v_isShared_3694_ = v_isSharedCheck_3721_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3690_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3721_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v_fst_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3719_; 
v_fst_3695_ = lean_ctor_get(v_a_3691_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_a_3691_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; 
v_unused_3720_ = lean_ctor_get(v_a_3691_, 1);
lean_dec(v_unused_3720_);
v___x_3697_ = v_a_3691_;
v_isShared_3698_ = v_isSharedCheck_3719_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_fst_3695_);
lean_dec(v_a_3691_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3719_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
if (lean_obj_tag(v_fst_3695_) == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_del_object(v___x_3693_);
v___x_3699_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3700_ = l_Lean_MessageData_ofName(v___x_3686_);
lean_inc_ref(v___x_3700_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 7);
lean_ctor_set(v___x_3697_, 1, v___x_3700_);
lean_ctor_set(v___x_3697_, 0, v___x_3699_);
v___x_3702_ = v___x_3697_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3706_ = l_Lean_indentD(v___x_3705_);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3704_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3700_);
v___x_3711_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3712_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3713_;
}
}
else
{
lean_object* v_val_3715_; lean_object* v___x_3717_; 
lean_del_object(v___x_3697_);
lean_dec(v___x_3686_);
lean_dec(v_stx_2329_);
v_val_3715_ = lean_ctor_get(v_fst_3695_, 0);
lean_inc(v_val_3715_);
lean_dec_ref_known(v_fst_3695_, 1);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v_val_3715_);
v___x_3717_ = v___x_3693_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_val_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v___x_3686_);
lean_dec(v_stx_2329_);
v_a_3722_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3690_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3690_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
lean_dec_ref_known(v___x_3683_, 1);
v___x_3730_ = lean_unsigned_to_nat(2u);
v___x_3731_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3730_);
v___x_3732_ = l_Lean_Syntax_isNone(v___x_3731_);
if (v___x_3732_ == 0)
{
uint8_t v___x_3733_; 
lean_inc(v___x_3731_);
v___x_3733_ = l_Lean_Syntax_matchesNull(v___x_3731_, v___x_3544_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v_env_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec(v___x_3731_);
v___x_3734_ = lean_st_ref_get(v_a_2335_);
v_env_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc_ref(v_env_3735_);
lean_dec(v___x_3734_);
lean_inc_n(v_stx_2329_, 2);
v___x_3736_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3737_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3738_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3737_, v_env_3735_, v___x_3736_);
v___x_3739_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3740_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3738_, v___x_3739_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3738_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3771_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3771_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3771_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_fst_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3769_; 
v_fst_3745_ = lean_ctor_get(v_a_3741_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_a_3741_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v_a_3741_, 1);
lean_dec(v_unused_3770_);
v___x_3747_ = v_a_3741_;
v_isShared_3748_ = v_isSharedCheck_3769_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_fst_3745_);
lean_dec(v_a_3741_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3769_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
if (lean_obj_tag(v_fst_3745_) == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
lean_del_object(v___x_3743_);
v___x_3749_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3750_ = l_Lean_MessageData_ofName(v___x_3736_);
lean_inc_ref(v___x_3750_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set_tag(v___x_3747_, 7);
lean_ctor_set(v___x_3747_, 1, v___x_3750_);
lean_ctor_set(v___x_3747_, 0, v___x_3749_);
v___x_3752_ = v___x_3747_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3753_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3756_ = l_Lean_indentD(v___x_3755_);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3754_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3750_);
v___x_3761_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3762_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3763_;
}
}
else
{
lean_object* v_val_3765_; lean_object* v___x_3767_; 
lean_del_object(v___x_3747_);
lean_dec(v___x_3736_);
lean_dec(v_stx_2329_);
v_val_3765_ = lean_ctor_get(v_fst_3745_, 0);
lean_inc(v_val_3765_);
lean_dec_ref_known(v_fst_3745_, 1);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v_val_3765_);
v___x_3767_ = v___x_3743_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_val_3765_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v___x_3736_);
lean_dec(v_stx_2329_);
v_a_3772_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3740_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3740_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
if (v___x_3732_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3780_ = l_Lean_Syntax_getArg(v___x_3731_, v___x_3543_);
lean_dec(v___x_3731_);
v___x_3781_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76));
v___x_3782_ = l_Lean_Syntax_isOfKind(v___x_3780_, v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v_env_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3783_ = lean_st_ref_get(v_a_2335_);
v_env_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc_ref(v_env_3784_);
lean_dec(v___x_3783_);
lean_inc_n(v_stx_2329_, 2);
v___x_3785_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3786_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3787_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3786_, v_env_3784_, v___x_3785_);
v___x_3788_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3789_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3787_, v___x_3788_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3787_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3820_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3820_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3820_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_fst_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3818_; 
v_fst_3794_ = lean_ctor_get(v_a_3790_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_a_3790_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_a_3790_, 1);
lean_dec(v_unused_3819_);
v___x_3796_ = v_a_3790_;
v_isShared_3797_ = v_isSharedCheck_3818_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_fst_3794_);
lean_dec(v_a_3790_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3818_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
if (lean_obj_tag(v_fst_3794_) == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
lean_del_object(v___x_3792_);
v___x_3798_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3799_ = l_Lean_MessageData_ofName(v___x_3785_);
lean_inc_ref(v___x_3799_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set_tag(v___x_3796_, 7);
lean_ctor_set(v___x_3796_, 1, v___x_3799_);
lean_ctor_set(v___x_3796_, 0, v___x_3798_);
v___x_3801_ = v___x_3796_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3802_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3805_ = l_Lean_indentD(v___x_3804_);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3803_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v___x_3799_);
v___x_3810_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3811_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3812_;
}
}
else
{
lean_object* v_val_3814_; lean_object* v___x_3816_; 
lean_del_object(v___x_3796_);
lean_dec(v___x_3785_);
lean_dec(v_stx_2329_);
v_val_3814_ = lean_ctor_get(v_fst_3794_, 0);
lean_inc(v_val_3814_);
lean_dec_ref_known(v_fst_3794_, 1);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_val_3814_);
v___x_3816_ = v___x_3792_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_val_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v___x_3785_);
lean_dec(v_stx_2329_);
v_a_3821_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3789_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3789_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
v___y_3574_ = v_a_2330_;
v___y_3575_ = v_a_2331_;
v___y_3576_ = v_a_2332_;
v___y_3577_ = v_a_2333_;
v___y_3578_ = v_a_2334_;
v___y_3579_ = v_a_2335_;
goto v___jp_3573_;
}
}
else
{
lean_dec(v___x_3731_);
v___y_3574_ = v_a_2330_;
v___y_3575_ = v_a_2331_;
v___y_3576_ = v_a_2332_;
v___y_3577_ = v_a_2333_;
v___y_3578_ = v_a_2334_;
v___y_3579_ = v_a_2335_;
goto v___jp_3573_;
}
}
}
else
{
lean_dec(v___x_3731_);
v___y_3574_ = v_a_2330_;
v___y_3575_ = v_a_2331_;
v___y_3576_ = v_a_2332_;
v___y_3577_ = v_a_2333_;
v___y_3578_ = v_a_2334_;
v___y_3579_ = v_a_2335_;
goto v___jp_3573_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_2741_, 0, v___y_2738_);
lean_ctor_set(v___x_2741_, 1, v___y_2739_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*2, v___x_2735_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*2 + 1, v___x_2735_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*2 + 2, v___y_2737_);
lean_ctor_set_uint8(v___x_2741_, sizeof(void*)*2 + 3, v___y_2740_);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
return v___x_2742_;
}
}
else
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_unsigned_to_nat(3u);
v___x_3842_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3841_);
lean_dec(v_stx_2329_);
v___x_3843_ = l_Lean_NameSet_empty;
v___x_3844_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_3844_, 0, v___x_3840_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*2, v___x_2731_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*2 + 1, v___x_2731_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*2 + 2, v___x_2731_);
lean_ctor_set_uint8(v___x_3844_, sizeof(void*)*2 + 3, v___x_2731_);
v___x_3845_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3842_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3854_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3854_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = l_Lean_Elab_Do_ControlInfo_alternative(v___x_3844_, v_a_3846_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3850_);
v___x_3852_ = v___x_3848_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v___x_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
else
{
lean_dec_ref_known(v___x_3844_, 2);
return v___x_3845_;
}
}
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; size_t v_sz_3858_; size_t v___x_3859_; lean_object* v___x_3860_; 
v___x_3855_ = lean_unsigned_to_nat(4u);
v___x_3856_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3855_);
v___x_3857_ = l_Lean_Syntax_getArgs(v___x_3856_);
lean_dec(v___x_3856_);
v_sz_3858_ = lean_array_size(v___x_3857_);
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(v_sz_3858_, v___x_3859_, v___x_3857_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v___x_3861_; lean_object* v_env_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3861_ = lean_st_ref_get(v_a_2335_);
v_env_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc_ref(v_env_3862_);
lean_dec(v___x_3861_);
lean_inc_n(v_stx_2329_, 2);
v___x_3863_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3864_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3865_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3864_, v_env_3862_, v___x_3863_);
v___x_3866_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3867_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3865_, v___x_3866_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3865_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3898_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3898_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3898_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_fst_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3896_; 
v_fst_3872_ = lean_ctor_get(v_a_3868_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_a_3868_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; 
v_unused_3897_ = lean_ctor_get(v_a_3868_, 1);
lean_dec(v_unused_3897_);
v___x_3874_ = v_a_3868_;
v_isShared_3875_ = v_isSharedCheck_3896_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_fst_3872_);
lean_dec(v_a_3868_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3896_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
if (lean_obj_tag(v_fst_3872_) == 0)
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3879_; 
lean_del_object(v___x_3870_);
v___x_3876_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3877_ = l_Lean_MessageData_ofName(v___x_3863_);
lean_inc_ref(v___x_3877_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set_tag(v___x_3874_, 7);
lean_ctor_set(v___x_3874_, 1, v___x_3877_);
lean_ctor_set(v___x_3874_, 0, v___x_3876_);
v___x_3879_ = v___x_3874_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v___x_3877_);
v___x_3879_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3880_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3883_ = l_Lean_indentD(v___x_3882_);
v___x_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3881_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3877_);
v___x_3888_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3889_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3890_;
}
}
else
{
lean_object* v_val_3892_; lean_object* v___x_3894_; 
lean_del_object(v___x_3874_);
lean_dec(v___x_3863_);
lean_dec(v_stx_2329_);
v_val_3892_ = lean_ctor_get(v_fst_3872_, 0);
lean_inc(v_val_3892_);
lean_dec_ref_known(v_fst_3872_, 1);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_val_3892_);
v___x_3894_ = v___x_3870_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_val_3892_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___x_3863_);
lean_dec(v_stx_2329_);
v_a_3899_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3867_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3867_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v_val_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3994_; 
v_val_3907_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3909_ = v___x_3860_;
v_isShared_3910_ = v_isSharedCheck_3994_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_val_3907_);
lean_dec(v___x_3860_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3994_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v_elseSeq_x3f_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3911_ = lean_unsigned_to_nat(3u);
v___x_3912_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3911_);
v___x_3937_ = lean_unsigned_to_nat(5u);
v___x_3938_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_3937_);
v___x_3939_ = l_Lean_Syntax_isNone(v___x_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; uint8_t v___x_3941_; 
v___x_3940_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3938_);
v___x_3941_ = l_Lean_Syntax_matchesNull(v___x_3938_, v___x_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v_env_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_dec(v___x_3938_);
lean_dec(v___x_3912_);
lean_del_object(v___x_3909_);
lean_dec(v_val_3907_);
v___x_3942_ = lean_st_ref_get(v_a_2335_);
v_env_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc_ref(v_env_3943_);
lean_dec(v___x_3942_);
lean_inc_n(v_stx_2329_, 2);
v___x_3944_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_3945_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_3946_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_3945_, v_env_3943_, v___x_3944_);
v___x_3947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_3948_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_3946_, v___x_3947_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_3946_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3979_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3951_ = v___x_3948_;
v_isShared_3952_ = v_isSharedCheck_3979_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3948_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3979_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v_fst_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3977_; 
v_fst_3953_ = lean_ctor_get(v_a_3949_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_a_3949_);
if (v_isSharedCheck_3977_ == 0)
{
lean_object* v_unused_3978_; 
v_unused_3978_ = lean_ctor_get(v_a_3949_, 1);
lean_dec(v_unused_3978_);
v___x_3955_ = v_a_3949_;
v_isShared_3956_ = v_isSharedCheck_3977_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_fst_3953_);
lean_dec(v_a_3949_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3977_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
if (lean_obj_tag(v_fst_3953_) == 0)
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
lean_del_object(v___x_3951_);
v___x_3957_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_3958_ = l_Lean_MessageData_ofName(v___x_3944_);
lean_inc_ref(v___x_3958_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set_tag(v___x_3955_, 7);
lean_ctor_set(v___x_3955_, 1, v___x_3958_);
lean_ctor_set(v___x_3955_, 0, v___x_3957_);
v___x_3960_ = v___x_3955_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3961_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3960_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_3964_ = l_Lean_indentD(v___x_3963_);
v___x_3965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3962_);
lean_ctor_set(v___x_3965_, 1, v___x_3964_);
v___x_3966_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3958_);
v___x_3969_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_3970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3968_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_3970_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_3971_;
}
}
else
{
lean_object* v_val_3973_; lean_object* v___x_3975_; 
lean_del_object(v___x_3955_);
lean_dec(v___x_3944_);
lean_dec(v_stx_2329_);
v_val_3973_ = lean_ctor_get(v_fst_3953_, 0);
lean_inc(v_val_3973_);
lean_dec_ref_known(v_fst_3953_, 1);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v_val_3973_);
v___x_3975_ = v___x_3951_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_val_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v___x_3944_);
lean_dec(v_stx_2329_);
v_a_3980_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3948_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3948_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
lean_dec(v_stx_2329_);
v___x_3988_ = lean_unsigned_to_nat(1u);
v___x_3989_ = l_Lean_Syntax_getArg(v___x_3938_, v___x_3988_);
lean_dec(v___x_3938_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3989_);
v___x_3991_ = v___x_3909_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
v_elseSeq_x3f_3914_ = v___x_3991_;
v___y_3915_ = v_a_2330_;
v___y_3916_ = v_a_2331_;
v___y_3917_ = v_a_2332_;
v___y_3918_ = v_a_2333_;
v___y_3919_ = v_a_2334_;
v___y_3920_ = v_a_2335_;
goto v___jp_3913_;
}
}
}
else
{
lean_object* v___x_3993_; 
lean_dec(v___x_3938_);
lean_del_object(v___x_3909_);
lean_dec(v_stx_2329_);
v___x_3993_ = lean_box(0);
v_elseSeq_x3f_3914_ = v___x_3993_;
v___y_3915_ = v_a_2330_;
v___y_3916_ = v_a_2331_;
v___y_3917_ = v_a_2332_;
v___y_3918_ = v_a_2333_;
v___y_3919_ = v_a_2334_;
v___y_3920_ = v_a_2335_;
goto v___jp_3913_;
}
v___jp_3913_:
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_elseSeq_x3f_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; size_t v_sz_3924_; lean_object* v___x_3925_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = l_Array_reverse___redArg(v_val_3907_);
v_sz_3924_ = lean_array_size(v___x_3923_);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v___x_3923_, v_sz_3924_, v___x_3859_, v_a_3922_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec_ref(v___x_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3927_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_3912_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = l_Lean_Elab_Do_ControlInfo_alternative(v_a_3928_, v_a_3926_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3932_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
lean_dec(v_a_3926_);
return v___x_3927_;
}
}
else
{
lean_dec(v___x_3912_);
return v___x_3925_;
}
}
else
{
lean_dec(v___x_3912_);
lean_dec(v_val_3907_);
return v___x_3921_;
}
}
}
}
}
}
else
{
lean_object* v___x_3995_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___x_4059_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_3995_ = lean_unsigned_to_nat(0u);
v___x_4059_ = lean_unsigned_to_nat(1u);
v___x_4166_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4059_);
v___x_4167_ = l_Lean_Syntax_isNone(v___x_4166_);
if (v___x_4167_ == 0)
{
uint8_t v___x_4168_; 
lean_inc(v___x_4166_);
v___x_4168_ = l_Lean_Syntax_matchesNull(v___x_4166_, v___x_4059_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v_env_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec(v___x_4166_);
v___x_4169_ = lean_st_ref_get(v_a_2335_);
v_env_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc_ref(v_env_4170_);
lean_dec(v___x_4169_);
lean_inc_n(v_stx_2329_, 2);
v___x_4171_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4172_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4173_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4172_, v_env_4170_, v___x_4171_);
v___x_4174_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4175_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4173_, v___x_4174_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4206_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4206_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4206_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v_fst_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4204_; 
v_fst_4180_ = lean_ctor_get(v_a_4176_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_a_4176_);
if (v_isSharedCheck_4204_ == 0)
{
lean_object* v_unused_4205_; 
v_unused_4205_ = lean_ctor_get(v_a_4176_, 1);
lean_dec(v_unused_4205_);
v___x_4182_ = v_a_4176_;
v_isShared_4183_ = v_isSharedCheck_4204_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_fst_4180_);
lean_dec(v_a_4176_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4204_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
if (lean_obj_tag(v_fst_4180_) == 0)
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
lean_del_object(v___x_4178_);
v___x_4184_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4185_ = l_Lean_MessageData_ofName(v___x_4171_);
lean_inc_ref(v___x_4185_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set_tag(v___x_4182_, 7);
lean_ctor_set(v___x_4182_, 1, v___x_4185_);
lean_ctor_set(v___x_4182_, 0, v___x_4184_);
v___x_4187_ = v___x_4182_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4184_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4188_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4191_ = l_Lean_indentD(v___x_4190_);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4189_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4185_);
v___x_4196_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4197_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4198_;
}
}
else
{
lean_object* v_val_4200_; lean_object* v___x_4202_; 
lean_del_object(v___x_4182_);
lean_dec(v___x_4171_);
lean_dec(v_stx_2329_);
v_val_4200_ = lean_ctor_get(v_fst_4180_, 0);
lean_inc(v_val_4200_);
lean_dec_ref_known(v_fst_4180_, 1);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v_val_4200_);
v___x_4202_ = v___x_4178_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_val_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v___x_4171_);
lean_dec(v_stx_2329_);
v_a_4207_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4175_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4175_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; 
v___x_4215_ = l_Lean_Syntax_getArg(v___x_4166_, v___x_3995_);
lean_dec(v___x_4166_);
v___x_4216_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__80));
v___x_4217_ = l_Lean_Syntax_isOfKind(v___x_4215_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v_env_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4218_ = lean_st_ref_get(v_a_2335_);
v_env_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc_ref(v_env_4219_);
lean_dec(v___x_4218_);
lean_inc_n(v_stx_2329_, 2);
v___x_4220_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4221_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4222_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4221_, v_env_4219_, v___x_4220_);
v___x_4223_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4224_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4222_, v___x_4223_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4222_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4255_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4255_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_fst_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4253_; 
v_fst_4229_ = lean_ctor_get(v_a_4225_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_a_4225_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; 
v_unused_4254_ = lean_ctor_get(v_a_4225_, 1);
lean_dec(v_unused_4254_);
v___x_4231_ = v_a_4225_;
v_isShared_4232_ = v_isSharedCheck_4253_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_fst_4229_);
lean_dec(v_a_4225_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4253_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
if (lean_obj_tag(v_fst_4229_) == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
lean_del_object(v___x_4227_);
v___x_4233_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4234_ = l_Lean_MessageData_ofName(v___x_4220_);
lean_inc_ref(v___x_4234_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set_tag(v___x_4231_, 7);
lean_ctor_set(v___x_4231_, 1, v___x_4234_);
lean_ctor_set(v___x_4231_, 0, v___x_4233_);
v___x_4236_ = v___x_4231_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4237_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4236_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4240_ = l_Lean_indentD(v___x_4239_);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4238_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
lean_ctor_set(v___x_4244_, 1, v___x_4234_);
v___x_4245_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4244_);
lean_ctor_set(v___x_4246_, 1, v___x_4245_);
v___x_4247_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4246_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4247_;
}
}
else
{
lean_object* v_val_4249_; lean_object* v___x_4251_; 
lean_del_object(v___x_4231_);
lean_dec(v___x_4220_);
lean_dec(v_stx_2329_);
v_val_4249_ = lean_ctor_get(v_fst_4229_, 0);
lean_inc(v_val_4249_);
lean_dec_ref_known(v_fst_4229_, 1);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v_val_4249_);
v___x_4251_ = v___x_4227_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_val_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v___x_4220_);
lean_dec(v_stx_2329_);
v_a_4256_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4224_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4224_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
v___y_4061_ = v_a_2330_;
v___y_4062_ = v_a_2331_;
v___y_4063_ = v_a_2332_;
v___y_4064_ = v_a_2333_;
v___y_4065_ = v_a_2334_;
v___y_4066_ = v_a_2335_;
goto v___jp_4060_;
}
}
}
else
{
lean_dec(v___x_4166_);
v___y_4061_ = v_a_2330_;
v___y_4062_ = v_a_2331_;
v___y_4063_ = v_a_2332_;
v___y_4064_ = v_a_2333_;
v___y_4065_ = v_a_2334_;
v___y_4066_ = v_a_2335_;
goto v___jp_4060_;
}
v___jp_3996_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v___x_4003_ = lean_unsigned_to_nat(6u);
v___x_4004_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4003_);
v___x_4005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(v___x_4004_);
v___x_4006_ = l_Lean_Syntax_isOfKind(v___x_4004_, v___x_4005_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; lean_object* v_env_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_dec(v___x_4004_);
v___x_4007_ = lean_st_ref_get(v___y_4002_);
v_env_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc_ref(v_env_4008_);
lean_dec(v___x_4007_);
lean_inc_n(v_stx_2329_, 2);
v___x_4009_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4010_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4011_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4010_, v_env_4008_, v___x_4009_);
v___x_4012_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4013_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4011_, v___x_4012_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___x_4011_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4044_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4016_ = v___x_4013_;
v_isShared_4017_ = v_isSharedCheck_4044_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4044_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_fst_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4042_; 
v_fst_4018_ = lean_ctor_get(v_a_4014_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_a_4014_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v_a_4014_, 1);
lean_dec(v_unused_4043_);
v___x_4020_ = v_a_4014_;
v_isShared_4021_ = v_isSharedCheck_4042_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_fst_4018_);
lean_dec(v_a_4014_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4042_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
if (lean_obj_tag(v_fst_4018_) == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4025_; 
lean_del_object(v___x_4016_);
v___x_4022_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4023_ = l_Lean_MessageData_ofName(v___x_4009_);
lean_inc_ref(v___x_4023_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set_tag(v___x_4020_, 7);
lean_ctor_set(v___x_4020_, 1, v___x_4023_);
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4025_ = v___x_4020_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4026_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4029_ = l_Lean_indentD(v___x_4028_);
v___x_4030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4027_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
v___x_4031_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4030_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v___x_4023_);
v___x_4034_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4033_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
v___x_4036_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4035_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4036_;
}
}
else
{
lean_object* v_val_4038_; lean_object* v___x_4040_; 
lean_del_object(v___x_4020_);
lean_dec(v___x_4009_);
lean_dec(v_stx_2329_);
v_val_4038_ = lean_ctor_get(v_fst_4018_, 0);
lean_inc(v_val_4038_);
lean_dec_ref_known(v_fst_4018_, 1);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v_val_4038_);
v___x_4040_ = v___x_4016_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_val_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v___x_4009_);
lean_dec(v_stx_2329_);
v_a_4045_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4013_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4013_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; size_t v_sz_4056_; size_t v___x_4057_; lean_object* v___x_4058_; 
lean_dec(v_stx_2329_);
v___x_4053_ = l_Lean_Syntax_getArg(v___x_4004_, v___x_3995_);
lean_dec(v___x_4004_);
v___x_4054_ = l_Lean_Syntax_getArgs(v___x_4053_);
lean_dec(v___x_4053_);
v___x_4055_ = l_Lean_Elab_Do_ControlInfo_empty;
v_sz_4056_ = lean_array_size(v___x_4054_);
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_2727_, v___x_4054_, v_sz_4056_, v___x_4057_, v___x_4055_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec_ref(v___x_4054_);
return v___x_4058_;
}
}
v___jp_4060_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; 
v___x_4067_ = lean_unsigned_to_nat(2u);
v___x_4068_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4067_);
v___x_4069_ = l_Lean_Syntax_isNone(v___x_4068_);
if (v___x_4069_ == 0)
{
uint8_t v___x_4070_; 
lean_inc(v___x_4068_);
v___x_4070_ = l_Lean_Syntax_matchesNull(v___x_4068_, v___x_4059_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v_env_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec(v___x_4068_);
v___x_4071_ = lean_st_ref_get(v___y_4066_);
v_env_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc_ref(v_env_4072_);
lean_dec(v___x_4071_);
lean_inc_n(v_stx_2329_, 2);
v___x_4073_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4074_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4075_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4074_, v_env_4072_, v___x_4073_);
v___x_4076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4077_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4075_, v___x_4076_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___x_4075_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4108_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4108_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4108_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v_fst_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4106_; 
v_fst_4082_ = lean_ctor_get(v_a_4078_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_a_4078_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; 
v_unused_4107_ = lean_ctor_get(v_a_4078_, 1);
lean_dec(v_unused_4107_);
v___x_4084_ = v_a_4078_;
v_isShared_4085_ = v_isSharedCheck_4106_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_fst_4082_);
lean_dec(v_a_4078_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4106_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
if (lean_obj_tag(v_fst_4082_) == 0)
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4089_; 
lean_del_object(v___x_4080_);
v___x_4086_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4087_ = l_Lean_MessageData_ofName(v___x_4073_);
lean_inc_ref(v___x_4087_);
if (v_isShared_4085_ == 0)
{
lean_ctor_set_tag(v___x_4084_, 7);
lean_ctor_set(v___x_4084_, 1, v___x_4087_);
lean_ctor_set(v___x_4084_, 0, v___x_4086_);
v___x_4089_ = v___x_4084_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4101_, 1, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4090_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4093_ = l_Lean_indentD(v___x_4092_);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4091_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
lean_ctor_set(v___x_4097_, 1, v___x_4087_);
v___x_4098_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4099_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4100_;
}
}
else
{
lean_object* v_val_4102_; lean_object* v___x_4104_; 
lean_del_object(v___x_4084_);
lean_dec(v___x_4073_);
lean_dec(v_stx_2329_);
v_val_4102_ = lean_ctor_get(v_fst_4082_, 0);
lean_inc(v_val_4102_);
lean_dec_ref_known(v_fst_4082_, 1);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_val_4102_);
v___x_4104_ = v___x_4080_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_val_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v___x_4073_);
lean_dec(v_stx_2329_);
v_a_4109_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4077_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4077_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4117_ = l_Lean_Syntax_getArg(v___x_4068_, v___x_3995_);
lean_dec(v___x_4068_);
v___x_4118_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__78));
v___x_4119_ = l_Lean_Syntax_isOfKind(v___x_4117_, v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v_env_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4120_ = lean_st_ref_get(v___y_4066_);
v_env_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc_ref(v_env_4121_);
lean_dec(v___x_4120_);
lean_inc_n(v_stx_2329_, 2);
v___x_4122_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4123_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4124_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4123_, v_env_4121_, v___x_4122_);
v___x_4125_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4126_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4124_, v___x_4125_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___x_4124_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4157_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4129_ = v___x_4126_;
v_isShared_4130_ = v_isSharedCheck_4157_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4126_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4157_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v_fst_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4155_; 
v_fst_4131_ = lean_ctor_get(v_a_4127_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_a_4127_);
if (v_isSharedCheck_4155_ == 0)
{
lean_object* v_unused_4156_; 
v_unused_4156_ = lean_ctor_get(v_a_4127_, 1);
lean_dec(v_unused_4156_);
v___x_4133_ = v_a_4127_;
v_isShared_4134_ = v_isSharedCheck_4155_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_fst_4131_);
lean_dec(v_a_4127_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4155_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
if (lean_obj_tag(v_fst_4131_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4138_; 
lean_del_object(v___x_4129_);
v___x_4135_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4136_ = l_Lean_MessageData_ofName(v___x_4122_);
lean_inc_ref(v___x_4136_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 7);
lean_ctor_set(v___x_4133_, 1, v___x_4136_);
lean_ctor_set(v___x_4133_, 0, v___x_4135_);
v___x_4138_ = v___x_4133_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4150_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4139_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4142_ = l_Lean_indentD(v___x_4141_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4140_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4143_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
lean_ctor_set(v___x_4146_, 1, v___x_4136_);
v___x_4147_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4148_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4149_;
}
}
else
{
lean_object* v_val_4151_; lean_object* v___x_4153_; 
lean_del_object(v___x_4133_);
lean_dec(v___x_4122_);
lean_dec(v_stx_2329_);
v_val_4151_ = lean_ctor_get(v_fst_4131_, 0);
lean_inc(v_val_4151_);
lean_dec_ref_known(v_fst_4131_, 1);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 0, v_val_4151_);
v___x_4153_ = v___x_4129_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_val_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v___x_4122_);
lean_dec(v_stx_2329_);
v_a_4158_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4126_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4126_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
v___y_3997_ = v___y_4061_;
v___y_3998_ = v___y_4062_;
v___y_3999_ = v___y_4063_;
v___y_4000_ = v___y_4064_;
v___y_4001_ = v___y_4065_;
v___y_4002_ = v___y_4066_;
goto v___jp_3996_;
}
}
}
else
{
lean_dec(v___x_4068_);
v___y_3997_ = v___y_4061_;
v___y_3998_ = v___y_4062_;
v___y_3999_ = v___y_4063_;
v___y_4000_ = v___y_4064_;
v___y_4001_ = v___y_4065_;
v___y_4002_ = v___y_4066_;
goto v___jp_3996_;
}
}
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = lean_unsigned_to_nat(0u);
v___x_4265_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4264_);
if (v___x_2725_ == 0)
{
lean_object* v___x_4266_; uint8_t v___x_4267_; 
v___x_4266_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(v___x_4265_);
v___x_4267_ = l_Lean_Syntax_isOfKind(v___x_4265_, v___x_4266_);
if (v___x_4267_ == 0)
{
if (v___x_2725_ == 0)
{
lean_object* v___x_4268_; uint8_t v___x_4269_; 
v___x_4268_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(v___x_4265_);
v___x_4269_ = l_Lean_Syntax_isOfKind(v___x_4265_, v___x_4268_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v_env_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec(v___x_4265_);
v___x_4270_ = lean_st_ref_get(v_a_2335_);
v_env_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc_ref(v_env_4271_);
lean_dec(v___x_4270_);
lean_inc_n(v_stx_2329_, 2);
v___x_4272_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4273_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4274_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4273_, v_env_4271_, v___x_4272_);
v___x_4275_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4276_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4274_, v___x_4275_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4274_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4307_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4307_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4307_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v_fst_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4305_; 
v_fst_4281_ = lean_ctor_get(v_a_4277_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_a_4277_);
if (v_isSharedCheck_4305_ == 0)
{
lean_object* v_unused_4306_; 
v_unused_4306_ = lean_ctor_get(v_a_4277_, 1);
lean_dec(v_unused_4306_);
v___x_4283_ = v_a_4277_;
v_isShared_4284_ = v_isSharedCheck_4305_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_fst_4281_);
lean_dec(v_a_4277_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4305_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
if (lean_obj_tag(v_fst_4281_) == 0)
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
lean_del_object(v___x_4279_);
v___x_4285_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4286_ = l_Lean_MessageData_ofName(v___x_4272_);
lean_inc_ref(v___x_4286_);
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 7);
lean_ctor_set(v___x_4283_, 1, v___x_4286_);
lean_ctor_set(v___x_4283_, 0, v___x_4285_);
v___x_4288_ = v___x_4283_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4285_);
lean_ctor_set(v_reuseFailAlloc_4300_, 1, v___x_4286_);
v___x_4288_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4289_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4288_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4292_ = l_Lean_indentD(v___x_4291_);
v___x_4293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4290_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v___x_4286_);
v___x_4297_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4298_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4299_;
}
}
else
{
lean_object* v_val_4301_; lean_object* v___x_4303_; 
lean_del_object(v___x_4283_);
lean_dec(v___x_4272_);
lean_dec(v_stx_2329_);
v_val_4301_ = lean_ctor_get(v_fst_4281_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v_fst_4281_, 1);
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v_val_4301_);
v___x_4303_ = v___x_4279_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_val_4301_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec(v___x_4272_);
lean_dec(v_stx_2329_);
v_a_4308_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4276_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4276_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
else
{
lean_object* v___x_4316_; 
lean_dec(v_stx_2329_);
v___x_4316_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2416_, v___x_4265_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4316_;
}
}
else
{
lean_object* v___x_4317_; 
lean_dec(v_stx_2329_);
v___x_4317_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2416_, v___x_4265_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4317_;
}
}
else
{
lean_object* v___x_4318_; 
lean_dec(v_stx_2329_);
v___x_4318_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2416_, v___x_4265_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4318_;
}
}
else
{
lean_object* v___x_4319_; 
lean_dec(v_stx_2329_);
v___x_4319_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2416_, v___x_4265_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4319_;
}
}
}
else
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = lean_unsigned_to_nat(0u);
v___x_4321_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4320_);
if (v___x_2723_ == 0)
{
lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__82));
lean_inc(v___x_4321_);
v___x_4349_ = l_Lean_Syntax_isOfKind(v___x_4321_, v___x_4348_);
if (v___x_4349_ == 0)
{
if (v___x_2723_ == 0)
{
lean_object* v___x_4350_; uint8_t v___x_4351_; 
v___x_4350_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__84));
lean_inc(v___x_4321_);
v___x_4351_ = l_Lean_Syntax_isOfKind(v___x_4321_, v___x_4350_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; lean_object* v_env_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
lean_dec(v___x_4321_);
v___x_4352_ = lean_st_ref_get(v_a_2335_);
v_env_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc_ref(v_env_4353_);
lean_dec(v___x_4352_);
lean_inc_n(v_stx_2329_, 2);
v___x_4354_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4355_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4356_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4355_, v_env_4353_, v___x_4354_);
v___x_4357_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4358_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4356_, v___x_4357_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4356_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4389_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4389_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4389_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_fst_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4387_; 
v_fst_4363_ = lean_ctor_get(v_a_4359_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v_a_4359_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; 
v_unused_4388_ = lean_ctor_get(v_a_4359_, 1);
lean_dec(v_unused_4388_);
v___x_4365_ = v_a_4359_;
v_isShared_4366_ = v_isSharedCheck_4387_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_fst_4363_);
lean_dec(v_a_4359_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4387_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
if (lean_obj_tag(v_fst_4363_) == 0)
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
lean_del_object(v___x_4361_);
v___x_4367_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4368_ = l_Lean_MessageData_ofName(v___x_4354_);
lean_inc_ref(v___x_4368_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set_tag(v___x_4365_, 7);
lean_ctor_set(v___x_4365_, 1, v___x_4368_);
lean_ctor_set(v___x_4365_, 0, v___x_4367_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4371_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4374_ = l_Lean_indentD(v___x_4373_);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4372_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4375_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
v___x_4378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
lean_ctor_set(v___x_4378_, 1, v___x_4368_);
v___x_4379_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4378_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4380_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4381_;
}
}
else
{
lean_object* v_val_4383_; lean_object* v___x_4385_; 
lean_del_object(v___x_4365_);
lean_dec(v___x_4354_);
lean_dec(v_stx_2329_);
v_val_4383_ = lean_ctor_get(v_fst_4363_, 0);
lean_inc(v_val_4383_);
lean_dec_ref_known(v_fst_4363_, 1);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v_val_4383_);
v___x_4385_ = v___x_4361_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_val_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v___x_4354_);
lean_dec(v_stx_2329_);
v_a_4390_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4358_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4358_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_4322_;
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_4322_;
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_4335_;
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_4335_;
}
v___jp_4322_:
{
lean_object* v___x_4323_; 
v___x_4323_ = l_Lean_Elab_Do_getLetPatDeclVars(v___x_4321_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4321_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v___x_4325_ = lean_box(0);
v___x_4326_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4324_, v___x_4325_, v___x_4325_, v___x_4325_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4326_;
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
v_a_4327_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4323_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4323_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
v___jp_4335_:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_Lean_Elab_Do_getLetIdDeclVars(v___x_4321_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4321_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
v___x_4338_ = lean_box(0);
v___x_4339_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_a_4337_, v___x_4338_, v___x_4338_, v___x_4338_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4339_;
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
v_a_4340_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4336_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4336_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
}
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; 
v___x_4398_ = lean_unsigned_to_nat(1u);
v___x_4399_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4398_);
v___x_4400_ = l_Lean_Syntax_isNone(v___x_4399_);
if (v___x_4400_ == 0)
{
uint8_t v___x_4401_; 
v___x_4401_ = l_Lean_Syntax_matchesNull(v___x_4399_, v___x_4398_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; lean_object* v_env_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4402_ = lean_st_ref_get(v_a_2335_);
v_env_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc_ref(v_env_4403_);
lean_dec(v___x_4402_);
lean_inc_n(v_stx_2329_, 2);
v___x_4404_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4405_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4406_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4405_, v_env_4403_, v___x_4404_);
v___x_4407_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4408_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4406_, v___x_4407_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4406_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4439_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4439_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4439_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v_fst_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4437_; 
v_fst_4413_ = lean_ctor_get(v_a_4409_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4437_ == 0)
{
lean_object* v_unused_4438_; 
v_unused_4438_ = lean_ctor_get(v_a_4409_, 1);
lean_dec(v_unused_4438_);
v___x_4415_ = v_a_4409_;
v_isShared_4416_ = v_isSharedCheck_4437_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_fst_4413_);
lean_dec(v_a_4409_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4437_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
if (lean_obj_tag(v_fst_4413_) == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
lean_del_object(v___x_4411_);
v___x_4417_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4418_ = l_Lean_MessageData_ofName(v___x_4404_);
lean_inc_ref(v___x_4418_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set_tag(v___x_4415_, 7);
lean_ctor_set(v___x_4415_, 1, v___x_4418_);
lean_ctor_set(v___x_4415_, 0, v___x_4417_);
v___x_4420_ = v___x_4415_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4417_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4421_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4420_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4424_ = l_Lean_indentD(v___x_4423_);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4422_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4425_);
lean_ctor_set(v___x_4427_, 1, v___x_4426_);
v___x_4428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
lean_ctor_set(v___x_4428_, 1, v___x_4418_);
v___x_4429_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4430_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4431_;
}
}
else
{
lean_object* v_val_4433_; lean_object* v___x_4435_; 
lean_del_object(v___x_4415_);
lean_dec(v___x_4404_);
lean_dec(v_stx_2329_);
v_val_4433_ = lean_ctor_get(v_fst_4413_, 0);
lean_inc(v_val_4433_);
lean_dec_ref_known(v_fst_4413_, 1);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v_val_4433_);
v___x_4435_ = v___x_4411_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_val_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v___x_4404_);
lean_dec(v_stx_2329_);
v_a_4440_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4408_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4408_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
else
{
v___y_2666_ = v_a_2330_;
v___y_2667_ = v_a_2331_;
v___y_2668_ = v_a_2332_;
v___y_2669_ = v_a_2333_;
v___y_2670_ = v_a_2334_;
v___y_2671_ = v_a_2335_;
goto v___jp_2665_;
}
}
else
{
lean_dec(v___x_4399_);
v___y_2666_ = v_a_2330_;
v___y_2667_ = v_a_2331_;
v___y_2668_ = v_a_2332_;
v___y_2669_ = v_a_2333_;
v___y_2670_ = v_a_2334_;
v___y_2671_ = v_a_2335_;
goto v___jp_2665_;
}
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4448_);
v___x_4450_ = l_Lean_Syntax_isNone(v___x_4449_);
if (v___x_4450_ == 0)
{
uint8_t v___x_4451_; 
v___x_4451_ = l_Lean_Syntax_matchesNull(v___x_4449_, v___x_4448_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; lean_object* v_env_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4452_ = lean_st_ref_get(v_a_2335_);
v_env_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc_ref(v_env_4453_);
lean_dec(v___x_4452_);
lean_inc_n(v_stx_2329_, 2);
v___x_4454_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4455_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4456_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4455_, v_env_4453_, v___x_4454_);
v___x_4457_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4458_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4456_, v___x_4457_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4456_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4489_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4489_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4489_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4487_; 
v_fst_4463_ = lean_ctor_get(v_a_4459_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_a_4459_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v_a_4459_, 1);
lean_dec(v_unused_4488_);
v___x_4465_ = v_a_4459_;
v_isShared_4466_ = v_isSharedCheck_4487_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_fst_4463_);
lean_dec(v_a_4459_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4487_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
if (lean_obj_tag(v_fst_4463_) == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4470_; 
lean_del_object(v___x_4461_);
v___x_4467_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4468_ = l_Lean_MessageData_ofName(v___x_4454_);
lean_inc_ref(v___x_4468_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set_tag(v___x_4465_, 7);
lean_ctor_set(v___x_4465_, 1, v___x_4468_);
lean_ctor_set(v___x_4465_, 0, v___x_4467_);
v___x_4470_ = v___x_4465_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4471_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4470_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
v___x_4473_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4474_ = l_Lean_indentD(v___x_4473_);
v___x_4475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4472_);
lean_ctor_set(v___x_4475_, 1, v___x_4474_);
v___x_4476_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4475_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
v___x_4478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
lean_ctor_set(v___x_4478_, 1, v___x_4468_);
v___x_4479_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4478_);
lean_ctor_set(v___x_4480_, 1, v___x_4479_);
v___x_4481_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4480_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4481_;
}
}
else
{
lean_object* v_val_4483_; lean_object* v___x_4485_; 
lean_del_object(v___x_4465_);
lean_dec(v___x_4454_);
lean_dec(v_stx_2329_);
v_val_4483_ = lean_ctor_get(v_fst_4463_, 0);
lean_inc(v_val_4483_);
lean_dec_ref_known(v_fst_4463_, 1);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v_val_4483_);
v___x_4485_ = v___x_4461_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_val_4483_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_dec(v___x_4454_);
lean_dec(v_stx_2329_);
v_a_4490_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4458_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4458_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
else
{
v___y_2597_ = v_a_2330_;
v___y_2598_ = v_a_2331_;
v___y_2599_ = v_a_2332_;
v___y_2600_ = v_a_2333_;
v___y_2601_ = v_a_2334_;
v___y_2602_ = v_a_2335_;
goto v___jp_2596_;
}
}
else
{
lean_dec(v___x_4449_);
v___y_2597_ = v_a_2330_;
v___y_2598_ = v_a_2331_;
v___y_2599_ = v_a_2332_;
v___y_2600_ = v_a_2333_;
v___y_2601_ = v_a_2334_;
v___y_2602_ = v_a_2335_;
goto v___jp_2596_;
}
}
v___jp_2655_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2662_ = lean_unsigned_to_nat(3u);
v___x_2663_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2662_);
lean_dec(v_stx_2329_);
v___x_2664_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v___x_2654_, v___x_2663_, v___y_2656_, v___y_2657_, v___y_2661_, v___y_2658_, v___y_2660_, v___y_2659_);
return v___x_2664_;
}
v___jp_2665_:
{
if (v___x_2654_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2672_ = lean_unsigned_to_nat(2u);
v___x_2673_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2672_);
v___x_2674_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2675_ = l_Lean_Syntax_isOfKind(v___x_2673_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v_env_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2676_ = lean_st_ref_get(v___y_2671_);
v_env_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_env_2677_);
lean_dec(v___x_2676_);
lean_inc_n(v_stx_2329_, 2);
v___x_2678_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2679_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2680_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2679_, v_env_2677_, v___x_2678_);
v___x_2681_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2682_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2680_, v___x_2681_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___x_2680_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2713_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2713_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2713_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_fst_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2711_; 
v_fst_2687_ = lean_ctor_get(v_a_2683_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_a_2683_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; 
v_unused_2712_ = lean_ctor_get(v_a_2683_, 1);
lean_dec(v_unused_2712_);
v___x_2689_ = v_a_2683_;
v_isShared_2690_ = v_isSharedCheck_2711_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_fst_2687_);
lean_dec(v_a_2683_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2711_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
if (lean_obj_tag(v_fst_2687_) == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
lean_del_object(v___x_2685_);
v___x_2691_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2692_ = l_Lean_MessageData_ofName(v___x_2678_);
lean_inc_ref(v___x_2692_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 7);
lean_ctor_set(v___x_2689_, 1, v___x_2692_);
lean_ctor_set(v___x_2689_, 0, v___x_2691_);
v___x_2694_ = v___x_2689_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2695_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2698_ = l_Lean_indentD(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2696_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___x_2692_);
v___x_2703_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2704_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2705_;
}
}
else
{
lean_object* v_val_2707_; lean_object* v___x_2709_; 
lean_del_object(v___x_2689_);
lean_dec(v___x_2678_);
lean_dec(v_stx_2329_);
v_val_2707_ = lean_ctor_get(v_fst_2687_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v_fst_2687_, 1);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v_val_2707_);
v___x_2709_ = v___x_2685_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_val_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v___x_2678_);
lean_dec(v_stx_2329_);
v_a_2714_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2682_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2682_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2671_;
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2668_;
goto v___jp_2655_;
}
}
else
{
v___y_2656_ = v___y_2666_;
v___y_2657_ = v___y_2667_;
v___y_2658_ = v___y_2669_;
v___y_2659_ = v___y_2671_;
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2668_;
goto v___jp_2655_;
}
}
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4498_);
v___x_4500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
v___x_4501_ = l_Lean_Syntax_isOfKind(v___x_4499_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v_env_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
lean_del_object(v___x_2390_);
v___x_4502_ = lean_st_ref_get(v_a_2335_);
v_env_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc_ref(v_env_4503_);
lean_dec(v___x_4502_);
lean_inc_n(v_stx_2329_, 2);
v___x_4504_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4505_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4506_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4505_, v_env_4503_, v___x_4504_);
v___x_4507_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4508_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4506_, v___x_4507_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4506_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4539_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4511_ = v___x_4508_;
v_isShared_4512_ = v_isSharedCheck_4539_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4508_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4539_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v_fst_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4537_; 
v_fst_4513_ = lean_ctor_get(v_a_4509_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_a_4509_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; 
v_unused_4538_ = lean_ctor_get(v_a_4509_, 1);
lean_dec(v_unused_4538_);
v___x_4515_ = v_a_4509_;
v_isShared_4516_ = v_isSharedCheck_4537_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_fst_4513_);
lean_dec(v_a_4509_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4537_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
if (lean_obj_tag(v_fst_4513_) == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
lean_del_object(v___x_4511_);
v___x_4517_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4518_ = l_Lean_MessageData_ofName(v___x_4504_);
lean_inc_ref(v___x_4518_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set_tag(v___x_4515_, 7);
lean_ctor_set(v___x_4515_, 1, v___x_4518_);
lean_ctor_set(v___x_4515_, 0, v___x_4517_);
v___x_4520_ = v___x_4515_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4521_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4520_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
v___x_4523_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4524_ = l_Lean_indentD(v___x_4523_);
v___x_4525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4522_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
lean_ctor_set(v___x_4528_, 1, v___x_4518_);
v___x_4529_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
v___x_4531_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4530_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4531_;
}
}
else
{
lean_object* v_val_4533_; lean_object* v___x_4535_; 
lean_del_object(v___x_4515_);
lean_dec(v___x_4504_);
lean_dec(v_stx_2329_);
v_val_4533_ = lean_ctor_get(v_fst_4513_, 0);
lean_inc(v_val_4533_);
lean_dec_ref_known(v_fst_4513_, 1);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 0, v_val_4533_);
v___x_4535_ = v___x_4511_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_val_4533_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec(v___x_4504_);
lean_dec(v_stx_2329_);
v_a_4540_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4508_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4508_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
else
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4548_ = lean_unsigned_to_nat(1u);
v___x_4549_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4548_);
v___x_4550_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__86));
lean_inc(v___x_4549_);
v___x_4551_ = l_Lean_Syntax_isOfKind(v___x_4549_, v___x_4550_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v_env_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_dec(v___x_4549_);
lean_del_object(v___x_2390_);
v___x_4552_ = lean_st_ref_get(v_a_2335_);
v_env_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc_ref(v_env_4553_);
lean_dec(v___x_4552_);
lean_inc_n(v_stx_2329_, 2);
v___x_4554_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4555_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4556_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4555_, v_env_4553_, v___x_4554_);
v___x_4557_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4558_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4556_, v___x_4557_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4556_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4589_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4561_ = v___x_4558_;
v_isShared_4562_ = v_isSharedCheck_4589_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4558_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4589_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v_fst_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4587_; 
v_fst_4563_ = lean_ctor_get(v_a_4559_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_a_4559_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; 
v_unused_4588_ = lean_ctor_get(v_a_4559_, 1);
lean_dec(v_unused_4588_);
v___x_4565_ = v_a_4559_;
v_isShared_4566_ = v_isSharedCheck_4587_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_fst_4563_);
lean_dec(v_a_4559_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4587_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
if (lean_obj_tag(v_fst_4563_) == 0)
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4570_; 
lean_del_object(v___x_4561_);
v___x_4567_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4568_ = l_Lean_MessageData_ofName(v___x_4554_);
lean_inc_ref(v___x_4568_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set_tag(v___x_4565_, 7);
lean_ctor_set(v___x_4565_, 1, v___x_4568_);
lean_ctor_set(v___x_4565_, 0, v___x_4567_);
v___x_4570_ = v___x_4565_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4567_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4571_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
v___x_4573_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4574_ = l_Lean_indentD(v___x_4573_);
v___x_4575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4572_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4575_);
lean_ctor_set(v___x_4577_, 1, v___x_4576_);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v___x_4568_);
v___x_4579_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4578_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
v___x_4581_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4580_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4581_;
}
}
else
{
lean_object* v_val_4583_; lean_object* v___x_4585_; 
lean_del_object(v___x_4565_);
lean_dec(v___x_4554_);
lean_dec(v_stx_2329_);
v_val_4583_ = lean_ctor_get(v_fst_4563_, 0);
lean_inc(v_val_4583_);
lean_dec_ref_known(v_fst_4563_, 1);
if (v_isShared_4562_ == 0)
{
lean_ctor_set(v___x_4561_, 0, v_val_4583_);
v___x_4585_ = v___x_4561_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_val_4583_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec(v___x_4554_);
lean_dec(v_stx_2329_);
v_a_4590_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4558_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4558_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4598_ = l_Lean_Syntax_getArg(v___x_4549_, v___x_4498_);
lean_dec(v___x_4549_);
lean_inc(v___x_4598_);
v___x_4599_ = l_Lean_Syntax_matchesNull(v___x_4598_, v___x_4548_);
if (v___x_4599_ == 0)
{
lean_object* v___x_4600_; lean_object* v_env_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
lean_dec(v___x_4598_);
lean_del_object(v___x_2390_);
v___x_4600_ = lean_st_ref_get(v_a_2335_);
v_env_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc_ref(v_env_4601_);
lean_dec(v___x_4600_);
lean_inc_n(v_stx_2329_, 2);
v___x_4602_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4603_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4604_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4603_, v_env_4601_, v___x_4602_);
v___x_4605_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4606_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4604_, v___x_4605_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4604_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4637_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4637_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4637_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_fst_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4635_; 
v_fst_4611_ = lean_ctor_get(v_a_4607_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v_a_4607_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; 
v_unused_4636_ = lean_ctor_get(v_a_4607_, 1);
lean_dec(v_unused_4636_);
v___x_4613_ = v_a_4607_;
v_isShared_4614_ = v_isSharedCheck_4635_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_fst_4611_);
lean_dec(v_a_4607_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4635_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
if (lean_obj_tag(v_fst_4611_) == 0)
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
lean_del_object(v___x_4609_);
v___x_4615_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4616_ = l_Lean_MessageData_ofName(v___x_4602_);
lean_inc_ref(v___x_4616_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set_tag(v___x_4613_, 7);
lean_ctor_set(v___x_4613_, 1, v___x_4616_);
lean_ctor_set(v___x_4613_, 0, v___x_4615_);
v___x_4618_ = v___x_4613_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v___x_4616_);
v___x_4618_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4619_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4618_);
lean_ctor_set(v___x_4620_, 1, v___x_4619_);
v___x_4621_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4622_ = l_Lean_indentD(v___x_4621_);
v___x_4623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4620_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4623_);
lean_ctor_set(v___x_4625_, 1, v___x_4624_);
v___x_4626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
lean_ctor_set(v___x_4626_, 1, v___x_4616_);
v___x_4627_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4626_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4628_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4629_;
}
}
else
{
lean_object* v_val_4631_; lean_object* v___x_4633_; 
lean_del_object(v___x_4613_);
lean_dec(v___x_4602_);
lean_dec(v_stx_2329_);
v_val_4631_ = lean_ctor_get(v_fst_4611_, 0);
lean_inc(v_val_4631_);
lean_dec_ref_known(v_fst_4611_, 1);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v_val_4631_);
v___x_4633_ = v___x_4609_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_val_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_dec(v___x_4602_);
lean_dec(v_stx_2329_);
v_a_4638_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4606_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4606_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
else
{
if (v___x_2593_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4646_ = l_Lean_Syntax_getArg(v___x_4598_, v___x_4498_);
lean_dec(v___x_4598_);
v___x_4647_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__88));
v___x_4648_ = l_Lean_Syntax_isOfKind(v___x_4646_, v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; lean_object* v_env_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
lean_del_object(v___x_2390_);
v___x_4649_ = lean_st_ref_get(v_a_2335_);
v_env_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc_ref(v_env_4650_);
lean_dec(v___x_4649_);
lean_inc_n(v_stx_2329_, 2);
v___x_4651_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4652_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4653_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4652_, v_env_4650_, v___x_4651_);
v___x_4654_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4655_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4653_, v___x_4654_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4653_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4686_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4658_ = v___x_4655_;
v_isShared_4659_ = v_isSharedCheck_4686_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_dec(v___x_4655_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4686_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v_fst_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4684_; 
v_fst_4660_ = lean_ctor_get(v_a_4656_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_a_4656_);
if (v_isSharedCheck_4684_ == 0)
{
lean_object* v_unused_4685_; 
v_unused_4685_ = lean_ctor_get(v_a_4656_, 1);
lean_dec(v_unused_4685_);
v___x_4662_ = v_a_4656_;
v_isShared_4663_ = v_isSharedCheck_4684_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_fst_4660_);
lean_dec(v_a_4656_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4684_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
if (lean_obj_tag(v_fst_4660_) == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4667_; 
lean_del_object(v___x_4658_);
v___x_4664_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4665_ = l_Lean_MessageData_ofName(v___x_4651_);
lean_inc_ref(v___x_4665_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set_tag(v___x_4662_, 7);
lean_ctor_set(v___x_4662_, 1, v___x_4665_);
lean_ctor_set(v___x_4662_, 0, v___x_4664_);
v___x_4667_ = v___x_4662_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4668_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4671_ = l_Lean_indentD(v___x_4670_);
v___x_4672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4669_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
v___x_4673_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4672_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
lean_ctor_set(v___x_4675_, 1, v___x_4665_);
v___x_4676_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4675_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4677_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4678_;
}
}
else
{
lean_object* v_val_4680_; lean_object* v___x_4682_; 
lean_del_object(v___x_4662_);
lean_dec(v___x_4651_);
lean_dec(v_stx_2329_);
v_val_4680_ = lean_ctor_get(v_fst_4660_, 0);
lean_inc(v_val_4680_);
lean_dec_ref_known(v_fst_4660_, 1);
if (v_isShared_4659_ == 0)
{
lean_ctor_set(v___x_4658_, 0, v_val_4680_);
v___x_4682_ = v___x_4658_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_val_4680_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec(v___x_4651_);
lean_dec(v_stx_2329_);
v_a_4687_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4655_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4655_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_2392_;
}
}
else
{
lean_dec(v___x_4598_);
lean_dec(v_stx_2329_);
goto v___jp_2392_;
}
}
}
}
}
v___jp_2596_:
{
if (v___x_2595_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2603_ = lean_unsigned_to_nat(2u);
v___x_2604_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2603_);
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2606_ = l_Lean_Syntax_isOfKind(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v_env_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2607_ = lean_st_ref_get(v___y_2602_);
v_env_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc_ref(v_env_2608_);
lean_dec(v___x_2607_);
lean_inc_n(v_stx_2329_, 2);
v___x_2609_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2610_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2611_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2610_, v_env_2608_, v___x_2609_);
v___x_2612_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2613_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2611_, v___x_2612_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___x_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2644_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2644_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2644_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v_fst_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2642_; 
v_fst_2618_ = lean_ctor_get(v_a_2614_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2614_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v_a_2614_, 1);
lean_dec(v_unused_2643_);
v___x_2620_ = v_a_2614_;
v_isShared_2621_ = v_isSharedCheck_2642_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_fst_2618_);
lean_dec(v_a_2614_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2642_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
if (lean_obj_tag(v_fst_2618_) == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_del_object(v___x_2616_);
v___x_2622_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2623_ = l_Lean_MessageData_ofName(v___x_2609_);
lean_inc_ref(v___x_2623_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set_tag(v___x_2620_, 7);
lean_ctor_set(v___x_2620_, 1, v___x_2623_);
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2626_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2629_ = l_Lean_indentD(v___x_2628_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2627_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2623_);
v___x_2634_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2635_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2636_;
}
}
else
{
lean_object* v_val_2638_; lean_object* v___x_2640_; 
lean_del_object(v___x_2620_);
lean_dec(v___x_2609_);
lean_dec(v_stx_2329_);
v_val_2638_ = lean_ctor_get(v_fst_2618_, 0);
lean_inc(v_val_2638_);
lean_dec_ref_known(v_fst_2618_, 1);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v_val_2638_);
v___x_2640_ = v___x_2616_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_val_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v___x_2609_);
lean_dec(v_stx_2329_);
v_a_2645_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2613_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2613_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
v___y_2361_ = v___y_2602_;
v___y_2362_ = v___y_2598_;
v___y_2363_ = v___y_2599_;
v___y_2364_ = v___y_2600_;
v___y_2365_ = v___y_2601_;
v___y_2366_ = v___y_2597_;
goto v___jp_2360_;
}
}
else
{
v___y_2361_ = v___y_2602_;
v___y_2362_ = v___y_2598_;
v___y_2363_ = v___y_2599_;
v___y_2364_ = v___y_2600_;
v___y_2365_ = v___y_2601_;
v___y_2366_ = v___y_2597_;
goto v___jp_2360_;
}
}
}
else
{
lean_del_object(v___x_2390_);
if (v___x_2540_ == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4695_ = lean_unsigned_to_nat(1u);
v___x_4696_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4695_);
v___x_4697_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_4698_ = l_Lean_Syntax_isOfKind(v___x_4696_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; lean_object* v_env_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4699_ = lean_st_ref_get(v_a_2335_);
v_env_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc_ref(v_env_4700_);
lean_dec(v___x_4699_);
lean_inc_n(v_stx_2329_, 2);
v___x_4701_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4702_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4703_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4702_, v_env_4700_, v___x_4701_);
v___x_4704_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4705_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4703_, v___x_4704_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4703_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4736_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4708_ = v___x_4705_;
v_isShared_4709_ = v_isSharedCheck_4736_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4736_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_fst_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4734_; 
v_fst_4710_ = lean_ctor_get(v_a_4706_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v_a_4706_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v_a_4706_, 1);
lean_dec(v_unused_4735_);
v___x_4712_ = v_a_4706_;
v_isShared_4713_ = v_isSharedCheck_4734_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_fst_4710_);
lean_dec(v_a_4706_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4734_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
if (lean_obj_tag(v_fst_4710_) == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
lean_del_object(v___x_4708_);
v___x_4714_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4715_ = l_Lean_MessageData_ofName(v___x_4701_);
lean_inc_ref(v___x_4715_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set_tag(v___x_4712_, 7);
lean_ctor_set(v___x_4712_, 1, v___x_4715_);
lean_ctor_set(v___x_4712_, 0, v___x_4714_);
v___x_4717_ = v___x_4712_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4718_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4721_ = l_Lean_indentD(v___x_4720_);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4719_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4724_);
lean_ctor_set(v___x_4725_, 1, v___x_4715_);
v___x_4726_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4725_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
v___x_4728_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4727_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4728_;
}
}
else
{
lean_object* v_val_4730_; lean_object* v___x_4732_; 
lean_del_object(v___x_4712_);
lean_dec(v___x_4701_);
lean_dec(v_stx_2329_);
v_val_4730_ = lean_ctor_get(v_fst_4710_, 0);
lean_inc(v_val_4730_);
lean_dec_ref_known(v_fst_4710_, 1);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 0, v_val_4730_);
v___x_4732_ = v___x_4708_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_val_4730_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec(v___x_4701_);
lean_dec(v_stx_2329_);
v_a_4737_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4705_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4705_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
else
{
goto v___jp_2541_;
}
}
else
{
goto v___jp_2541_;
}
}
}
else
{
lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
lean_del_object(v___x_2390_);
v___x_4745_ = lean_unsigned_to_nat(1u);
v___x_4746_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4745_);
v___x_4747_ = l_Lean_Syntax_isNone(v___x_4746_);
if (v___x_4747_ == 0)
{
uint8_t v___x_4748_; 
v___x_4748_ = l_Lean_Syntax_matchesNull(v___x_4746_, v___x_4745_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; lean_object* v_env_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4749_ = lean_st_ref_get(v_a_2335_);
v_env_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc_ref(v_env_4750_);
lean_dec(v___x_4749_);
lean_inc_n(v_stx_2329_, 2);
v___x_4751_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4752_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4753_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4752_, v_env_4750_, v___x_4751_);
v___x_4754_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4755_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4753_, v___x_4754_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4753_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4786_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4786_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4786_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v_fst_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4784_; 
v_fst_4760_ = lean_ctor_get(v_a_4756_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_a_4756_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v_a_4756_, 1);
lean_dec(v_unused_4785_);
v___x_4762_ = v_a_4756_;
v_isShared_4763_ = v_isSharedCheck_4784_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_fst_4760_);
lean_dec(v_a_4756_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4784_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
if (lean_obj_tag(v_fst_4760_) == 0)
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4767_; 
lean_del_object(v___x_4758_);
v___x_4764_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4765_ = l_Lean_MessageData_ofName(v___x_4751_);
lean_inc_ref(v___x_4765_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set_tag(v___x_4762_, 7);
lean_ctor_set(v___x_4762_, 1, v___x_4765_);
lean_ctor_set(v___x_4762_, 0, v___x_4764_);
v___x_4767_ = v___x_4762_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4779_, 1, v___x_4765_);
v___x_4767_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4768_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4767_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4771_ = l_Lean_indentD(v___x_4770_);
v___x_4772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4769_);
lean_ctor_set(v___x_4772_, 1, v___x_4771_);
v___x_4773_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
lean_ctor_set(v___x_4775_, 1, v___x_4765_);
v___x_4776_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v___x_4778_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4777_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4778_;
}
}
else
{
lean_object* v_val_4780_; lean_object* v___x_4782_; 
lean_del_object(v___x_4762_);
lean_dec(v___x_4751_);
lean_dec(v_stx_2329_);
v_val_4780_ = lean_ctor_get(v_fst_4760_, 0);
lean_inc(v_val_4780_);
lean_dec_ref_known(v_fst_4760_, 1);
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 0, v_val_4780_);
v___x_4782_ = v___x_4758_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_val_4780_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v___x_4751_);
lean_dec(v_stx_2329_);
v_a_4787_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4755_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4755_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
v___y_2483_ = v_a_2330_;
v___y_2484_ = v_a_2331_;
v___y_2485_ = v_a_2332_;
v___y_2486_ = v_a_2333_;
v___y_2487_ = v_a_2334_;
v___y_2488_ = v_a_2335_;
goto v___jp_2482_;
}
}
else
{
lean_dec(v___x_4746_);
v___y_2483_ = v_a_2330_;
v___y_2484_ = v_a_2331_;
v___y_2485_ = v_a_2332_;
v___y_2486_ = v_a_2333_;
v___y_2487_ = v_a_2334_;
v___y_2488_ = v_a_2335_;
goto v___jp_2482_;
}
}
v___jp_2541_:
{
if (v___x_2540_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2542_ = lean_unsigned_to_nat(2u);
v___x_2543_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2542_);
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2545_ = l_Lean_Syntax_isOfKind(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v_env_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2546_ = lean_st_ref_get(v_a_2335_);
v_env_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref(v_env_2547_);
lean_dec(v___x_2546_);
lean_inc_n(v_stx_2329_, 2);
v___x_2548_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2549_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2550_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2549_, v_env_2547_, v___x_2548_);
v___x_2551_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2552_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2550_, v___x_2551_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_2550_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2583_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2583_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2583_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_fst_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2581_; 
v_fst_2557_ = lean_ctor_get(v_a_2553_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_a_2553_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v_a_2553_, 1);
lean_dec(v_unused_2582_);
v___x_2559_ = v_a_2553_;
v_isShared_2560_ = v_isSharedCheck_2581_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_fst_2557_);
lean_dec(v_a_2553_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2581_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
if (lean_obj_tag(v_fst_2557_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
lean_del_object(v___x_2555_);
v___x_2561_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2562_ = l_Lean_MessageData_ofName(v___x_2548_);
lean_inc_ref(v___x_2562_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 7);
lean_ctor_set(v___x_2559_, 1, v___x_2562_);
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2565_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2564_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2568_ = l_Lean_indentD(v___x_2567_);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2566_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___x_2562_);
v___x_2573_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2574_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2575_;
}
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2579_; 
lean_del_object(v___x_2559_);
lean_dec(v___x_2548_);
lean_dec(v_stx_2329_);
v_val_2577_ = lean_ctor_get(v_fst_2557_, 0);
lean_inc(v_val_2577_);
lean_dec_ref_known(v_fst_2557_, 1);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_val_2577_);
v___x_2579_ = v___x_2555_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_val_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v___x_2548_);
lean_dec(v_stx_2329_);
v_a_2584_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2552_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2552_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_2397_;
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_2397_;
}
}
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_del_object(v___x_2390_);
v___x_4795_ = lean_unsigned_to_nat(1u);
v___x_4796_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4795_);
lean_dec(v_stx_2329_);
v___x_4797_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v___x_4796_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4797_;
}
v___jp_2425_:
{
if (v___x_2424_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2432_ = lean_unsigned_to_nat(3u);
v___x_2433_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
v___x_2435_ = l_Lean_Syntax_isOfKind(v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v_env_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2436_ = lean_st_ref_get(v___y_2426_);
v_env_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc_ref(v_env_2437_);
lean_dec(v___x_2436_);
lean_inc_n(v_stx_2329_, 2);
v___x_2438_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2439_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2440_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2439_, v_env_2437_, v___x_2438_);
v___x_2441_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2442_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2440_, v___x_2441_, v___y_2431_, v___y_2430_, v___y_2428_, v___y_2427_, v___y_2429_, v___y_2426_);
lean_dec(v___x_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2473_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2473_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2473_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_fst_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2471_; 
v_fst_2447_ = lean_ctor_get(v_a_2443_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_a_2443_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v_a_2443_, 1);
lean_dec(v_unused_2472_);
v___x_2449_ = v_a_2443_;
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_fst_2447_);
lean_dec(v_a_2443_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
if (lean_obj_tag(v_fst_2447_) == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
lean_del_object(v___x_2445_);
v___x_2451_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2452_ = l_Lean_MessageData_ofName(v___x_2438_);
lean_inc_ref(v___x_2452_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 7);
lean_ctor_set(v___x_2449_, 1, v___x_2452_);
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2455_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2458_ = l_Lean_indentD(v___x_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2452_);
v___x_2463_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2464_, v___y_2431_, v___y_2430_, v___y_2428_, v___y_2427_, v___y_2429_, v___y_2426_);
return v___x_2465_;
}
}
else
{
lean_object* v_val_2467_; lean_object* v___x_2469_; 
lean_del_object(v___x_2449_);
lean_dec(v___x_2438_);
lean_dec(v_stx_2329_);
v_val_2467_ = lean_ctor_get(v_fst_2447_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v_fst_2447_, 1);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v_val_2467_);
v___x_2469_ = v___x_2445_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_val_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v___x_2438_);
lean_dec(v_stx_2329_);
v_a_2474_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2442_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2442_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_2381_;
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_2381_;
}
}
v___jp_2482_:
{
if (v___x_2424_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2489_ = lean_unsigned_to_nat(2u);
v___x_2490_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2489_);
v___x_2491_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
v___x_2492_ = l_Lean_Syntax_isOfKind(v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; lean_object* v_env_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2493_ = lean_st_ref_get(v___y_2488_);
v_env_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_ref(v_env_2494_);
lean_dec(v___x_2493_);
lean_inc_n(v_stx_2329_, 2);
v___x_2495_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_2496_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_2497_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_2496_, v_env_2494_, v___x_2495_);
v___x_2498_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_2499_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_2497_, v___x_2498_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___x_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2530_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2530_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2530_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_fst_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2528_; 
v_fst_2504_ = lean_ctor_get(v_a_2500_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_a_2500_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_a_2500_, 1);
lean_dec(v_unused_2529_);
v___x_2506_ = v_a_2500_;
v_isShared_2507_ = v_isSharedCheck_2528_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_fst_2504_);
lean_dec(v_a_2500_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2528_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
if (lean_obj_tag(v_fst_2504_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_del_object(v___x_2502_);
v___x_2508_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_2509_ = l_Lean_MessageData_ofName(v___x_2495_);
lean_inc_ref(v___x_2509_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set_tag(v___x_2506_, 7);
lean_ctor_set(v___x_2506_, 1, v___x_2509_);
lean_ctor_set(v___x_2506_, 0, v___x_2508_);
v___x_2511_ = v___x_2506_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2512_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_2515_ = l_Lean_indentD(v___x_2514_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2513_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2509_);
v___x_2520_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_2521_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2522_;
}
}
else
{
lean_object* v_val_2524_; lean_object* v___x_2526_; 
lean_del_object(v___x_2506_);
lean_dec(v___x_2495_);
lean_dec(v_stx_2329_);
v_val_2524_ = lean_ctor_get(v_fst_2504_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_fst_2504_, 1);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v_val_2524_);
v___x_2526_ = v___x_2502_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v___x_2495_);
lean_dec(v_stx_2329_);
v_a_2531_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2499_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2499_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
v___y_2426_ = v___y_2488_;
v___y_2427_ = v___y_2486_;
v___y_2428_ = v___y_2485_;
v___y_2429_ = v___y_2487_;
v___y_2430_ = v___y_2484_;
v___y_2431_ = v___y_2483_;
goto v___jp_2425_;
}
}
else
{
v___y_2426_ = v___y_2488_;
v___y_2427_ = v___y_2486_;
v___y_2428_ = v___y_2485_;
v___y_2429_ = v___y_2487_;
v___y_2430_ = v___y_2484_;
v___y_2431_ = v___y_2483_;
goto v___jp_2425_;
}
}
}
else
{
lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
lean_del_object(v___x_2390_);
v___x_4798_ = lean_unsigned_to_nat(0u);
v___x_4799_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4798_);
lean_dec(v_stx_2329_);
v___x_4800_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v___x_4799_);
if (lean_obj_tag(v___x_4800_) == 1)
{
lean_object* v_val_4801_; lean_object* v_snd_4802_; lean_object* v_body_4803_; lean_object* v___x_4804_; 
v_val_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc(v_val_4801_);
lean_dec_ref_known(v___x_4800_, 1);
v_snd_4802_ = lean_ctor_get(v_val_4801_, 1);
lean_inc(v_snd_4802_);
lean_dec(v_val_4801_);
v_body_4803_ = lean_ctor_get(v_snd_4802_, 1);
lean_inc(v_body_4803_);
lean_dec(v_snd_4802_);
v___x_4804_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_4803_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4825_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4807_ = v___x_4804_;
v_isShared_4808_ = v_isSharedCheck_4825_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4825_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
uint8_t v_breaks_4809_; uint8_t v_continues_4810_; uint8_t v_returnsEarly_4811_; lean_object* v_reassigns_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4823_; 
v_breaks_4809_ = lean_ctor_get_uint8(v_a_4805_, sizeof(void*)*2);
v_continues_4810_ = lean_ctor_get_uint8(v_a_4805_, sizeof(void*)*2 + 1);
v_returnsEarly_4811_ = lean_ctor_get_uint8(v_a_4805_, sizeof(void*)*2 + 2);
v_reassigns_4812_ = lean_ctor_get(v_a_4805_, 1);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_a_4805_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v_a_4805_, 0);
lean_dec(v_unused_4824_);
v___x_4814_ = v_a_4805_;
v_isShared_4815_ = v_isSharedCheck_4823_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_reassigns_4812_);
lean_dec(v_a_4805_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4823_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v___x_4818_; 
v___x_4816_ = lean_unsigned_to_nat(1u);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v___x_4816_);
v___x_4818_ = v___x_4814_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v_reassigns_4812_);
lean_ctor_set_uint8(v_reuseFailAlloc_4822_, sizeof(void*)*2, v_breaks_4809_);
lean_ctor_set_uint8(v_reuseFailAlloc_4822_, sizeof(void*)*2 + 1, v_continues_4810_);
lean_ctor_set_uint8(v_reuseFailAlloc_4822_, sizeof(void*)*2 + 2, v_returnsEarly_4811_);
v___x_4818_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
lean_object* v___x_4820_; 
lean_ctor_set_uint8(v___x_4818_, sizeof(void*)*2 + 3, v___x_2420_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4818_);
v___x_4820_ = v___x_4807_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
}
else
{
return v___x_4804_;
}
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_dec(v___x_4800_);
v___x_4826_ = lean_unsigned_to_nat(1u);
v___x_4827_ = l_Lean_NameSet_empty;
v___x_4828_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*2, v___x_2420_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*2 + 1, v___x_2420_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*2 + 2, v___x_2420_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*2 + 3, v___x_2420_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
}
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4835_; lean_object* v___x_4836_; uint8_t v___x_4837_; 
lean_del_object(v___x_2390_);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4835_ = lean_unsigned_to_nat(1u);
v___x_4836_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_4835_);
v___x_4837_ = l_Lean_Syntax_isNone(v___x_4836_);
if (v___x_4837_ == 0)
{
uint8_t v___x_4838_; 
v___x_4838_ = l_Lean_Syntax_matchesNull(v___x_4836_, v___x_4835_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; lean_object* v_env_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4839_ = lean_st_ref_get(v_a_2335_);
v_env_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc_ref(v_env_4840_);
lean_dec(v___x_4839_);
lean_inc_n(v_stx_2329_, 2);
v___x_4841_ = l_Lean_Syntax_getKind(v_stx_2329_);
v___x_4842_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_4843_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_4842_, v_env_4840_, v___x_4841_);
v___x_4844_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
v___x_4845_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_2329_, v___x_4843_, v___x_4844_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v___x_4843_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4876_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4876_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4876_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v_fst_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4874_; 
v_fst_4850_ = lean_ctor_get(v_a_4846_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_a_4846_);
if (v_isSharedCheck_4874_ == 0)
{
lean_object* v_unused_4875_; 
v_unused_4875_ = lean_ctor_get(v_a_4846_, 1);
lean_dec(v_unused_4875_);
v___x_4852_ = v_a_4846_;
v_isShared_4853_ = v_isSharedCheck_4874_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_fst_4850_);
lean_dec(v_a_4846_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4874_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
if (lean_obj_tag(v_fst_4850_) == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4857_; 
lean_del_object(v___x_4848_);
v___x_4854_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13);
v___x_4855_ = l_Lean_MessageData_ofName(v___x_4841_);
lean_inc_ref(v___x_4855_);
if (v_isShared_4853_ == 0)
{
lean_ctor_set_tag(v___x_4852_, 7);
lean_ctor_set(v___x_4852_, 1, v___x_4855_);
lean_ctor_set(v___x_4852_, 0, v___x_4854_);
v___x_4857_ = v___x_4852_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4854_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v___x_4855_);
v___x_4857_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4858_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15);
v___x_4859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4857_);
lean_ctor_set(v___x_4859_, 1, v___x_4858_);
v___x_4860_ = l_Lean_MessageData_ofSyntax(v_stx_2329_);
v___x_4861_ = l_Lean_indentD(v___x_4860_);
v___x_4862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4859_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___x_4863_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v___x_4855_);
v___x_4866_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19);
v___x_4867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4865_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v___x_4867_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_4868_;
}
}
else
{
lean_object* v_val_4870_; lean_object* v___x_4872_; 
lean_del_object(v___x_4852_);
lean_dec(v___x_4841_);
lean_dec(v_stx_2329_);
v_val_4870_ = lean_ctor_get(v_fst_4850_, 0);
lean_inc(v_val_4870_);
lean_dec_ref_known(v_fst_4850_, 1);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v_val_4870_);
v___x_4872_ = v___x_4848_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_val_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v___x_4841_);
lean_dec(v_stx_2329_);
v_a_4877_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4845_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4845_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_dec(v_stx_2329_);
goto v___jp_4831_;
}
}
else
{
lean_dec(v___x_4836_);
lean_dec(v_stx_2329_);
goto v___jp_4831_;
}
v___jp_4831_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4832_ = l_Lean_NameSet_empty;
v___x_4833_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4833_, 0, v___x_4830_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
lean_ctor_set_uint8(v___x_4833_, sizeof(void*)*2, v___x_2418_);
lean_ctor_set_uint8(v___x_4833_, sizeof(void*)*2 + 1, v___x_2418_);
lean_ctor_set_uint8(v___x_4833_, sizeof(void*)*2 + 2, v___x_2416_);
lean_ctor_set_uint8(v___x_4833_, sizeof(void*)*2 + 3, v___x_2416_);
v___x_4834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
return v___x_4834_;
}
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
lean_del_object(v___x_2390_);
lean_dec(v_stx_2329_);
v___x_4885_ = lean_unsigned_to_nat(0u);
v___x_4886_ = l_Lean_NameSet_empty;
v___x_4887_ = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*2, v___x_2415_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*2 + 1, v___x_2416_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*2 + 2, v___x_2415_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*2 + 3, v___x_2416_);
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
return v___x_4888_;
}
}
else
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_del_object(v___x_2390_);
lean_dec(v_stx_2329_);
v___x_4889_ = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__89);
v___x_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
return v___x_4890_;
}
}
v___jp_2392_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = l_Lean_Elab_Do_ControlInfo_pure;
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_stx_2329_);
v_a_4892_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_2387_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_2387_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
v___jp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2338_, v_bodyInfo_2339_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
v___jp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = l_Lean_Elab_Do_ControlInfo_alternative(v___y_2343_, v_bodyInfo_2344_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
v___jp_2347_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2356_ = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6));
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2353_);
v___x_2359_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v___x_2356_, v___x_2357_, v___x_2358_, v___y_2355_, v___y_2354_, v___y_2349_, v___y_2350_, v___y_2352_, v___y_2351_, v___y_2348_);
return v___x_2359_;
}
v___jp_2360_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2367_ = lean_unsigned_to_nat(7u);
v___x_2368_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2367_);
v___x_2369_ = lean_unsigned_to_nat(8u);
v___x_2370_ = l_Lean_Syntax_getArg(v_stx_2329_, v___x_2369_);
lean_dec(v_stx_2329_);
v___x_2371_ = l_Lean_Syntax_getOptional_x3f(v___x_2370_);
lean_dec(v___x_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_box(0);
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___y_2365_;
v___y_2352_ = v___y_2364_;
v___y_2353_ = v___x_2368_;
v___y_2354_ = v___y_2366_;
v___y_2355_ = v___x_2372_;
goto v___jp_2347_;
}
else
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
v_val_2373_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2371_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v___x_2371_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_val_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
v___y_2348_ = v___y_2361_;
v___y_2349_ = v___y_2362_;
v___y_2350_ = v___y_2363_;
v___y_2351_ = v___y_2365_;
v___y_2352_ = v___y_2364_;
v___y_2353_ = v___x_2368_;
v___y_2354_ = v___y_2366_;
v___y_2355_ = v___x_2378_;
goto v___jp_2347_;
}
}
}
}
v___jp_2381_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = l_Lean_Elab_Do_ControlInfo_pure;
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* v_as_4900_, size_t v_sz_4901_, size_t v_i_4902_, lean_object* v_b_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v___x_4911_; 
v___x_4911_ = lean_usize_dec_lt(v_i_4902_, v_sz_4901_);
if (v___x_4911_ == 0)
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_b_4903_);
return v___x_4912_;
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
v_a_4913_ = lean_array_uget_borrowed(v_as_4900_, v_i_4902_);
lean_inc(v_a_4913_);
v___x_4914_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_a_4913_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; size_t v___x_4917_; size_t v___x_4918_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = l_Lean_Elab_Do_ControlInfo_sequence(v_b_4903_, v_a_4915_);
v___x_4917_ = ((size_t)1ULL);
v___x_4918_ = lean_usize_add(v_i_4902_, v___x_4917_);
v_i_4902_ = v___x_4918_;
v_b_4903_ = v___x_4916_;
goto _start;
}
else
{
lean_dec_ref(v_b_4903_);
return v___x_4914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* v_stx_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_){
_start:
{
lean_object* v_info_4928_; lean_object* v___x_4929_; size_t v_sz_4930_; size_t v___x_4931_; lean_object* v___x_4932_; 
v_info_4928_ = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
v___x_4929_ = l_Lean_Parser_Term_getDoElems(v_stx_4920_);
v_sz_4930_ = lean_array_size(v___x_4929_);
v___x_4931_ = ((size_t)0ULL);
v___x_4932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v___x_4929_, v_sz_4930_, v___x_4931_, v_info_4928_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
lean_dec_ref(v___x_4929_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* v_stx_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_stx_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec_ref(v_a_4934_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* v_stx_x3f_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(v_stx_x3f_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* v_as_4951_, lean_object* v_sz_4952_, lean_object* v_i_4953_, lean_object* v_b_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
size_t v_sz_boxed_4962_; size_t v_i_boxed_4963_; lean_object* v_res_4964_; 
v_sz_boxed_4962_ = lean_unbox_usize(v_sz_4952_);
lean_dec(v_sz_4952_);
v_i_boxed_4963_ = lean_unbox_usize(v_i_4953_);
lean_dec(v_i_4953_);
v_res_4964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(v_as_4951_, v_sz_boxed_4962_, v_i_boxed_4963_, v_b_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_);
lean_dec(v___y_4960_);
lean_dec_ref(v___y_4959_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec_ref(v_as_4951_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* v_as_4965_, lean_object* v_sz_4966_, lean_object* v_i_4967_, lean_object* v_b_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
size_t v_sz_boxed_4976_; size_t v_i_boxed_4977_; lean_object* v_res_4978_; 
v_sz_boxed_4976_ = lean_unbox_usize(v_sz_4966_);
lean_dec(v_sz_4966_);
v_i_boxed_4977_ = lean_unbox_usize(v_i_4967_);
lean_dec(v_i_4967_);
v_res_4978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(v_as_4965_, v_sz_boxed_4976_, v_i_boxed_4977_, v_b_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
lean_dec_ref(v_as_4965_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* v___x_4979_, lean_object* v_as_4980_, lean_object* v_sz_4981_, lean_object* v_i_4982_, lean_object* v_b_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
uint8_t v___x_166323__boxed_4991_; size_t v_sz_boxed_4992_; size_t v_i_boxed_4993_; lean_object* v_res_4994_; 
v___x_166323__boxed_4991_ = lean_unbox(v___x_4979_);
v_sz_boxed_4992_ = lean_unbox_usize(v_sz_4981_);
lean_dec(v_sz_4981_);
v_i_boxed_4993_ = lean_unbox_usize(v_i_4982_);
lean_dec(v_i_4982_);
v_res_4994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(v___x_166323__boxed_4991_, v_as_4980_, v_sz_boxed_4992_, v_i_boxed_4993_, v_b_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
lean_dec(v___y_4987_);
lean_dec_ref(v___y_4986_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec_ref(v_as_4980_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* v___x_4995_, lean_object* v_as_4996_, lean_object* v_sz_4997_, lean_object* v_i_4998_, lean_object* v_b_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
uint8_t v___x_166370__boxed_5007_; size_t v_sz_boxed_5008_; size_t v_i_boxed_5009_; lean_object* v_res_5010_; 
v___x_166370__boxed_5007_ = lean_unbox(v___x_4995_);
v_sz_boxed_5008_ = lean_unbox_usize(v_sz_4997_);
lean_dec(v_sz_4997_);
v_i_boxed_5009_ = lean_unbox_usize(v_i_4998_);
lean_dec(v_i_4998_);
v_res_5010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(v___x_166370__boxed_5007_, v_as_4996_, v_sz_boxed_5008_, v_i_boxed_5009_, v_b_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec_ref(v_as_4996_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* v_reassigned_5011_, lean_object* v_rhs_x3f_5012_, lean_object* v_otherwise_x3f_5013_, lean_object* v_body_x3f_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v_res_5022_; 
v_res_5022_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(v_reassigned_5011_, v_rhs_x3f_5012_, v_otherwise_x3f_5013_, v_body_x3f_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* v_as_5023_, lean_object* v_sz_5024_, lean_object* v_i_5025_, lean_object* v_b_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
size_t v_sz_boxed_5034_; size_t v_i_boxed_5035_; lean_object* v_res_5036_; 
v_sz_boxed_5034_ = lean_unbox_usize(v_sz_5024_);
lean_dec(v_sz_5024_);
v_i_boxed_5035_ = lean_unbox_usize(v_i_5025_);
lean_dec(v_i_5025_);
v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(v_as_5023_, v_sz_boxed_5034_, v_i_boxed_5035_, v_b_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec_ref(v_as_5023_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* v_reassignment_5037_, lean_object* v_decl_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_){
_start:
{
uint8_t v_reassignment_boxed_5046_; lean_object* v_res_5047_; 
v_reassignment_boxed_5046_ = lean_unbox(v_reassignment_5037_);
v_res_5047_ = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(v_reassignment_boxed_5046_, v_decl_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* v_stx_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_stx_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_);
lean_dec(v_a_5054_);
lean_dec_ref(v_a_5053_);
lean_dec(v_a_5052_);
lean_dec_ref(v_a_5051_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(lean_object* v_00_u03b1_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v___x_5065_; 
v___x_5065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___redArg();
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* v_00_u03b1_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(v_00_u03b1_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* v_00_u03b1_5075_, lean_object* v_ref_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(v_ref_5076_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* v_00_u03b1_5085_, lean_object* v_ref_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(v_00_u03b1_5085_, v_ref_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* v_00_u03b1_5095_, lean_object* v_x_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(v_x_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* v_00_u03b1_5105_, lean_object* v_x_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(v_00_u03b1_5105_, v_x_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* v_stx_5115_, lean_object* v_as_5116_, lean_object* v_as_x27_5117_, lean_object* v_b_5118_, lean_object* v_a_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(v_stx_5115_, v_as_x27_5117_, v_b_5118_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* v_stx_5128_, lean_object* v_as_5129_, lean_object* v_as_x27_5130_, lean_object* v_b_5131_, lean_object* v_a_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(v_stx_5128_, v_as_5129_, v_as_x27_5130_, v_b_5131_, v_a_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
lean_dec(v___y_5138_);
lean_dec_ref(v___y_5137_);
lean_dec(v___y_5136_);
lean_dec_ref(v___y_5135_);
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v_as_x27_5130_);
lean_dec(v_as_5129_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* v_00_u03b1_5141_, lean_object* v_msg_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(v_msg_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* v_00_u03b1_5151_, lean_object* v_msg_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(v_00_u03b1_5151_, v_msg_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* v_cls_5161_, lean_object* v_msg_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_){
_start:
{
lean_object* v___x_5170_; 
v___x_5170_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(v_cls_5161_, v_msg_5162_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* v_cls_5171_, lean_object* v_msg_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(v_cls_5171_, v_msg_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
lean_dec(v___y_5178_);
lean_dec_ref(v___y_5177_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* v_as_5181_, lean_object* v_as_x27_5182_, lean_object* v_b_5183_, lean_object* v_a_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___redArg(v_as_x27_5182_, v_b_5183_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* v_as_5193_, lean_object* v_as_x27_5194_, lean_object* v_b_5195_, lean_object* v_a_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(v_as_5193_, v_as_x27_5194_, v_b_5195_, v_a_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
lean_dec(v_as_x27_5194_);
lean_dec(v_as_5193_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* v_00_u03b1_5205_, lean_object* v_ref_5206_, lean_object* v_msg_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___redArg(v_ref_5206_, v_msg_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* v_00_u03b1_5216_, lean_object* v_ref_5217_, lean_object* v_msg_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(v_00_u03b1_5216_, v_ref_5217_, v_msg_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
lean_dec(v_ref_5217_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* v_msgData_5227_, lean_object* v_macroStack_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_){
_start:
{
lean_object* v___x_5236_; 
v___x_5236_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___redArg(v_msgData_5227_, v_macroStack_5228_, v___y_5233_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* v_msgData_5237_, lean_object* v_macroStack_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(v_msgData_5237_, v_macroStack_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(lean_object* v_00_u03b2_5247_, lean_object* v_m_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___redArg(v_m_5248_, v_a_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10___boxed(lean_object* v_00_u03b2_5251_, lean_object* v_m_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10(v_00_u03b2_5251_, v_m_5252_, v_a_5253_);
lean_dec(v_a_5253_);
lean_dec_ref(v_m_5252_);
return v_res_5254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(lean_object* v_00_u03b2_5255_, lean_object* v_x_5256_, lean_object* v_x_5257_){
_start:
{
uint8_t v___x_5258_; 
v___x_5258_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___redArg(v_x_5256_, v_x_5257_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26___boxed(lean_object* v_00_u03b2_5259_, lean_object* v_x_5260_, lean_object* v_x_5261_){
_start:
{
uint8_t v_res_5262_; lean_object* v_r_5263_; 
v_res_5262_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26(v_00_u03b2_5259_, v_x_5260_, v_x_5261_);
lean_dec_ref(v_x_5261_);
lean_dec_ref(v_x_5260_);
v_r_5263_ = lean_box(v_res_5262_);
return v_r_5263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(lean_object* v_00_u03b2_5264_, lean_object* v_a_5265_, lean_object* v_x_5266_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___redArg(v_a_5265_, v_x_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29___boxed(lean_object* v_00_u03b2_5268_, lean_object* v_a_5269_, lean_object* v_x_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__10_spec__29(v_00_u03b2_5268_, v_a_5269_, v_x_5270_);
lean_dec(v_x_5270_);
lean_dec(v_a_5269_);
return v_res_5271_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(lean_object* v_00_u03b2_5272_, lean_object* v_x_5273_, size_t v_x_5274_, lean_object* v_x_5275_){
_start:
{
uint8_t v___x_5276_; 
v___x_5276_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___redArg(v_x_5273_, v_x_5274_, v_x_5275_);
return v___x_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32___boxed(lean_object* v_00_u03b2_5277_, lean_object* v_x_5278_, lean_object* v_x_5279_, lean_object* v_x_5280_){
_start:
{
size_t v_x_173075__boxed_5281_; uint8_t v_res_5282_; lean_object* v_r_5283_; 
v_x_173075__boxed_5281_ = lean_unbox_usize(v_x_5279_);
lean_dec(v_x_5279_);
v_res_5282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32(v_00_u03b2_5277_, v_x_5278_, v_x_173075__boxed_5281_, v_x_5280_);
lean_dec_ref(v_x_5280_);
lean_dec_ref(v_x_5278_);
v_r_5283_ = lean_box(v_res_5282_);
return v_r_5283_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(lean_object* v_00_u03b2_5284_, lean_object* v_keys_5285_, lean_object* v_vals_5286_, lean_object* v_heq_5287_, lean_object* v_i_5288_, lean_object* v_k_5289_){
_start:
{
uint8_t v___x_5290_; 
v___x_5290_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___redArg(v_keys_5285_, v_i_5288_, v_k_5289_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36___boxed(lean_object* v_00_u03b2_5291_, lean_object* v_keys_5292_, lean_object* v_vals_5293_, lean_object* v_heq_5294_, lean_object* v_i_5295_, lean_object* v_k_5296_){
_start:
{
uint8_t v_res_5297_; lean_object* v_r_5298_; 
v_res_5297_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2_spec__8_spec__26_spec__32_spec__36(v_00_u03b2_5291_, v_keys_5292_, v_vals_5293_, v_heq_5294_, v_i_5295_, v_k_5296_);
lean_dec_ref(v_k_5296_);
lean_dec_ref(v_vals_5293_);
lean_dec_ref(v_keys_5292_);
v_r_5298_ = lean_box(v_res_5297_);
return v_r_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* v_doSeq_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_doSeq_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* v_doSeq_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_Elab_Do_inferControlInfoSeq(v_doSeq_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_);
lean_dec(v_a_5314_);
lean_dec_ref(v_a_5313_);
lean_dec(v_a_5312_);
lean_dec_ref(v_a_5311_);
lean_dec(v_a_5310_);
lean_dec_ref(v_a_5309_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* v_doElem_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_){
_start:
{
lean_object* v___x_5325_; 
v___x_5325_ = l_Lean_Elab_Do_InferControlInfo_ofElem(v_doElem_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* v_doElem_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l_Lean_Elab_Do_inferControlInfoElem(v_doElem_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
lean_dec(v_a_5332_);
lean_dec_ref(v_a_5331_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
return v_res_5334_;
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
