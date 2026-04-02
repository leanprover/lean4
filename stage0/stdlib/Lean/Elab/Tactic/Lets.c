// Lean compiler output
// Module: Lean.Elab.Tactic.Lets
// Imports: public import Lean.Meta.Tactic.Lets public import Lean.Elab.Tactic.Location import Lean.Elab.Binders import Lean.Linter.Basic
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
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_MVarId_letToHave(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_letToHaveLocalDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_extractLetsLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_liftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* l_Lean_MVarId_extractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "unusedName"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 206, 61, 199, 208, 244, 88, 253)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 220, 201, 55, 250, 95, 85, 187)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "enable the 'unused name' tactic linter"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 218, 239, 141, 209, 224, 98, 123)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 199, 243, 68, 217, 216, 62, 142)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 222, 21, 214, 118, 132, 172, 125)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_linter_tactic_unusedName;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unused name"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ExtractLetsConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(146, 95, 47, 57, 208, 157, 66, 165)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "'extract_lets' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLets"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 152, 152, 121, 17, 54, 202)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__3_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalExtractLets___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__6_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalExtractLets"};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 187, 108, 174, 23, 225, 147, 32)}};
static const lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "LiftLetsConfig"};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(15, 138, 90, 221, 135, 228, 98, 245)}};
static const lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1;
static const lean_ctor_object l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 16, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "'lift_lets' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "liftLets"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 154, 84, 113, 122, 200, 54, 62)}};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLiftLets___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalLiftLets"};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 204, 119, 233, 20, 201, 134, 20)}};
static const lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "'let_to_have' tactic failed"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalExtractLets___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 208, 147, 22, 140, 102, 111, 183)}};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_evalLetToHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalLetToHave"};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 67, 243, 172, 71, 255, 176, 225)}};
static const lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_64_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_65_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4__spec__0(v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4____boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_opts_68_, lean_object* v_opt_69_){
_start:
{
lean_object* v_name_70_; lean_object* v_defValue_71_; lean_object* v_map_72_; lean_object* v___x_73_; 
v_name_70_ = lean_ctor_get(v_opt_69_, 0);
v_defValue_71_ = lean_ctor_get(v_opt_69_, 1);
v_map_72_ = lean_ctor_get(v_opts_68_, 0);
v___x_73_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_72_, v_name_70_);
if (lean_obj_tag(v___x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = lean_unbox(v_defValue_71_);
return v___x_74_;
}
else
{
lean_object* v_val_75_; 
v_val_75_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v___x_73_);
if (lean_obj_tag(v_val_75_) == 1)
{
uint8_t v_v_76_; 
v_v_76_ = lean_ctor_get_uint8(v_val_75_, 0);
lean_dec_ref(v_val_75_);
return v_v_76_;
}
else
{
uint8_t v___x_77_; 
lean_dec(v_val_75_);
v___x_77_ = lean_unbox(v_defValue_71_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_78_, lean_object* v_opt_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_opts_78_, v_opt_79_);
lean_dec_ref(v_opt_79_);
lean_dec_ref(v_opts_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v_env_89_; lean_object* v___x_90_; lean_object* v_mctx_91_; lean_object* v_lctx_92_; lean_object* v_options_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_88_ = lean_st_ref_get(v___y_86_);
v_env_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_ref(v_env_89_);
lean_dec(v___x_88_);
v___x_90_ = lean_st_ref_get(v___y_84_);
v_mctx_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_mctx_91_);
lean_dec(v___x_90_);
v_lctx_92_ = lean_ctor_get(v___y_83_, 2);
v_options_93_ = lean_ctor_get(v___y_85_, 2);
lean_inc_ref(v_options_93_);
lean_inc_ref(v_lctx_92_);
v___x_94_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_94_, 0, v_env_89_);
lean_ctor_set(v___x_94_, 1, v_mctx_91_);
lean_ctor_set(v___x_94_, 2, v_lctx_92_);
lean_ctor_set(v___x_94_, 3, v_options_93_);
v___x_95_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_msgData_82_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msgData_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msgData_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(uint8_t v___y_110_, uint8_t v_suppressElabErrors_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 1)
{
lean_object* v_pre_113_; 
v_pre_113_ = lean_ctor_get(v_x_112_, 0);
switch(lean_obj_tag(v_pre_113_))
{
case 1:
{
lean_object* v_pre_114_; 
v_pre_114_ = lean_ctor_get(v_pre_113_, 0);
switch(lean_obj_tag(v_pre_114_))
{
case 0:
{
lean_object* v_str_115_; lean_object* v_str_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_str_115_ = lean_ctor_get(v_x_112_, 1);
v_str_116_ = lean_ctor_get(v_pre_113_, 1);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_118_ = lean_string_dec_eq(v_str_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_));
v___x_120_ = lean_string_dec_eq(v_str_116_, v___x_119_);
if (v___x_120_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_122_ = lean_string_dec_eq(v_str_115_, v___x_121_);
if (v___x_122_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
else
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_124_ = lean_string_dec_eq(v_str_115_, v___x_123_);
if (v___x_124_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
case 1:
{
lean_object* v_pre_125_; 
v_pre_125_ = lean_ctor_get(v_pre_114_, 0);
if (lean_obj_tag(v_pre_125_) == 0)
{
lean_object* v_str_126_; lean_object* v_str_127_; lean_object* v_str_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_str_126_ = lean_ctor_get(v_x_112_, 1);
v_str_127_ = lean_ctor_get(v_pre_113_, 1);
v_str_128_ = lean_ctor_get(v_pre_114_, 1);
v___x_129_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_130_ = lean_string_dec_eq(v_str_128_, v___x_129_);
if (v___x_130_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_132_ = lean_string_dec_eq(v_str_127_, v___x_131_);
if (v___x_132_ == 0)
{
return v___y_110_;
}
else
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_134_ = lean_string_dec_eq(v_str_126_, v___x_133_);
if (v___x_134_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
}
}
else
{
return v___y_110_;
}
}
default: 
{
return v___y_110_;
}
}
}
case 0:
{
lean_object* v_str_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_str_135_ = lean_ctor_get(v_x_112_, 1);
v___x_136_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_137_ = lean_string_dec_eq(v_str_135_, v___x_136_);
if (v___x_137_ == 0)
{
return v___y_110_;
}
else
{
return v_suppressElabErrors_111_;
}
}
default: 
{
return v___y_110_;
}
}
}
else
{
return v___y_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v___y_138_, lean_object* v_suppressElabErrors_139_, lean_object* v_x_140_){
_start:
{
uint8_t v___y_6510__boxed_141_; uint8_t v_suppressElabErrors_boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v___y_6510__boxed_141_ = lean_unbox(v___y_138_);
v_suppressElabErrors_boxed_142_ = lean_unbox(v_suppressElabErrors_139_);
v_res_143_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0(v___y_6510__boxed_141_, v_suppressElabErrors_boxed_142_, v_x_140_);
lean_dec(v_x_140_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_146_, lean_object* v_msgData_147_, uint8_t v_severity_148_, uint8_t v_isSilent_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; uint8_t v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; uint8_t v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; uint8_t v___y_198_; lean_object* v___y_199_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___y_221_; uint8_t v___y_222_; uint8_t v___y_223_; lean_object* v___y_224_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; uint8_t v___y_231_; uint8_t v___y_232_; lean_object* v___y_233_; uint8_t v___y_234_; uint8_t v___x_239_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; uint8_t v___y_244_; lean_object* v___y_245_; uint8_t v___y_246_; uint8_t v___y_247_; uint8_t v___y_249_; uint8_t v___x_264_; 
v___x_239_ = 2;
v___x_264_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_239_);
if (v___x_264_ == 0)
{
v___y_249_ = v___x_264_;
goto v___jp_248_;
}
else
{
uint8_t v___x_265_; 
lean_inc_ref(v_msgData_147_);
v___x_265_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_147_);
v___y_249_ = v___x_265_;
goto v___jp_248_;
}
v___jp_155_:
{
lean_object* v___x_165_; lean_object* v_currNamespace_166_; lean_object* v_openDecls_167_; lean_object* v_env_168_; lean_object* v_nextMacroScope_169_; lean_object* v_ngen_170_; lean_object* v_auxDeclNGen_171_; lean_object* v_traceState_172_; lean_object* v_cache_173_; lean_object* v_messages_174_; lean_object* v_infoState_175_; lean_object* v_snapshotTasks_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_190_; 
v___x_165_ = lean_st_ref_take(v___y_164_);
v_currNamespace_166_ = lean_ctor_get(v___y_163_, 6);
v_openDecls_167_ = lean_ctor_get(v___y_163_, 7);
v_env_168_ = lean_ctor_get(v___x_165_, 0);
v_nextMacroScope_169_ = lean_ctor_get(v___x_165_, 1);
v_ngen_170_ = lean_ctor_get(v___x_165_, 2);
v_auxDeclNGen_171_ = lean_ctor_get(v___x_165_, 3);
v_traceState_172_ = lean_ctor_get(v___x_165_, 4);
v_cache_173_ = lean_ctor_get(v___x_165_, 5);
v_messages_174_ = lean_ctor_get(v___x_165_, 6);
v_infoState_175_ = lean_ctor_get(v___x_165_, 7);
v_snapshotTasks_176_ = lean_ctor_get(v___x_165_, 8);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_190_ == 0)
{
v___x_178_ = v___x_165_;
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snapshotTasks_176_);
lean_inc(v_infoState_175_);
lean_inc(v_messages_174_);
lean_inc(v_cache_173_);
lean_inc(v_traceState_172_);
lean_inc(v_auxDeclNGen_171_);
lean_inc(v_ngen_170_);
lean_inc(v_nextMacroScope_169_);
lean_inc(v_env_168_);
lean_dec(v___x_165_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
lean_inc(v_openDecls_167_);
lean_inc(v_currNamespace_166_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_currNamespace_166_);
lean_ctor_set(v___x_180_, 1, v_openDecls_167_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___y_156_);
lean_inc_ref(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_182_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_182_, 0, v___y_157_);
lean_ctor_set(v___x_182_, 1, v___y_161_);
lean_ctor_set(v___x_182_, 2, v___y_160_);
lean_ctor_set(v___x_182_, 3, v___y_158_);
lean_ctor_set(v___x_182_, 4, v___x_181_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5, v___y_159_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5 + 1, v___y_162_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*5 + 2, v_isSilent_149_);
v___x_183_ = l_Lean_MessageLog_add(v___x_182_, v_messages_174_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 6, v___x_183_);
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_env_168_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_nextMacroScope_169_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_ngen_170_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v_auxDeclNGen_171_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v_traceState_172_);
lean_ctor_set(v_reuseFailAlloc_189_, 5, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_189_, 6, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_189_, 7, v_infoState_175_);
lean_ctor_set(v_reuseFailAlloc_189_, 8, v_snapshotTasks_176_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_st_ref_set(v___y_164_, v___x_185_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
v___jp_191_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_215_; 
v___x_200_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_147_);
v___x_201_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v___x_200_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_215_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_215_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
lean_inc_ref_n(v___y_193_, 2);
v___x_206_ = l_Lean_FileMap_toPosition(v___y_193_, v___y_194_);
lean_dec(v___y_194_);
v___x_207_ = l_Lean_FileMap_toPosition(v___y_193_, v___y_199_);
lean_dec(v___y_199_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___x_209_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
if (v___y_196_ == 0)
{
lean_del_object(v___x_204_);
lean_dec_ref(v___y_192_);
v___y_156_ = v_a_202_;
v___y_157_ = v___y_195_;
v___y_158_ = v___x_209_;
v___y_159_ = v___y_197_;
v___y_160_ = v___x_208_;
v___y_161_ = v___x_206_;
v___y_162_ = v___y_198_;
v___y_163_ = v___y_152_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
else
{
uint8_t v___x_210_; 
lean_inc(v_a_202_);
v___x_210_ = l_Lean_MessageData_hasTag(v___y_192_, v_a_202_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref(v___x_208_);
lean_dec_ref(v___x_206_);
lean_dec(v_a_202_);
v___x_211_ = lean_box(0);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_211_);
v___x_213_ = v___x_204_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_del_object(v___x_204_);
v___y_156_ = v_a_202_;
v___y_157_ = v___y_195_;
v___y_158_ = v___x_209_;
v___y_159_ = v___y_197_;
v___y_160_ = v___x_208_;
v___y_161_ = v___x_206_;
v___y_162_ = v___y_198_;
v___y_163_ = v___y_152_;
v___y_164_ = v___y_153_;
goto v___jp_155_;
}
}
}
}
v___jp_216_:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Syntax_getTailPos_x3f(v___y_219_, v___y_222_);
lean_dec(v___y_219_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_inc(v___y_224_);
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_224_;
v___y_195_ = v___y_220_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_222_;
v___y_198_ = v___y_223_;
v___y_199_ = v___y_224_;
goto v___jp_191_;
}
else
{
lean_object* v_val_226_; 
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec_ref(v___x_225_);
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_224_;
v___y_195_ = v___y_220_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_222_;
v___y_198_ = v___y_223_;
v___y_199_ = v_val_226_;
goto v___jp_191_;
}
}
v___jp_227_:
{
lean_object* v_ref_235_; lean_object* v___x_236_; 
v_ref_235_ = l_Lean_replaceRef(v_ref_146_, v___y_233_);
v___x_236_ = l_Lean_Syntax_getPos_x3f(v_ref_235_, v___y_232_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v_ref_235_;
v___y_220_ = v___y_230_;
v___y_221_ = v___y_231_;
v___y_222_ = v___y_232_;
v___y_223_ = v___y_234_;
v___y_224_ = v___x_237_;
goto v___jp_216_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v___x_236_);
v___y_217_ = v___y_228_;
v___y_218_ = v___y_229_;
v___y_219_ = v_ref_235_;
v___y_220_ = v___y_230_;
v___y_221_ = v___y_231_;
v___y_222_ = v___y_232_;
v___y_223_ = v___y_234_;
v___y_224_ = v_val_238_;
goto v___jp_216_;
}
}
v___jp_240_:
{
if (v___y_247_ == 0)
{
v___y_228_ = v___y_243_;
v___y_229_ = v___y_241_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_244_;
v___y_232_ = v___y_246_;
v___y_233_ = v___y_245_;
v___y_234_ = v_severity_148_;
goto v___jp_227_;
}
else
{
v___y_228_ = v___y_243_;
v___y_229_ = v___y_241_;
v___y_230_ = v___y_242_;
v___y_231_ = v___y_244_;
v___y_232_ = v___y_246_;
v___y_233_ = v___y_245_;
v___y_234_ = v___x_239_;
goto v___jp_227_;
}
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v_fileName_250_; lean_object* v_fileMap_251_; lean_object* v_options_252_; lean_object* v_ref_253_; uint8_t v_suppressElabErrors_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v_fileName_250_ = lean_ctor_get(v___y_152_, 0);
v_fileMap_251_ = lean_ctor_get(v___y_152_, 1);
v_options_252_ = lean_ctor_get(v___y_152_, 2);
v_ref_253_ = lean_ctor_get(v___y_152_, 5);
v_suppressElabErrors_254_ = lean_ctor_get_uint8(v___y_152_, sizeof(void*)*14 + 1);
v___x_255_ = lean_box(v___y_249_);
v___x_256_ = lean_box(v_suppressElabErrors_254_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_257_, 0, v___x_255_);
lean_closure_set(v___f_257_, 1, v___x_256_);
v___x_258_ = 1;
v___x_259_ = l_Lean_instBEqMessageSeverity_beq(v_severity_148_, v___x_258_);
if (v___x_259_ == 0)
{
v___y_241_ = v_fileMap_251_;
v___y_242_ = v_fileName_250_;
v___y_243_ = v___f_257_;
v___y_244_ = v_suppressElabErrors_254_;
v___y_245_ = v_ref_253_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_259_;
goto v___jp_240_;
}
else
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = l_Lean_warningAsError;
v___x_261_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_252_, v___x_260_);
v___y_241_ = v_fileMap_251_;
v___y_242_ = v_fileName_250_;
v___y_243_ = v___f_257_;
v___y_244_ = v_suppressElabErrors_254_;
v___y_245_ = v_ref_253_;
v___y_246_ = v___y_249_;
v___y_247_ = v___x_261_;
goto v___jp_240_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v_msgData_147_);
v___x_262_ = lean_box(0);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_266_, lean_object* v_msgData_267_, lean_object* v_severity_268_, lean_object* v_isSilent_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_severity_boxed_275_; uint8_t v_isSilent_boxed_276_; lean_object* v_res_277_; 
v_severity_boxed_275_ = lean_unbox(v_severity_268_);
v_isSilent_boxed_276_ = lean_unbox(v_isSilent_269_);
v_res_277_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_266_, v_msgData_267_, v_severity_boxed_275_, v_isSilent_boxed_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v_ref_266_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(lean_object* v_ref_278_, lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 1;
v___x_290_ = 0;
v___x_291_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_278_, v_msgData_279_, v___x_289_, v___x_290_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3___boxed(lean_object* v_ref_292_, lean_object* v_msgData_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_ref_292_, v_msgData_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_ref_292_);
return v_res_303_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__0));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__2));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(lean_object* v_linterOption_310_, lean_object* v_stx_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_name_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_337_; 
v_name_322_ = lean_ctor_get(v_linterOption_310_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_linterOption_310_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_linterOption_310_, 1);
lean_dec(v_unused_338_);
v___x_324_ = v_linterOption_310_;
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_name_322_);
lean_dec(v_linterOption_310_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_337_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__1);
lean_inc(v_name_322_);
v___x_327_ = l_Lean_MessageData_ofName(v_name_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_327_);
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_336_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_disable_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___closed__3);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v_disable_332_ = l_Lean_MessageData_note(v___x_331_);
v___x_333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_333_, 0, v_msg_312_);
lean_ctor_set(v___x_333_, 1, v_disable_332_);
v___x_334_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_334_, 0, v_name_322_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3(v_stx_311_, v___x_334_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1___boxed(lean_object* v_linterOption_339_, lean_object* v_stx_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_339_, v_stx_340_, v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v_stx_340_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(lean_object* v_o_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_env_356_; lean_object* v___x_357_; lean_object* v_toEnvExtension_358_; lean_object* v_asyncMode_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_linterSets_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_env_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_env_356_);
lean_dec(v___x_355_);
v___x_357_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_358_ = lean_ctor_get(v___x_357_, 0);
v_asyncMode_359_ = lean_ctor_get(v_toEnvExtension_358_, 2);
v___x_360_ = lean_box(1);
v___x_361_ = lean_box(0);
v_linterSets_362_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_360_, v___x_357_, v_env_356_, v_asyncMode_359_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_o_352_);
lean_ctor_set(v___x_363_, 1, v_linterSets_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_o_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_365_, v___y_366_);
lean_dec(v___y_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_options_378_; lean_object* v___x_379_; 
v_options_378_ = lean_ctor_get(v___y_375_, 2);
lean_inc_ref(v_options_378_);
v___x_379_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_options_378_, v___y_376_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0___boxed(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(lean_object* v_linterOption_390_, lean_object* v_stx_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
v___x_402_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0(v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_413_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
uint8_t v___x_407_; 
v___x_407_ = l_Lean_Linter_getLinterValue(v_linterOption_390_, v_a_403_);
lean_dec(v_a_403_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
lean_dec_ref(v_msg_392_);
lean_dec_ref(v_linterOption_390_);
v___x_408_ = lean_box(0);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
else
{
lean_object* v___x_412_; 
lean_del_object(v___x_405_);
v___x_412_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1(v_linterOption_390_, v_stx_391_, v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0___boxed(lean_object* v_linterOption_414_, lean_object* v_stx_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v_linterOption_414_, v_stx_415_, v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v_stx_415_);
return v_res_426_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__0));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(lean_object* v_upperBound_430_, lean_object* v_fvars_431_, lean_object* v_ids_432_, lean_object* v_a_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_a_445_; uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_lt(v_a_433_, v_upperBound_430_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
lean_dec(v_a_433_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v_b_434_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = lean_array_get_size(v_fvars_431_);
v___x_453_ = lean_nat_dec_lt(v_a_433_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = l_Lean_Elab_Tactic_linter_tactic_unusedName;
v___x_455_ = lean_array_fget_borrowed(v_ids_432_, v_a_433_);
v___x_456_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___closed__1);
v___x_457_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0(v___x_454_, v___x_455_, v___x_456_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_dec_ref(v___x_457_);
v_a_445_ = v___x_451_;
goto v___jp_444_;
}
else
{
lean_dec(v_a_433_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = lean_array_fget_borrowed(v_ids_432_, v_a_433_);
v___x_459_ = lean_array_fget_borrowed(v_fvars_431_, v_a_433_);
lean_inc(v___x_459_);
v___x_460_ = l_Lean_mkFVar(v___x_459_);
lean_inc(v___x_458_);
v___x_461_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_458_, v___x_460_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_dec_ref(v___x_461_);
v_a_445_ = v___x_451_;
goto v___jp_444_;
}
else
{
lean_dec(v_a_433_);
return v___x_461_;
}
}
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_add(v_a_433_, v___x_446_);
lean_dec(v_a_433_);
v_a_433_ = v___x_447_;
v_b_434_ = v_a_445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg___boxed(lean_object* v_upperBound_462_, lean_object* v_fvars_463_, lean_object* v_ids_464_, lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_462_, v_fvars_463_, v_ids_464_, v_a_465_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v_ids_464_);
lean_dec_ref(v_fvars_463_);
lean_dec(v_upperBound_462_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(lean_object* v___x_477_, lean_object* v_fvars_478_, lean_object* v_ids_479_, lean_object* v___x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v___x_477_, v_fvars_478_, v_ids_479_, v___x_490_, v___x_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_499_);
v___x_493_ = v___x_491_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_dec(v___x_491_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_480_);
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_480_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed(lean_object* v___x_500_, lean_object* v_fvars_501_, lean_object* v_ids_502_, lean_object* v___x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0(v___x_500_, v_fvars_501_, v_ids_502_, v___x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec_ref(v_ids_502_);
lean_dec_ref(v_fvars_501_);
lean_dec(v___x_500_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo(lean_object* v_ids_514_, lean_object* v_fvars_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; 
v___x_525_ = lean_array_get_size(v_ids_514_);
v___x_526_ = lean_box(0);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_extractLetsAddVarInfo___lam__0___boxed), 13, 4);
lean_closure_set(v___f_527_, 0, v___x_525_);
lean_closure_set(v___f_527_, 1, v_fvars_515_);
lean_closure_set(v___f_527_, 2, v_ids_514_);
lean_closure_set(v___f_527_, 3, v___x_526_);
v___x_528_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_527_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_extractLetsAddVarInfo___boxed(lean_object* v_ids_529_, lean_object* v_fvars_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_529_, v_fvars_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(lean_object* v_upperBound_541_, lean_object* v_fvars_542_, lean_object* v_ids_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___redArg(v_upperBound_541_, v_fvars_542_, v_ids_543_, v_a_546_, v_b_547_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_559_ = _args[0];
lean_object* v_fvars_560_ = _args[1];
lean_object* v_ids_561_ = _args[2];
lean_object* v_inst_562_ = _args[3];
lean_object* v_R_563_ = _args[4];
lean_object* v_a_564_ = _args[5];
lean_object* v_b_565_ = _args[6];
lean_object* v_c_566_ = _args[7];
lean_object* v___y_567_ = _args[8];
lean_object* v___y_568_ = _args[9];
lean_object* v___y_569_ = _args[10];
lean_object* v___y_570_ = _args[11];
lean_object* v___y_571_ = _args[12];
lean_object* v___y_572_ = _args[13];
lean_object* v___y_573_ = _args[14];
lean_object* v___y_574_ = _args[15];
lean_object* v___y_575_ = _args[16];
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__1(v_upperBound_559_, v_fvars_560_, v_ids_561_, v_inst_562_, v_R_563_, v_a_564_, v_b_565_, v_c_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_ids_561_);
lean_dec_ref(v_fvars_560_);
lean_dec(v_upperBound_559_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(lean_object* v_o_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___redArg(v_o_577_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1___boxed(lean_object* v_o_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__0_spec__1(v_o_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(lean_object* v_ref_599_, lean_object* v_msgData_600_, uint8_t v_severity_601_, uint8_t v_isSilent_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_599_, v_msgData_600_, v_severity_601_, v_isSilent_602_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_613_, lean_object* v_msgData_614_, lean_object* v_severity_615_, lean_object* v_isSilent_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v_severity_boxed_626_; uint8_t v_isSilent_boxed_627_; lean_object* v_res_628_; 
v_severity_boxed_626_ = lean_unbox(v_severity_615_);
v_isSilent_boxed_627_ = lean_unbox(v_isSilent_616_);
v_res_628_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5(v_ref_613_, v_msgData_614_, v_severity_boxed_626_, v_isSilent_boxed_627_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v_ref_613_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object* v_e_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_642_ = 0;
v___x_643_ = 1;
v___x_644_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_641_, v_e_635_, v___x_642_, v___x_643_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object* v_e_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_652_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3____boxed(lean_object* v_e_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v_e_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
return v_res_669_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_box(1);
v___x_671_ = l_Lean_MessageData_ofFormat(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__2));
v___x_676_ = l_Lean_MessageData_ofFormat(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
return v_x_677_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_702_; 
v_head_679_ = lean_ctor_get(v_x_678_, 0);
v_tail_680_ = lean_ctor_get(v_x_678_, 1);
v_isSharedCheck_702_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_702_ == 0)
{
v___x_682_ = v_x_678_;
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_702_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_before_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_700_; 
v_before_684_ = lean_ctor_get(v_head_679_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v_head_679_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v_head_679_, 1);
lean_dec(v_unused_701_);
v___x_686_ = v_head_679_;
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_before_684_);
lean_dec(v_head_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_700_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 7);
lean_ctor_set(v___x_686_, 1, v___x_688_);
lean_ctor_set(v___x_686_, 0, v_x_677_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_x_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_699_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 7);
lean_ctor_set(v___x_682_, 1, v___x_691_);
lean_ctor_set(v___x_682_, 0, v___x_690_);
v___x_693_ = v___x_682_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_698_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_MessageData_ofSyntax(v_before_684_);
v___x_695_ = l_Lean_indentD(v___x_694_);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_693_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v_x_677_ = v___x_696_;
v_x_678_ = v_tail_680_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__1));
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(lean_object* v_msgData_708_, lean_object* v_macroStack_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_options_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v_options_712_ = lean_ctor_get(v___y_710_, 2);
v___x_713_ = l_Lean_Elab_pp_macroStack;
v___x_714_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__7(v_options_712_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec(v_macroStack_709_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_msgData_708_);
return v___x_715_;
}
else
{
if (lean_obj_tag(v_macroStack_709_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msgData_708_);
return v___x_716_;
}
else
{
lean_object* v_head_717_; lean_object* v_after_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_733_; 
v_head_717_ = lean_ctor_get(v_macroStack_709_, 0);
lean_inc(v_head_717_);
v_after_718_ = lean_ctor_get(v_head_717_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_head_717_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_head_717_, 0);
lean_dec(v_unused_734_);
v___x_720_ = v_head_717_;
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_after_718_);
lean_dec(v_head_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_733_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 7);
lean_ctor_set(v___x_720_, 1, v___x_722_);
lean_ctor_set(v___x_720_, 0, v_msgData_708_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_msgData_708_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_722_);
v___x_724_ = v_reuseFailAlloc_732_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v_msgData_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___closed__2);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_MessageData_ofSyntax(v_after_718_);
v___x_728_ = l_Lean_indentD(v___x_727_);
v_msgData_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_729_, 0, v___x_726_);
lean_ctor_set(v_msgData_729_, 1, v___x_728_);
v___x_730_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4_spec__8(v_msgData_729_, v_macroStack_709_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_735_, lean_object* v_macroStack_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_msgData_735_, v_macroStack_736_, v___y_737_);
lean_dec_ref(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v_macroStack_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_ref_748_ = lean_ctor_get(v___y_745_, 5);
v___x_749_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_740_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref(v___x_749_);
v_macroStack_751_ = lean_ctor_get(v___y_741_, 1);
lean_inc_n(v_macroStack_751_, 2);
v___x_752_ = l_Lean_Elab_getBetterRef(v_ref_748_, v_macroStack_751_);
v___x_753_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_a_750_, v_macroStack_751_, v___y_745_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_752_);
lean_ctor_set(v___x_758_, 1, v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg___boxed(lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_771_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_772_; double v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_float_of_nat(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_ref_783_; lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_829_; 
v_ref_783_ = lean_ctor_get(v___y_780_, 5);
v___x_784_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_829_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_829_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_829_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_traceState_790_; lean_object* v_env_791_; lean_object* v_nextMacroScope_792_; lean_object* v_ngen_793_; lean_object* v_auxDeclNGen_794_; lean_object* v_cache_795_; lean_object* v_messages_796_; lean_object* v_infoState_797_; lean_object* v_snapshotTasks_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_828_; 
v___x_789_ = lean_st_ref_take(v___y_781_);
v_traceState_790_ = lean_ctor_get(v___x_789_, 4);
v_env_791_ = lean_ctor_get(v___x_789_, 0);
v_nextMacroScope_792_ = lean_ctor_get(v___x_789_, 1);
v_ngen_793_ = lean_ctor_get(v___x_789_, 2);
v_auxDeclNGen_794_ = lean_ctor_get(v___x_789_, 3);
v_cache_795_ = lean_ctor_get(v___x_789_, 5);
v_messages_796_ = lean_ctor_get(v___x_789_, 6);
v_infoState_797_ = lean_ctor_get(v___x_789_, 7);
v_snapshotTasks_798_ = lean_ctor_get(v___x_789_, 8);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_828_ == 0)
{
v___x_800_ = v___x_789_;
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snapshotTasks_798_);
lean_inc(v_infoState_797_);
lean_inc(v_messages_796_);
lean_inc(v_cache_795_);
lean_inc(v_traceState_790_);
lean_inc(v_auxDeclNGen_794_);
lean_inc(v_ngen_793_);
lean_inc(v_nextMacroScope_792_);
lean_inc(v_env_791_);
lean_dec(v___x_789_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint64_t v_tid_802_; lean_object* v_traces_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_827_; 
v_tid_802_ = lean_ctor_get_uint64(v_traceState_790_, sizeof(void*)*1);
v_traces_803_ = lean_ctor_get(v_traceState_790_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v_traceState_790_);
if (v_isSharedCheck_827_ == 0)
{
v___x_805_ = v_traceState_790_;
v_isShared_806_ = v_isSharedCheck_827_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_traces_803_);
lean_dec(v_traceState_790_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_827_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; double v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_807_ = lean_box(0);
v___x_808_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_809_ = 0;
v___x_810_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
v___x_811_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_811_, 0, v_cls_776_);
lean_ctor_set(v___x_811_, 1, v___x_807_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
lean_ctor_set_float(v___x_811_, sizeof(void*)*3, v___x_808_);
lean_ctor_set_float(v___x_811_, sizeof(void*)*3 + 8, v___x_808_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*3 + 16, v___x_809_);
v___x_812_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_813_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v_a_785_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
lean_inc(v_ref_783_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_ref_783_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_PersistentArray_push___redArg(v_traces_803_, v___x_814_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_815_);
lean_ctor_set_uint64(v_reuseFailAlloc_826_, sizeof(void*)*1, v_tid_802_);
v___x_817_ = v_reuseFailAlloc_826_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v___x_817_);
v___x_819_ = v___x_800_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_env_791_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_nextMacroScope_792_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_ngen_793_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_auxDeclNGen_794_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v_cache_795_);
lean_ctor_set(v_reuseFailAlloc_825_, 6, v_messages_796_);
lean_ctor_set(v_reuseFailAlloc_825_, 7, v_infoState_797_);
lean_ctor_set(v_reuseFailAlloc_825_, 8, v_snapshotTasks_798_);
v___x_819_ = v_reuseFailAlloc_825_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_820_ = lean_st_ref_set(v___y_781_, v___x_819_);
v___x_821_ = lean_box(0);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_821_);
v___x_823_ = v___x_787_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_830_, v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_838_, lean_object* v_i_839_, lean_object* v_k_840_){
_start:
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_array_get_size(v_keys_838_);
v___x_842_ = lean_nat_dec_lt(v_i_839_, v___x_841_);
if (v___x_842_ == 0)
{
lean_dec(v_i_839_);
return v___x_842_;
}
else
{
lean_object* v_k_x27_843_; uint8_t v___x_844_; 
v_k_x27_843_ = lean_array_fget_borrowed(v_keys_838_, v_i_839_);
v___x_844_ = l_Lean_instBEqExtraModUse_beq(v_k_840_, v_k_x27_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_add(v_i_839_, v___x_845_);
lean_dec(v_i_839_);
v_i_839_ = v___x_846_;
goto _start;
}
else
{
lean_dec(v_i_839_);
return v___x_844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_848_, lean_object* v_i_849_, lean_object* v_k_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_848_, v_i_849_, v_k_850_);
lean_dec_ref(v_k_850_);
lean_dec_ref(v_keys_848_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; 
v___x_853_ = ((size_t)5ULL);
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_shift_left(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; 
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_858_ = lean_usize_sub(v___x_857_, v___x_856_);
return v___x_858_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_859_, size_t v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_es_862_; lean_object* v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v_j_867_; lean_object* v___x_868_; 
v_es_862_ = lean_ctor_get(v_x_859_, 0);
v___x_863_ = lean_box(2);
v___x_864_ = ((size_t)5ULL);
v___x_865_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_866_ = lean_usize_land(v_x_860_, v___x_865_);
v_j_867_ = lean_usize_to_nat(v___x_866_);
v___x_868_ = lean_array_get_borrowed(v___x_863_, v_es_862_, v_j_867_);
lean_dec(v_j_867_);
switch(lean_obj_tag(v___x_868_))
{
case 0:
{
lean_object* v_key_869_; uint8_t v___x_870_; 
v_key_869_ = lean_ctor_get(v___x_868_, 0);
v___x_870_ = l_Lean_instBEqExtraModUse_beq(v_x_861_, v_key_869_);
return v___x_870_;
}
case 1:
{
lean_object* v_node_871_; size_t v___x_872_; 
v_node_871_ = lean_ctor_get(v___x_868_, 0);
v___x_872_ = lean_usize_shift_right(v_x_860_, v___x_864_);
v_x_859_ = v_node_871_;
v_x_860_ = v___x_872_;
goto _start;
}
default: 
{
uint8_t v___x_874_; 
v___x_874_ = 0;
return v___x_874_;
}
}
}
else
{
lean_object* v_ks_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_ks_875_ = lean_ctor_get(v_x_859_, 0);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_875_, v___x_876_, v_x_861_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
size_t v_x_11961__boxed_881_; uint8_t v_res_882_; lean_object* v_r_883_; 
v_x_11961__boxed_881_ = lean_unbox_usize(v_x_879_);
lean_dec(v_x_879_);
v_res_882_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_878_, v_x_11961__boxed_881_, v_x_880_);
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_878_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_884_, lean_object* v_x_885_){
_start:
{
uint64_t v___x_886_; size_t v___x_887_; uint8_t v___x_888_; 
v___x_886_ = l_Lean_instHashableExtraModUse_hash(v_x_885_);
v___x_887_ = lean_uint64_to_usize(v___x_886_);
v___x_888_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_884_, v___x_887_, v_x_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
uint8_t v_res_891_; lean_object* v_r_892_; 
v_res_891_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v_x_889_, v_x_890_);
lean_dec_ref(v_x_890_);
lean_dec_ref(v_x_889_);
v_r_892_ = lean_box(v_res_891_);
return v_r_892_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__1));
v___x_896_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__0));
v___x_897_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__3);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__4);
v___x_904_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
lean_ctor_set(v___x_904_, 2, v___x_903_);
lean_ctor_set(v___x_904_, 3, v___x_903_);
lean_ctor_set(v___x_904_, 4, v___x_903_);
lean_ctor_set(v___x_904_, 5, v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__9));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__11));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5___redArg___closed__0));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v_cls_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_cls_918_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8));
v___x_919_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__14));
v___x_920_ = l_Lean_Name_append(v___x_919_, v_cls_918_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__16));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__18));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(lean_object* v_mod_931_, uint8_t v_isMeta_932_, lean_object* v_hint_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_env_942_; uint8_t v_isExporting_943_; lean_object* v___x_944_; lean_object* v_env_945_; lean_object* v___x_946_; lean_object* v_entry_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_941_ = lean_st_ref_get(v___y_939_);
v_env_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc_ref(v_env_942_);
lean_dec(v___x_941_);
v_isExporting_943_ = lean_ctor_get_uint8(v_env_942_, sizeof(void*)*8);
lean_dec_ref(v_env_942_);
v___x_944_ = lean_st_ref_get(v___y_939_);
v_env_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc_ref(v_env_945_);
lean_dec(v___x_944_);
v___x_946_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_931_);
v_entry_947_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_947_, 0, v_mod_931_);
lean_ctor_set_uint8(v_entry_947_, sizeof(void*)*1, v_isExporting_943_);
lean_ctor_set_uint8(v_entry_947_, sizeof(void*)*1 + 1, v_isMeta_932_);
v___x_948_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_949_ = lean_box(1);
v___x_950_ = lean_box(0);
v___x_993_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_946_, v___x_948_, v_env_945_, v___x_949_, v___x_950_);
v___x_994_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v___x_993_, v_entry_947_);
lean_dec(v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v_options_995_; uint8_t v_hasTrace_996_; 
v_options_995_ = lean_ctor_get(v___y_938_, 2);
v_hasTrace_996_ = lean_ctor_get_uint8(v_options_995_, sizeof(void*)*1);
if (v_hasTrace_996_ == 0)
{
lean_dec(v_hint_933_);
lean_dec(v_mod_931_);
v___y_952_ = v___y_937_;
v___y_953_ = v___y_939_;
goto v___jp_951_;
}
else
{
lean_object* v_inheritedTraceOptions_997_; lean_object* v_cls_998_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_inheritedTraceOptions_997_ = lean_ctor_get(v___y_938_, 13);
v_cls_998_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__8));
v___x_1018_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__15);
v___x_1019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_997_, v_options_995_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec(v_hint_933_);
lean_dec(v_mod_931_);
v___y_952_ = v___y_937_;
v___y_953_ = v___y_939_;
goto v___jp_951_;
}
else
{
lean_object* v___x_1020_; lean_object* v___y_1022_; 
v___x_1020_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__17);
if (v_isExporting_943_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__22));
v___y_1022_ = v___x_1029_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__23));
v___y_1022_ = v___x_1030_;
goto v___jp_1021_;
}
v___jp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_inc_ref(v___y_1022_);
v___x_1023_ = l_Lean_stringToMessageData(v___y_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__19);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
if (v_isMeta_932_ == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__20));
v___y_1005_ = v___x_1026_;
v___y_1006_ = v___x_1027_;
goto v___jp_1004_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__21));
v___y_1005_ = v___x_1026_;
v___y_1006_ = v___x_1028_;
goto v___jp_1004_;
}
}
}
v___jp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_1000_);
lean_ctor_set(v___x_1002_, 1, v___y_1001_);
v___x_1003_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_998_, v___x_1002_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_dec_ref(v___x_1003_);
v___y_952_ = v___y_937_;
v___y_953_ = v___y_939_;
goto v___jp_951_;
}
else
{
lean_dec_ref(v_entry_947_);
return v___x_1003_;
}
}
v___jp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
lean_inc_ref(v___y_1006_);
v___x_1007_ = l_Lean_stringToMessageData(v___y_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___y_1005_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__10);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_MessageData_ofName(v_mod_931_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Name_isAnonymous(v_hint_933_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__12);
v___x_1015_ = l_Lean_MessageData_ofName(v_hint_933_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___y_1000_ = v___x_1012_;
v___y_1001_ = v___x_1016_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1017_; 
lean_dec(v_hint_933_);
v___x_1017_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__13);
v___y_1000_ = v___x_1012_;
v___y_1001_ = v___x_1017_;
goto v___jp_999_;
}
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_entry_947_);
lean_dec(v_hint_933_);
lean_dec(v_mod_931_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
v___jp_951_:
{
lean_object* v___x_954_; lean_object* v_toEnvExtension_955_; lean_object* v_env_956_; lean_object* v_nextMacroScope_957_; lean_object* v_ngen_958_; lean_object* v_auxDeclNGen_959_; lean_object* v_traceState_960_; lean_object* v_messages_961_; lean_object* v_infoState_962_; lean_object* v_snapshotTasks_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_991_; 
v___x_954_ = lean_st_ref_take(v___y_953_);
v_toEnvExtension_955_ = lean_ctor_get(v___x_948_, 0);
v_env_956_ = lean_ctor_get(v___x_954_, 0);
v_nextMacroScope_957_ = lean_ctor_get(v___x_954_, 1);
v_ngen_958_ = lean_ctor_get(v___x_954_, 2);
v_auxDeclNGen_959_ = lean_ctor_get(v___x_954_, 3);
v_traceState_960_ = lean_ctor_get(v___x_954_, 4);
v_messages_961_ = lean_ctor_get(v___x_954_, 6);
v_infoState_962_ = lean_ctor_get(v___x_954_, 7);
v_snapshotTasks_963_ = lean_ctor_get(v___x_954_, 8);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v___x_954_, 5);
lean_dec(v_unused_992_);
v___x_965_ = v___x_954_;
v_isShared_966_ = v_isSharedCheck_991_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_snapshotTasks_963_);
lean_inc(v_infoState_962_);
lean_inc(v_messages_961_);
lean_inc(v_traceState_960_);
lean_inc(v_auxDeclNGen_959_);
lean_inc(v_ngen_958_);
lean_inc(v_nextMacroScope_957_);
lean_inc(v_env_956_);
lean_dec(v___x_954_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_991_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_asyncMode_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v_asyncMode_967_ = lean_ctor_get(v_toEnvExtension_955_, 2);
v___x_968_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_948_, v_env_956_, v_entry_947_, v_asyncMode_967_, v___x_950_);
v___x_969_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__5);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 5, v___x_969_);
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_971_ = v___x_965_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_nextMacroScope_957_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_ngen_958_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_auxDeclNGen_959_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_traceState_960_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v_messages_961_);
lean_ctor_set(v_reuseFailAlloc_990_, 7, v_infoState_962_);
lean_ctor_set(v_reuseFailAlloc_990_, 8, v_snapshotTasks_963_);
v___x_971_ = v_reuseFailAlloc_990_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_mctx_974_; lean_object* v_zetaDeltaFVarIds_975_; lean_object* v_postponed_976_; lean_object* v_diag_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_988_; 
v___x_972_ = lean_st_ref_set(v___y_953_, v___x_971_);
v___x_973_ = lean_st_ref_take(v___y_952_);
v_mctx_974_ = lean_ctor_get(v___x_973_, 0);
v_zetaDeltaFVarIds_975_ = lean_ctor_get(v___x_973_, 2);
v_postponed_976_ = lean_ctor_get(v___x_973_, 3);
v_diag_977_ = lean_ctor_get(v___x_973_, 4);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_973_, 1);
lean_dec(v_unused_989_);
v___x_979_ = v___x_973_;
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_diag_977_);
lean_inc(v_postponed_976_);
lean_inc(v_zetaDeltaFVarIds_975_);
lean_inc(v_mctx_974_);
lean_dec(v___x_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___closed__6);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v___x_981_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_mctx_974_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_zetaDeltaFVarIds_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_postponed_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_diag_977_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_st_ref_set(v___y_952_, v___x_983_);
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0___boxed(lean_object* v_mod_1033_, lean_object* v_isMeta_1034_, lean_object* v_hint_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
uint8_t v_isMeta_boxed_1043_; lean_object* v_res_1044_; 
v_isMeta_boxed_1043_ = lean_unbox(v_isMeta_1034_);
v_res_1044_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_mod_1033_, v_isMeta_boxed_1043_, v_hint_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_1045_, lean_object* v_x_1046_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_box(0);
return v___x_1047_;
}
else
{
lean_object* v_key_1048_; lean_object* v_value_1049_; lean_object* v_tail_1050_; uint8_t v___x_1051_; 
v_key_1048_ = lean_ctor_get(v_x_1046_, 0);
v_value_1049_ = lean_ctor_get(v_x_1046_, 1);
v_tail_1050_ = lean_ctor_get(v_x_1046_, 2);
v___x_1051_ = lean_name_eq(v_key_1048_, v_a_1045_);
if (v___x_1051_ == 0)
{
v_x_1046_ = v_tail_1050_;
goto _start;
}
else
{
lean_object* v___x_1053_; 
lean_inc(v_value_1049_);
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_value_1049_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg(v_a_1054_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec(v_a_1054_);
return v_res_1056_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1057_; uint64_t v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1723u);
v___x_1058_ = lean_uint64_of_nat(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(lean_object* v_m_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_buckets_1061_; lean_object* v___x_1062_; uint64_t v___y_1064_; 
v_buckets_1061_ = lean_ctor_get(v_m_1059_, 1);
v___x_1062_ = lean_array_get_size(v_buckets_1061_);
if (lean_obj_tag(v_a_1060_) == 0)
{
uint64_t v___x_1078_; 
v___x_1078_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___closed__0);
v___y_1064_ = v___x_1078_;
goto v___jp_1063_;
}
else
{
uint64_t v_hash_1079_; 
v_hash_1079_ = lean_ctor_get_uint64(v_a_1060_, sizeof(void*)*2);
v___y_1064_ = v_hash_1079_;
goto v___jp_1063_;
}
v___jp_1063_:
{
uint64_t v___x_1065_; uint64_t v___x_1066_; uint64_t v_fold_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1065_ = 32ULL;
v___x_1066_ = lean_uint64_shift_right(v___y_1064_, v___x_1065_);
v_fold_1067_ = lean_uint64_xor(v___y_1064_, v___x_1066_);
v___x_1068_ = 16ULL;
v___x_1069_ = lean_uint64_shift_right(v_fold_1067_, v___x_1068_);
v___x_1070_ = lean_uint64_xor(v_fold_1067_, v___x_1069_);
v___x_1071_ = lean_uint64_to_usize(v___x_1070_);
v___x_1072_ = lean_usize_of_nat(v___x_1062_);
v___x_1073_ = ((size_t)1ULL);
v___x_1074_ = lean_usize_sub(v___x_1072_, v___x_1073_);
v___x_1075_ = lean_usize_land(v___x_1071_, v___x_1074_);
v___x_1076_ = lean_array_uget_borrowed(v_buckets_1061_, v___x_1075_);
v___x_1077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg(v_a_1060_, v___x_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v_m_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_m_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(lean_object* v___x_1083_, lean_object* v_declName_1084_, lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_usize_dec_lt(v_i_1087_, v_sz_1086_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v_declName_1084_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_b_1088_);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v_modules_1099_; lean_object* v___x_1100_; lean_object* v_a_1101_; lean_object* v___x_1102_; lean_object* v_toImport_1103_; lean_object* v_module_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; 
v___x_1098_ = l_Lean_Environment_header(v___x_1083_);
v_modules_1099_ = lean_ctor_get(v___x_1098_, 3);
lean_inc_ref(v_modules_1099_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1101_ = lean_array_uget_borrowed(v_as_1085_, v_i_1087_);
v___x_1102_ = lean_array_get(v___x_1100_, v_modules_1099_, v_a_1101_);
lean_dec_ref(v_modules_1099_);
v_toImport_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_toImport_1103_);
lean_dec(v___x_1102_);
v_module_1104_ = lean_ctor_get(v_toImport_1103_, 0);
lean_inc(v_module_1104_);
lean_dec_ref(v_toImport_1103_);
v___x_1105_ = 0;
lean_inc(v_declName_1084_);
v___x_1106_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_module_1104_, v___x_1105_, v_declName_1084_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; 
lean_dec_ref(v___x_1106_);
v___x_1107_ = lean_box(0);
v___x_1108_ = ((size_t)1ULL);
v___x_1109_ = lean_usize_add(v_i_1087_, v___x_1108_);
v_i_1087_ = v___x_1109_;
v_b_1088_ = v___x_1107_;
goto _start;
}
else
{
lean_dec(v_declName_1084_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1___boxed(lean_object* v___x_1111_, lean_object* v_declName_1112_, lean_object* v_as_1113_, lean_object* v_sz_1114_, lean_object* v_i_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1114_);
lean_dec(v_sz_1114_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1115_);
lean_dec(v_i_1115_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(v___x_1111_, v_declName_1112_, v_as_1113_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec_ref(v_as_1113_);
lean_dec_ref(v___x_1111_);
return v_res_1126_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__1));
v___x_1130_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__0));
v___x_1131_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(lean_object* v_declName_1134_, uint8_t v_isMeta_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; lean_object* v_env_1147_; lean_object* v___y_1149_; lean_object* v___x_1162_; 
v___x_1143_ = lean_st_ref_get(v___y_1141_);
v_env_1147_ = lean_ctor_get(v___x_1143_, 0);
lean_inc_ref(v_env_1147_);
lean_dec(v___x_1143_);
v___x_1162_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1147_, v_declName_1134_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1134_);
goto v___jp_1144_;
}
else
{
lean_object* v_val_1163_; lean_object* v___x_1164_; lean_object* v_modules_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l_Lean_Environment_header(v_env_1147_);
v_modules_1165_ = lean_ctor_get(v___x_1164_, 3);
lean_inc_ref(v_modules_1165_);
lean_dec_ref(v___x_1164_);
v___x_1166_ = lean_array_get_size(v_modules_1165_);
v___x_1167_ = lean_nat_dec_lt(v_val_1163_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v_modules_1165_);
lean_dec(v_val_1163_);
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1134_);
goto v___jp_1144_;
}
else
{
lean_object* v___x_1168_; lean_object* v_env_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___y_1173_; 
v___x_1168_ = lean_st_ref_get(v___y_1141_);
v_env_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_env_1169_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__2);
v___x_1171_ = lean_array_fget(v_modules_1165_, v_val_1163_);
lean_dec(v_val_1163_);
lean_dec_ref(v_modules_1165_);
if (v_isMeta_1135_ == 0)
{
lean_dec_ref(v_env_1169_);
v___y_1173_ = v_isMeta_1135_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1184_; 
lean_inc(v_declName_1134_);
v___x_1184_ = l_Lean_isMarkedMeta(v_env_1169_, v_declName_1134_);
if (v___x_1184_ == 0)
{
v___y_1173_ = v_isMeta_1135_;
goto v___jp_1172_;
}
else
{
uint8_t v___x_1185_; 
v___x_1185_ = 0;
v___y_1173_ = v___x_1185_;
goto v___jp_1172_;
}
}
v___jp_1172_:
{
lean_object* v_toImport_1174_; lean_object* v_module_1175_; lean_object* v___x_1176_; 
v_toImport_1174_ = lean_ctor_get(v___x_1171_, 0);
lean_inc_ref(v_toImport_1174_);
lean_dec(v___x_1171_);
v_module_1175_ = lean_ctor_get(v_toImport_1174_, 0);
lean_inc(v_module_1175_);
lean_dec_ref(v_toImport_1174_);
lean_inc(v_declName_1134_);
v___x_1176_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0(v_module_1175_, v___y_1173_, v_declName_1134_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec_ref(v___x_1176_);
v___x_1177_ = l_Lean_indirectModUseExt;
v___x_1178_ = lean_box(1);
v___x_1179_ = lean_box(0);
lean_inc_ref(v_env_1147_);
v___x_1180_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1170_, v___x_1177_, v_env_1147_, v___x_1178_, v___x_1179_);
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v___x_1180_, v_declName_1134_);
lean_dec(v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___closed__3));
v___y_1149_ = v___x_1182_;
goto v___jp_1148_;
}
else
{
lean_object* v_val_1183_; 
v_val_1183_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_val_1183_);
lean_dec_ref(v___x_1181_);
v___y_1149_ = v_val_1183_;
goto v___jp_1148_;
}
}
else
{
lean_dec_ref(v_env_1147_);
lean_dec(v_declName_1134_);
return v___x_1176_;
}
}
}
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
v___jp_1148_:
{
lean_object* v___x_1150_; size_t v_sz_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_box(0);
v_sz_1151_ = lean_array_size(v___y_1149_);
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__1(v_env_1147_, v_declName_1134_, v___y_1149_, v_sz_1151_, v___x_1152_, v___x_1150_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_env_1147_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1153_, 0);
lean_dec(v_unused_1161_);
v___x_1155_ = v___x_1153_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v___x_1153_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1150_);
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1150_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0___boxed(lean_object* v_declName_1186_, lean_object* v_isMeta_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_isMeta_boxed_1195_; lean_object* v_res_1196_; 
v_isMeta_boxed_1195_ = lean_unbox(v_isMeta_1187_);
v_res_1196_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v_declName_1186_, v_isMeta_boxed_1195_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1196_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__0));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__2));
v___x_1202_ = l_Lean_stringToMessageData(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__4));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__6));
v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1210_ = l_Lean_MessageData_ofName(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__8);
v___x_1212_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7);
v___x_1213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(lean_object* v_optConfig_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v_recover_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; uint8_t v___x_1264_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; 
v_recover_1258_ = lean_ctor_get_uint8(v_a_1218_, sizeof(void*)*1);
lean_inc(v_optConfig_1217_);
v___x_1259_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_1217_);
v___x_1260_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_1259_);
v___x_1261_ = lean_array_get_size(v___x_1260_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_nat_dec_eq(v___x_1261_, v___x_1262_);
v___x_1264_ = 1;
if (v___x_1263_ == 0)
{
lean_object* v___x_1312_; lean_object* v_fileName_1313_; lean_object* v_fileMap_1314_; lean_object* v_options_1315_; lean_object* v_currRecDepth_1316_; lean_object* v_maxRecDepth_1317_; lean_object* v_ref_1318_; lean_object* v_currNamespace_1319_; lean_object* v_openDecls_1320_; lean_object* v_initHeartbeats_1321_; lean_object* v_maxHeartbeats_1322_; lean_object* v_quotContext_1323_; lean_object* v_currMacroScope_1324_; uint8_t v_diag_1325_; lean_object* v_cancelTk_x3f_1326_; uint8_t v_suppressElabErrors_1327_; lean_object* v_inheritedTraceOptions_1328_; lean_object* v_env_1329_; lean_object* v_ref_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1312_ = lean_st_ref_get(v_a_1224_);
v_fileName_1313_ = lean_ctor_get(v_a_1223_, 0);
v_fileMap_1314_ = lean_ctor_get(v_a_1223_, 1);
v_options_1315_ = lean_ctor_get(v_a_1223_, 2);
v_currRecDepth_1316_ = lean_ctor_get(v_a_1223_, 3);
v_maxRecDepth_1317_ = lean_ctor_get(v_a_1223_, 4);
v_ref_1318_ = lean_ctor_get(v_a_1223_, 5);
v_currNamespace_1319_ = lean_ctor_get(v_a_1223_, 6);
v_openDecls_1320_ = lean_ctor_get(v_a_1223_, 7);
v_initHeartbeats_1321_ = lean_ctor_get(v_a_1223_, 8);
v_maxHeartbeats_1322_ = lean_ctor_get(v_a_1223_, 9);
v_quotContext_1323_ = lean_ctor_get(v_a_1223_, 10);
v_currMacroScope_1324_ = lean_ctor_get(v_a_1223_, 11);
v_diag_1325_ = lean_ctor_get_uint8(v_a_1223_, sizeof(void*)*14);
v_cancelTk_x3f_1326_ = lean_ctor_get(v_a_1223_, 12);
v_suppressElabErrors_1327_ = lean_ctor_get_uint8(v_a_1223_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1328_ = lean_ctor_get(v_a_1223_, 13);
v_env_1329_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1329_);
lean_dec(v___x_1312_);
v_ref_1330_ = l_Lean_replaceRef(v_optConfig_1217_, v_ref_1318_);
lean_dec(v_optConfig_1217_);
lean_inc_ref(v_inheritedTraceOptions_1328_);
lean_inc(v_cancelTk_x3f_1326_);
lean_inc(v_currMacroScope_1324_);
lean_inc(v_quotContext_1323_);
lean_inc(v_maxHeartbeats_1322_);
lean_inc(v_initHeartbeats_1321_);
lean_inc(v_openDecls_1320_);
lean_inc(v_currNamespace_1319_);
lean_inc(v_maxRecDepth_1317_);
lean_inc(v_currRecDepth_1316_);
lean_inc_ref(v_options_1315_);
lean_inc_ref(v_fileMap_1314_);
lean_inc_ref(v_fileName_1313_);
v___x_1331_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1331_, 0, v_fileName_1313_);
lean_ctor_set(v___x_1331_, 1, v_fileMap_1314_);
lean_ctor_set(v___x_1331_, 2, v_options_1315_);
lean_ctor_set(v___x_1331_, 3, v_currRecDepth_1316_);
lean_ctor_set(v___x_1331_, 4, v_maxRecDepth_1317_);
lean_ctor_set(v___x_1331_, 5, v_ref_1330_);
lean_ctor_set(v___x_1331_, 6, v_currNamespace_1319_);
lean_ctor_set(v___x_1331_, 7, v_openDecls_1320_);
lean_ctor_set(v___x_1331_, 8, v_initHeartbeats_1321_);
lean_ctor_set(v___x_1331_, 9, v_maxHeartbeats_1322_);
lean_ctor_set(v___x_1331_, 10, v_quotContext_1323_);
lean_ctor_set(v___x_1331_, 11, v_currMacroScope_1324_);
lean_ctor_set(v___x_1331_, 12, v_cancelTk_x3f_1326_);
lean_ctor_set(v___x_1331_, 13, v_inheritedTraceOptions_1328_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*14, v_diag_1325_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*14 + 1, v_suppressElabErrors_1327_);
v___x_1332_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1333_ = l_Lean_Environment_contains(v_env_1329_, v___x_1332_, v___x_1264_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v___x_1260_);
v___x_1334_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__9);
v___x_1335_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1334_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v___x_1331_, v_a_1224_);
lean_dec_ref(v___x_1331_);
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1335_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1335_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
v___y_1266_ = v_a_1219_;
v___y_1267_ = v_a_1220_;
v___y_1268_ = v_a_1221_;
v___y_1269_ = v_a_1222_;
v___y_1270_ = v___x_1331_;
v___y_1271_ = v_a_1224_;
goto v___jp_1265_;
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref(v___x_1260_);
lean_dec(v_optConfig_1217_);
v___x_1344_ = ((lean_object*)(l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__10));
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
v___jp_1226_:
{
if (v___y_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v___y_1228_);
v___x_1237_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1);
v___x_1238_ = l_Lean_MessageData_ofExpr(v___y_1227_);
v___x_1239_ = l_Lean_indentD(v___x_1238_);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3);
v___x_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_Exception_toMessageData(v___y_1232_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1244_, v___y_1235_, v___y_1234_, v___y_1231_, v___y_1230_, v___y_1229_, v___y_1233_);
lean_dec_ref(v___y_1229_);
return v___x_1245_;
}
else
{
lean_dec_ref(v___y_1232_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v___y_1227_);
return v___y_1228_;
}
}
v___jp_1246_:
{
lean_object* v___x_1254_; 
lean_inc_ref(v___y_1247_);
v___x_1254_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_(v___y_1247_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref(v___y_1252_);
lean_dec_ref(v___y_1247_);
return v___x_1254_;
}
else
{
lean_object* v_a_1255_; uint8_t v___x_1256_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
v___x_1256_ = l_Lean_Exception_isInterrupt(v_a_1255_);
if (v___x_1256_ == 0)
{
uint8_t v___x_1257_; 
lean_inc(v_a_1255_);
v___x_1257_ = l_Lean_Exception_isRuntime(v_a_1255_);
v___y_1227_ = v___y_1247_;
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___y_1252_;
v___y_1230_ = v___y_1251_;
v___y_1231_ = v___y_1250_;
v___y_1232_ = v_a_1255_;
v___y_1233_ = v___y_1253_;
v___y_1234_ = v___y_1249_;
v___y_1235_ = v___y_1248_;
v___y_1236_ = v___x_1257_;
goto v___jp_1226_;
}
else
{
v___y_1227_ = v___y_1247_;
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___y_1252_;
v___y_1230_ = v___y_1251_;
v___y_1231_ = v___y_1250_;
v___y_1232_ = v_a_1255_;
v___y_1233_ = v___y_1253_;
v___y_1234_ = v___y_1249_;
v___y_1235_ = v___y_1248_;
v___y_1236_ = v___x_1256_;
goto v___jp_1226_;
}
}
}
v___jp_1265_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_Lets_747541921____hygCtx___hyg_3_));
v___x_1273_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v___x_1272_, v___x_1264_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v___x_1273_);
v___x_1274_ = l_Lean_Elab_Tactic_elabConfig(v_recover_1258_, v___x_1272_, v___x_1260_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1295_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1295_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1295_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_Expr_hasSyntheticSorry(v_a_1275_);
if (v___x_1279_ == 0)
{
uint8_t v___x_1280_; 
lean_del_object(v___x_1277_);
v___x_1280_ = l_Lean_Expr_hasSorry(v_a_1275_);
if (v___x_1280_ == 0)
{
v___y_1247_ = v_a_1275_;
v___y_1248_ = v___y_1266_;
v___y_1249_ = v___y_1267_;
v___y_1250_ = v___y_1268_;
v___y_1251_ = v___y_1269_;
v___y_1252_ = v___y_1270_;
v___y_1253_ = v___y_1271_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1275_);
v___x_1281_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5);
v___x_1282_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_1281_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec_ref(v___y_1270_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
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
else
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_a_1275_);
lean_dec_ref(v___y_1270_);
v___x_1291_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_1291_, 0, v___x_1263_);
lean_ctor_set_uint8(v___x_1291_, 1, v___x_1264_);
lean_ctor_set_uint8(v___x_1291_, 2, v___x_1263_);
lean_ctor_set_uint8(v___x_1291_, 3, v___x_1264_);
lean_ctor_set_uint8(v___x_1291_, 4, v___x_1264_);
lean_ctor_set_uint8(v___x_1291_, 5, v___x_1263_);
lean_ctor_set_uint8(v___x_1291_, 6, v___x_1264_);
lean_ctor_set_uint8(v___x_1291_, 7, v___x_1264_);
lean_ctor_set_uint8(v___x_1291_, 8, v___x_1263_);
lean_ctor_set_uint8(v___x_1291_, 9, v___x_1263_);
lean_ctor_set_uint8(v___x_1291_, 10, v___x_1263_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1291_);
v___x_1293_ = v___x_1277_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v___y_1270_);
v_a_1296_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1274_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1274_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___y_1270_);
lean_dec_ref(v___x_1260_);
v_a_1304_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1273_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1273_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___boxed(lean_object* v_optConfig_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_optConfig_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec_ref(v_a_1347_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig(lean_object* v_optConfig_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v_optConfig_1356_, v_a_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabExtractLetsConfig___boxed(lean_object* v_optConfig_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Elab_Tactic_elabExtractLetsConfig(v_optConfig_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(lean_object* v_00_u03b1_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v_msg_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_msg_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1(v_00_u03b1_1388_, v_msg_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(lean_object* v_00_u03b2_1398_, lean_object* v_m_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___redArg(v_m_1399_, v_a_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1402_, lean_object* v_m_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2(v_00_u03b2_1402_, v_m_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_m_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(lean_object* v_msgData_1406_, lean_object* v_macroStack_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___redArg(v_msgData_1406_, v_macroStack_1407_, v___y_1412_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4___boxed(lean_object* v_msgData_1416_, lean_object* v_macroStack_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1_spec__4(v_msgData_1416_, v_macroStack_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___redArg(v_x_1427_, v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1(v_00_u03b2_1430_, v_x_1431_, v_x_1432_);
lean_dec_ref(v_x_1432_);
lean_dec_ref(v_x_1431_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(lean_object* v_cls_1435_, lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___redArg(v_cls_1435_, v_msg_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__2(v_cls_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1455_, lean_object* v_a_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___redArg(v_a_1456_, v_x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_a_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__2_spec__5(v_00_u03b2_1459_, v_a_1460_, v_x_1461_);
lean_dec(v_x_1461_);
lean_dec(v_a_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1463_, lean_object* v_x_1464_, size_t v_x_1465_, lean_object* v_x_1466_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1464_, v_x_1465_, v_x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
size_t v_x_12935__boxed_1472_; uint8_t v_res_1473_; lean_object* v_r_1474_; 
v_x_12935__boxed_1472_ = lean_unbox_usize(v_x_1470_);
lean_dec(v_x_1470_);
v_res_1473_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1468_, v_x_1469_, v_x_12935__boxed_1472_, v_x_1471_);
lean_dec_ref(v_x_1471_);
lean_dec_ref(v_x_1469_);
v_r_1474_ = lean_box(v_res_1473_);
return v_r_1474_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_heq_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1476_, v_i_1479_, v_k_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_1482_, lean_object* v_keys_1483_, lean_object* v_vals_1484_, lean_object* v_heq_1485_, lean_object* v_i_1486_, lean_object* v_k_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1482_, v_keys_1483_, v_vals_1484_, v_heq_1485_, v_i_1486_, v_k_1487_);
lean_dec_ref(v_k_1487_);
lean_dec_ref(v_vals_1484_);
lean_dec_ref(v_keys_1483_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg(){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___closed__0);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg___boxed(lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(lean_object* v_00_u03b1_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___boxed(lean_object* v_00_u03b1_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0(v_00_u03b1_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(lean_object* v_msg_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_ref_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
v_ref_1526_ = lean_ctor_get(v___y_1523_, 5);
v___x_1527_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Tactic_extractLetsAddVarInfo_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_inc(v_ref_1526_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_ref_1526_);
lean_ctor_set(v___x_1532_, 1, v_a_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 1);
lean_ctor_set(v___x_1530_, 0, v___x_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg___boxed(lean_object* v_msg_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1543_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__0));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0(lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_obj_once(&l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalExtractLets___lam__0___closed__1);
v___x_1558_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_1557_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__0___boxed(lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Elab_Tactic_evalExtractLets___lam__0(v_x_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_x_1559_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1(lean_object* v_h_1570_, lean_object* v___x_1571_, lean_object* v_a_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1574_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l_Lean_MVarId_extractLetsLocalDecl(v_a_1583_, v_h_1570_, v___x_1571_, v_a_1572_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v_fst_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1613_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v_fst_1586_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v_a_1585_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_a_1585_);
v_fst_1588_ = lean_ctor_get(v_fst_1586_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_fst_1586_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_fst_1586_, 1);
lean_dec(v_unused_1614_);
v___x_1590_ = v_fst_1586_;
v_isShared_1591_ = v_isSharedCheck_1613_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_fst_1588_);
lean_dec(v_fst_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1613_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = lean_box(0);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 1);
lean_ctor_set(v___x_1590_, 1, v___x_1592_);
lean_ctor_set(v___x_1590_, 0, v_snd_1587_);
v___x_1594_ = v___x_1590_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_snd_1587_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1594_, v___y_1574_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v___x_1595_, 0);
lean_dec(v_unused_1603_);
v___x_1597_ = v___x_1595_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v___x_1595_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_fst_1588_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_fst_1588_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_fst_1588_);
v_a_1604_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1595_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1595_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
v_a_1615_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1584_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1584_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_a_1572_);
lean_dec(v___x_1571_);
lean_dec(v_h_1570_);
v_a_1623_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1582_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1582_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed(lean_object* v_h_1631_, lean_object* v___x_1632_, lean_object* v_a_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Elab_Tactic_evalExtractLets___lam__1(v_h_1631_, v___x_1632_, v_a_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2(lean_object* v___x_1644_, lean_object* v_a_1645_, lean_object* v_ids_1646_, lean_object* v_h_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; 
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__1___boxed), 12, 3);
lean_closure_set(v___f_1657_, 0, v_h_1647_);
lean_closure_set(v___f_1657_, 1, v___x_1644_);
lean_closure_set(v___f_1657_, 2, v_a_1645_);
v___x_1658_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1657_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_1646_, v_a_1659_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1660_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec_ref(v_ids_1646_);
v_a_1661_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1658_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1658_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed(lean_object* v___x_1669_, lean_object* v_a_1670_, lean_object* v_ids_1671_, lean_object* v_h_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Elab_Tactic_evalExtractLets___lam__2(v___x_1669_, v_a_1670_, v_ids_1671_, v_h_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3(lean_object* v___x_1683_, lean_object* v_a_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1686_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = l_Lean_MVarId_extractLets(v_a_1695_, v___x_1683_, v_a_1684_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v_fst_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1725_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v_fst_1698_ = lean_ctor_get(v_a_1697_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_a_1697_, 1);
lean_inc(v_snd_1699_);
lean_dec(v_a_1697_);
v_fst_1700_ = lean_ctor_get(v_fst_1698_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_fst_1698_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_fst_1698_, 1);
lean_dec(v_unused_1726_);
v___x_1702_ = v_fst_1698_;
v_isShared_1703_ = v_isSharedCheck_1725_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_fst_1700_);
lean_dec(v_fst_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1725_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 1);
lean_ctor_set(v___x_1702_, 1, v___x_1704_);
lean_ctor_set(v___x_1702_, 0, v_snd_1699_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_snd_1699_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1706_, v___y_1686_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v___x_1707_, 0);
lean_dec(v_unused_1715_);
v___x_1709_ = v___x_1707_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v___x_1707_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v_fst_1700_);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_fst_1700_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_fst_1700_);
v_a_1716_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1707_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1707_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1727_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1696_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1696_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_a_1684_);
lean_dec(v___x_1683_);
v_a_1735_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1694_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1694_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed(lean_object* v___x_1743_, lean_object* v_a_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Elab_Tactic_evalExtractLets___lam__3(v___x_1743_, v_a_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4(lean_object* v___f_1755_, lean_object* v_ids_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1755_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1768_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(v_ids_1756_, v_a_1767_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1768_;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_ids_1756_);
v_a_1769_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1766_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1766_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed(lean_object* v___f_1777_, lean_object* v_ids_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Tactic_evalExtractLets___lam__4(v___f_1777_, v_ids_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(size_t v_sz_1789_, size_t v_i_1790_, lean_object* v_bs_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_usize_dec_lt(v_i_1790_, v_sz_1789_);
if (v___x_1792_ == 0)
{
return v_bs_1791_;
}
else
{
lean_object* v_v_1793_; lean_object* v___x_1794_; lean_object* v_bs_x27_1795_; lean_object* v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v_v_1793_ = lean_array_uget(v_bs_1791_, v_i_1790_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v_bs_x27_1795_ = lean_array_uset(v_bs_1791_, v_i_1790_, v___x_1794_);
v___x_1796_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_1793_);
lean_dec(v_v_1793_);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1790_, v___x_1797_);
v___x_1799_ = lean_array_uset(v_bs_x27_1795_, v_i_1790_, v___x_1796_);
v_i_1790_ = v___x_1798_;
v_bs_1791_ = v___x_1799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2___boxed(lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_bs_1803_){
_start:
{
size_t v_sz_boxed_1804_; size_t v_i_boxed_1805_; lean_object* v_res_1806_; 
v_sz_boxed_1804_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1805_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_boxed_1804_, v_i_boxed_1805_, v_bs_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets(lean_object* v_x_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
lean_inc(v_x_1827_);
v___x_1854_ = l_Lean_Syntax_isOfKind(v_x_1827_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
lean_dec(v_x_1827_);
v___x_1855_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1856_);
v___x_1858_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_1857_);
v___x_1859_ = l_Lean_Syntax_isOfKind(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec(v___x_1857_);
lean_dec(v_x_1827_);
v___x_1860_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1860_;
}
else
{
lean_object* v___f_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_loc_x3f_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___f_1861_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__5));
v___x_1862_ = lean_unsigned_to_nat(2u);
v___x_1863_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1862_);
v___x_1901_ = lean_unsigned_to_nat(3u);
v___x_1902_ = l_Lean_Syntax_getArg(v_x_1827_, v___x_1901_);
lean_dec(v_x_1827_);
v___x_1903_ = l_Lean_Syntax_isNone(v___x_1902_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; 
lean_inc(v___x_1902_);
v___x_1904_ = l_Lean_Syntax_matchesNull(v___x_1902_, v___x_1856_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_dec(v___x_1902_);
lean_dec(v___x_1863_);
lean_dec(v___x_1857_);
v___x_1905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; lean_object* v_loc_x3f_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
v_loc_x3f_1907_ = l_Lean_Syntax_getArg(v___x_1902_, v___x_1906_);
lean_dec(v___x_1902_);
v___x_1908_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_1907_);
v___x_1909_ = l_Lean_Syntax_isOfKind(v_loc_x3f_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
lean_dec(v_loc_x3f_1907_);
lean_dec(v___x_1863_);
lean_dec(v___x_1857_);
v___x_1910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_loc_x3f_1907_);
v_loc_x3f_1865_ = v___x_1911_;
v___y_1866_ = v_a_1828_;
v___y_1867_ = v_a_1829_;
v___y_1868_ = v_a_1830_;
v___y_1869_ = v_a_1831_;
v___y_1870_ = v_a_1832_;
v___y_1871_ = v_a_1833_;
v___y_1872_ = v_a_1834_;
v___y_1873_ = v_a_1835_;
goto v___jp_1864_;
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v___x_1902_);
v___x_1912_ = lean_box(0);
v_loc_x3f_1865_ = v___x_1912_;
v___y_1866_ = v_a_1828_;
v___y_1867_ = v_a_1829_;
v___y_1868_ = v_a_1830_;
v___y_1869_ = v_a_1831_;
v___y_1870_ = v_a_1832_;
v___y_1871_ = v_a_1833_;
v___y_1872_ = v_a_1834_;
v___y_1873_ = v_a_1835_;
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(v___x_1857_, v___y_1866_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_ids_1876_; size_t v_sz_1877_; size_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___f_1881_; lean_object* v___f_1882_; lean_object* v___f_1883_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_n(v_a_1875_, 2);
lean_dec_ref(v___x_1874_);
v_ids_1876_ = l_Lean_Syntax_getArgs(v___x_1863_);
lean_dec(v___x_1863_);
v_sz_1877_ = lean_array_size(v_ids_1876_);
v___x_1878_ = ((size_t)0ULL);
lean_inc_ref_n(v_ids_1876_, 2);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalExtractLets_spec__2(v_sz_1877_, v___x_1878_, v_ids_1876_);
v___x_1880_ = lean_array_to_list(v___x_1879_);
lean_inc(v___x_1880_);
v___f_1881_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__2___boxed), 13, 3);
lean_closure_set(v___f_1881_, 0, v___x_1880_);
lean_closure_set(v___f_1881_, 1, v_a_1875_);
lean_closure_set(v___f_1881_, 2, v_ids_1876_);
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_1882_, 0, v___x_1880_);
lean_closure_set(v___f_1882_, 1, v_a_1875_);
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___lam__4___boxed), 11, 2);
lean_closure_set(v___f_1883_, 0, v___f_1882_);
lean_closure_set(v___f_1883_, 1, v_ids_1876_);
if (lean_obj_tag(v_loc_x3f_1865_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_box(0);
v___y_1838_ = v___y_1867_;
v___y_1839_ = v___f_1881_;
v___y_1840_ = v___f_1883_;
v___y_1841_ = v___y_1870_;
v___y_1842_ = v___y_1872_;
v___y_1843_ = v___y_1868_;
v___y_1844_ = v___y_1873_;
v___y_1845_ = v___y_1869_;
v___y_1846_ = v___y_1871_;
v___y_1847_ = v___y_1866_;
v___y_1848_ = v___f_1861_;
v___y_1849_ = v___x_1884_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_val_1885_ = lean_ctor_get(v_loc_x3f_1865_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_loc_x3f_1865_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v_loc_x3f_1865_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_val_1885_);
lean_dec(v_loc_x3f_1865_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_val_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v___y_1838_ = v___y_1867_;
v___y_1839_ = v___f_1881_;
v___y_1840_ = v___f_1883_;
v___y_1841_ = v___y_1870_;
v___y_1842_ = v___y_1872_;
v___y_1843_ = v___y_1868_;
v___y_1844_ = v___y_1873_;
v___y_1845_ = v___y_1869_;
v___y_1846_ = v___y_1871_;
v___y_1847_ = v___y_1866_;
v___y_1848_ = v___f_1861_;
v___y_1849_ = v___x_1890_;
goto v___jp_1837_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_loc_x3f_1865_);
lean_dec(v___x_1863_);
v_a_1893_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1874_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1874_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
v___jp_1837_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_mkOptionalNode(v___y_1849_);
v___x_1851_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1850_);
lean_dec(v___x_1850_);
lean_inc_ref(v___y_1848_);
v___x_1852_ = l_Lean_Elab_Tactic_withLocation(v___x_1851_, v___y_1839_, v___y_1840_, v___y_1848_, v___y_1847_, v___y_1838_, v___y_1843_, v___y_1845_, v___y_1841_, v___y_1846_, v___y_1842_, v___y_1844_);
lean_dec(v___x_1851_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___boxed(lean_object* v_x_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Elab_Tactic_evalExtractLets(v_x_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(lean_object* v_00_u03b1_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v_msg_1925_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_msg_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1(v_00_u03b1_1936_, v_msg_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1(){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1955_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__2));
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___closed__1));
v___x_1958_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExtractLets___boxed), 10, 0);
v___x_1959_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1955_, v___x_1956_, v___x_1957_, v___x_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1___boxed(lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object* v_e_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1973_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_1974_ = 0;
v___x_1975_ = 1;
v___x_1976_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_1973_, v_e_1967_, v___x_1974_, v___x_1975_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object* v_e_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(lean_object* v_e_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_1984_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3____boxed(lean_object* v_e_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Elab_Tactic_evalUnsafe_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v_e_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
return v_res_2001_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2003_ = l_Lean_MessageData_ofName(v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__0);
v___x_2005_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__7);
v___x_2006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v___x_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(lean_object* v_optConfig_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; uint8_t v___y_2029_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v_recover_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; uint8_t v___x_2057_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; 
v_recover_2051_ = lean_ctor_get_uint8(v_a_2011_, sizeof(void*)*1);
lean_inc(v_optConfig_2010_);
v___x_2052_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_2010_);
v___x_2053_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_2052_);
v___x_2054_ = lean_array_get_size(v___x_2053_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_nat_dec_eq(v___x_2054_, v___x_2055_);
v___x_2057_ = 1;
if (v___x_2056_ == 0)
{
lean_object* v___x_2105_; lean_object* v_fileName_2106_; lean_object* v_fileMap_2107_; lean_object* v_options_2108_; lean_object* v_currRecDepth_2109_; lean_object* v_maxRecDepth_2110_; lean_object* v_ref_2111_; lean_object* v_currNamespace_2112_; lean_object* v_openDecls_2113_; lean_object* v_initHeartbeats_2114_; lean_object* v_maxHeartbeats_2115_; lean_object* v_quotContext_2116_; lean_object* v_currMacroScope_2117_; uint8_t v_diag_2118_; lean_object* v_cancelTk_x3f_2119_; uint8_t v_suppressElabErrors_2120_; lean_object* v_inheritedTraceOptions_2121_; lean_object* v_env_2122_; lean_object* v_ref_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2105_ = lean_st_ref_get(v_a_2017_);
v_fileName_2106_ = lean_ctor_get(v_a_2016_, 0);
v_fileMap_2107_ = lean_ctor_get(v_a_2016_, 1);
v_options_2108_ = lean_ctor_get(v_a_2016_, 2);
v_currRecDepth_2109_ = lean_ctor_get(v_a_2016_, 3);
v_maxRecDepth_2110_ = lean_ctor_get(v_a_2016_, 4);
v_ref_2111_ = lean_ctor_get(v_a_2016_, 5);
v_currNamespace_2112_ = lean_ctor_get(v_a_2016_, 6);
v_openDecls_2113_ = lean_ctor_get(v_a_2016_, 7);
v_initHeartbeats_2114_ = lean_ctor_get(v_a_2016_, 8);
v_maxHeartbeats_2115_ = lean_ctor_get(v_a_2016_, 9);
v_quotContext_2116_ = lean_ctor_get(v_a_2016_, 10);
v_currMacroScope_2117_ = lean_ctor_get(v_a_2016_, 11);
v_diag_2118_ = lean_ctor_get_uint8(v_a_2016_, sizeof(void*)*14);
v_cancelTk_x3f_2119_ = lean_ctor_get(v_a_2016_, 12);
v_suppressElabErrors_2120_ = lean_ctor_get_uint8(v_a_2016_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2121_ = lean_ctor_get(v_a_2016_, 13);
v_env_2122_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_ref(v_env_2122_);
lean_dec(v___x_2105_);
v_ref_2123_ = l_Lean_replaceRef(v_optConfig_2010_, v_ref_2111_);
lean_dec(v_optConfig_2010_);
lean_inc_ref(v_inheritedTraceOptions_2121_);
lean_inc(v_cancelTk_x3f_2119_);
lean_inc(v_currMacroScope_2117_);
lean_inc(v_quotContext_2116_);
lean_inc(v_maxHeartbeats_2115_);
lean_inc(v_initHeartbeats_2114_);
lean_inc(v_openDecls_2113_);
lean_inc(v_currNamespace_2112_);
lean_inc(v_maxRecDepth_2110_);
lean_inc(v_currRecDepth_2109_);
lean_inc_ref(v_options_2108_);
lean_inc_ref(v_fileMap_2107_);
lean_inc_ref(v_fileName_2106_);
v___x_2124_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2124_, 0, v_fileName_2106_);
lean_ctor_set(v___x_2124_, 1, v_fileMap_2107_);
lean_ctor_set(v___x_2124_, 2, v_options_2108_);
lean_ctor_set(v___x_2124_, 3, v_currRecDepth_2109_);
lean_ctor_set(v___x_2124_, 4, v_maxRecDepth_2110_);
lean_ctor_set(v___x_2124_, 5, v_ref_2123_);
lean_ctor_set(v___x_2124_, 6, v_currNamespace_2112_);
lean_ctor_set(v___x_2124_, 7, v_openDecls_2113_);
lean_ctor_set(v___x_2124_, 8, v_initHeartbeats_2114_);
lean_ctor_set(v___x_2124_, 9, v_maxHeartbeats_2115_);
lean_ctor_set(v___x_2124_, 10, v_quotContext_2116_);
lean_ctor_set(v___x_2124_, 11, v_currMacroScope_2117_);
lean_ctor_set(v___x_2124_, 12, v_cancelTk_x3f_2119_);
lean_ctor_set(v___x_2124_, 13, v_inheritedTraceOptions_2121_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*14, v_diag_2118_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*14 + 1, v_suppressElabErrors_2120_);
v___x_2125_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2126_ = l_Lean_Environment_contains(v_env_2122_, v___x_2125_, v___x_2057_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___x_2053_);
v___x_2127_ = lean_obj_once(&l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__1);
v___x_2128_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2127_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v___x_2124_, v_a_2017_);
lean_dec_ref(v___x_2124_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
v___y_2059_ = v_a_2012_;
v___y_2060_ = v_a_2013_;
v___y_2061_ = v_a_2014_;
v___y_2062_ = v_a_2015_;
v___y_2063_ = v___x_2124_;
v___y_2064_ = v_a_2017_;
goto v___jp_2058_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref(v___x_2053_);
lean_dec(v_optConfig_2010_);
v___x_2137_ = ((lean_object*)(l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___closed__2));
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
return v___x_2138_;
}
v___jp_2019_:
{
if (v___y_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref(v___y_2020_);
v___x_2030_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__1);
v___x_2031_ = l_Lean_MessageData_ofExpr(v___y_2024_);
v___x_2032_ = l_Lean_indentD(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2030_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__3);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = l_Lean_Exception_toMessageData(v___y_2025_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2035_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2037_, v___y_2027_, v___y_2028_, v___y_2023_, v___y_2026_, v___y_2022_, v___y_2021_);
lean_dec_ref(v___y_2022_);
return v___x_2038_;
}
else
{
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v___y_2022_);
return v___y_2020_;
}
}
v___jp_2039_:
{
lean_object* v___x_2047_; 
lean_inc_ref(v___y_2040_);
v___x_2047_ = l_Lean_Elab_Tactic_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_(v___y_2040_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_dec_ref(v___y_2045_);
lean_dec_ref(v___y_2040_);
return v___x_2047_;
}
else
{
lean_object* v_a_2048_; uint8_t v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
v___x_2049_ = l_Lean_Exception_isInterrupt(v_a_2048_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; 
lean_inc(v_a_2048_);
v___x_2050_ = l_Lean_Exception_isRuntime(v_a_2048_);
v___y_2020_ = v___x_2047_;
v___y_2021_ = v___y_2046_;
v___y_2022_ = v___y_2045_;
v___y_2023_ = v___y_2043_;
v___y_2024_ = v___y_2040_;
v___y_2025_ = v_a_2048_;
v___y_2026_ = v___y_2044_;
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___x_2050_;
goto v___jp_2019_;
}
else
{
v___y_2020_ = v___x_2047_;
v___y_2021_ = v___y_2046_;
v___y_2022_ = v___y_2045_;
v___y_2023_ = v___y_2043_;
v___y_2024_ = v___y_2040_;
v___y_2025_ = v_a_2048_;
v___y_2026_ = v___y_2044_;
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___x_2049_;
goto v___jp_2019_;
}
}
}
v___jp_2058_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_Lets_3494133133____hygCtx___hyg_3_));
v___x_2066_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__0(v___x_2065_, v___x_2057_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref(v___x_2066_);
v___x_2067_ = l_Lean_Elab_Tactic_elabConfig(v_recover_2051_, v___x_2065_, v___x_2053_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2088_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2070_ = v___x_2067_;
v_isShared_2071_ = v_isSharedCheck_2088_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2088_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; 
v___x_2072_ = l_Lean_Expr_hasSyntheticSorry(v_a_2068_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; 
lean_del_object(v___x_2070_);
v___x_2073_ = l_Lean_Expr_hasSorry(v_a_2068_);
if (v___x_2073_ == 0)
{
v___y_2040_ = v_a_2068_;
v___y_2041_ = v___y_2059_;
v___y_2042_ = v___y_2060_;
v___y_2043_ = v___y_2061_;
v___y_2044_ = v___y_2062_;
v___y_2045_ = v___y_2063_;
v___y_2046_ = v___y_2064_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_a_2068_);
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5, &l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg___closed__5);
v___x_2075_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabExtractLetsConfig_spec__1___redArg(v___x_2074_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec_ref(v___y_2063_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_a_2068_);
lean_dec_ref(v___y_2063_);
v___x_2084_ = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(v___x_2084_, 0, v___x_2056_);
lean_ctor_set_uint8(v___x_2084_, 1, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 2, v___x_2056_);
lean_ctor_set_uint8(v___x_2084_, 3, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 4, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 5, v___x_2056_);
lean_ctor_set_uint8(v___x_2084_, 6, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 7, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 8, v___x_2056_);
lean_ctor_set_uint8(v___x_2084_, 9, v___x_2057_);
lean_ctor_set_uint8(v___x_2084_, 10, v___x_2057_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2084_);
v___x_2086_ = v___x_2070_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v___y_2063_);
v_a_2089_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2067_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2067_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v___y_2063_);
lean_dec_ref(v___x_2053_);
v_a_2097_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2066_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2066_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg___boxed(lean_object* v_optConfig_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_optConfig_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig(lean_object* v_optConfig_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v_optConfig_2149_, v_a_2150_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabLiftLetsConfig___boxed(lean_object* v_optConfig_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Elab_Tactic_elabLiftLetsConfig(v_optConfig_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__0));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0(lean_object* v_x_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLiftLets___lam__0___closed__1);
v___x_2185_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2184_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__0___boxed(lean_object* v_x_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Elab_Tactic_evalLiftLets___lam__0(v_x_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v_x_2186_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1(lean_object* v_a_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2199_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_MVarId_liftLets(v_a_2208_, v_a_2197_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v_a_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2212_, v___y_2199_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2213_;
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
v_a_2214_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2209_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2209_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v_a_2197_);
v_a_2222_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2207_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2207_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed(lean_object* v_a_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Elab_Tactic_evalLiftLets___lam__1(v_a_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2(lean_object* v___f_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed(lean_object* v___f_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Elab_Tactic_evalLiftLets___lam__2(v___f_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3(lean_object* v_h_2263_, lean_object* v_a_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2266_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2276_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = l_Lean_MVarId_liftLetsLocalDecl(v_a_2275_, v_h_2263_, v_a_2264_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_box(0);
v___x_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2279_, v___y_2266_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2280_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2276_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2276_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec_ref(v_a_2264_);
lean_dec(v_h_2263_);
v_a_2289_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2274_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2274_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed(lean_object* v_h_2297_, lean_object* v_a_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Elab_Tactic_evalLiftLets___lam__3(v_h_2297_, v_a_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4(lean_object* v_a_2309_, lean_object* v_h_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___f_2320_; lean_object* v___x_2321_; 
v___f_2320_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2320_, 0, v_h_2310_);
lean_closure_set(v___f_2320_, 1, v_a_2309_);
v___x_2321_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2320_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed(lean_object* v_a_2322_, lean_object* v_h_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_Elab_Tactic_evalLiftLets___lam__4(v_a_2322_, v_h_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets(lean_object* v_x_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
lean_inc(v_x_2341_);
v___x_2368_ = l_Lean_Syntax_isOfKind(v_x_2341_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec(v_x_2341_);
v___x_2369_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__4));
lean_inc(v___x_2371_);
v___x_2373_ = l_Lean_Syntax_isOfKind(v___x_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec(v___x_2371_);
lean_dec(v_x_2341_);
v___x_2374_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2374_;
}
else
{
lean_object* v___f_2375_; lean_object* v_loc_x3f_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___f_2375_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__2));
v___x_2408_ = lean_unsigned_to_nat(2u);
v___x_2409_ = l_Lean_Syntax_getArg(v_x_2341_, v___x_2408_);
lean_dec(v_x_2341_);
v___x_2410_ = l_Lean_Syntax_isNone(v___x_2409_);
if (v___x_2410_ == 0)
{
uint8_t v___x_2411_; 
lean_inc(v___x_2409_);
v___x_2411_ = l_Lean_Syntax_matchesNull(v___x_2409_, v___x_2370_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec(v___x_2409_);
lean_dec(v___x_2371_);
v___x_2412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; lean_object* v_loc_x3f_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2413_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2414_ = l_Lean_Syntax_getArg(v___x_2409_, v___x_2413_);
lean_dec(v___x_2409_);
v___x_2415_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2414_);
v___x_2416_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_dec(v_loc_x3f_2414_);
lean_dec(v___x_2371_);
v___x_2417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_loc_x3f_2414_);
v_loc_x3f_2377_ = v___x_2418_;
v___y_2378_ = v_a_2342_;
v___y_2379_ = v_a_2343_;
v___y_2380_ = v_a_2344_;
v___y_2381_ = v_a_2345_;
v___y_2382_ = v_a_2346_;
v___y_2383_ = v_a_2347_;
v___y_2384_ = v_a_2348_;
v___y_2385_ = v_a_2349_;
goto v___jp_2376_;
}
}
}
else
{
lean_object* v___x_2419_; 
lean_dec(v___x_2409_);
v___x_2419_ = lean_box(0);
v_loc_x3f_2377_ = v___x_2419_;
v___y_2378_ = v_a_2342_;
v___y_2379_ = v_a_2343_;
v___y_2380_ = v_a_2344_;
v___y_2381_ = v_a_2345_;
v___y_2382_ = v_a_2346_;
v___y_2383_ = v_a_2347_;
v___y_2384_ = v_a_2348_;
v___y_2385_ = v_a_2349_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(v___x_2371_, v___y_2378_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___f_2388_; lean_object* v___f_2389_; lean_object* v___f_2390_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_n(v_a_2387_, 2);
lean_dec_ref(v___x_2386_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2388_, 0, v_a_2387_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_2389_, 0, v___f_2388_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__4___boxed), 11, 1);
lean_closure_set(v___f_2390_, 0, v_a_2387_);
if (lean_obj_tag(v_loc_x3f_2377_) == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_box(0);
v___y_2352_ = v___f_2389_;
v___y_2353_ = v___y_2382_;
v___y_2354_ = v___y_2381_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___f_2390_;
v___y_2357_ = v___y_2385_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v___y_2380_;
v___y_2360_ = v___y_2384_;
v___y_2361_ = v___y_2378_;
v___y_2362_ = v___f_2375_;
v___y_2363_ = v___x_2391_;
goto v___jp_2351_;
}
else
{
lean_object* v_val_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_val_2392_ = lean_ctor_get(v_loc_x3f_2377_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_loc_x3f_2377_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v_loc_x3f_2377_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_val_2392_);
lean_dec(v_loc_x3f_2377_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_val_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v___y_2352_ = v___f_2389_;
v___y_2353_ = v___y_2382_;
v___y_2354_ = v___y_2381_;
v___y_2355_ = v___y_2379_;
v___y_2356_ = v___f_2390_;
v___y_2357_ = v___y_2385_;
v___y_2358_ = v___y_2383_;
v___y_2359_ = v___y_2380_;
v___y_2360_ = v___y_2384_;
v___y_2361_ = v___y_2378_;
v___y_2362_ = v___f_2375_;
v___y_2363_ = v___x_2397_;
goto v___jp_2351_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_loc_x3f_2377_);
v_a_2400_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2386_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2386_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
v___jp_2351_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_mkOptionalNode(v___y_2363_);
v___x_2365_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2364_);
lean_dec(v___x_2364_);
lean_inc_ref(v___y_2362_);
v___x_2366_ = l_Lean_Elab_Tactic_withLocation(v___x_2365_, v___y_2356_, v___y_2352_, v___y_2362_, v___y_2361_, v___y_2355_, v___y_2359_, v___y_2354_, v___y_2353_, v___y_2358_, v___y_2360_, v___y_2357_);
lean_dec(v___x_2365_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___boxed(lean_object* v_x_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Elab_Tactic_evalLiftLets(v_x_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1(){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2438_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___closed__1));
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___closed__1));
v___x_2441_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___boxed), 10, 0);
v___x_2442_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2438_, v___x_2439_, v___x_2440_, v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1___boxed(lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
return v_res_2444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__0));
v___x_2447_ = l_Lean_stringToMessageData(v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0(lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1, &l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_evalLetToHave___lam__0___closed__1);
v___x_2459_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalExtractLets_spec__1___redArg(v___x_2458_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__0___boxed(lean_object* v_x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_Elab_Tactic_evalLetToHave___lam__0(v_x_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v_x_2460_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1(uint8_t v___x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2473_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = l_Lean_MVarId_letToHave(v_a_2482_, v___x_2471_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2483_);
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2486_, v___y_2473_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2487_;
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2483_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2483_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_a_2496_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2481_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2481_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed(lean_object* v___x_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v___x_1772__boxed_2514_; lean_object* v_res_2515_; 
v___x_1772__boxed_2514_ = lean_unbox(v___x_2504_);
v_res_2515_ = l_Lean_Elab_Tactic_evalLetToHave___lam__1(v___x_1772__boxed_2514_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3(lean_object* v_h_2516_, uint8_t v___x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_2519_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = l_Lean_MVarId_letToHaveLocalDecl(v_a_2528_, v_h_2516_, v___x_2517_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_a_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2532_, v___y_2519_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2533_;
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2529_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2529_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_h_2516_);
v_a_2542_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2527_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2527_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed(lean_object* v_h_2550_, lean_object* v___x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
uint8_t v___x_1848__boxed_2561_; lean_object* v_res_2562_; 
v___x_1848__boxed_2561_ = lean_unbox(v___x_2551_);
v_res_2562_ = l_Lean_Elab_Tactic_evalLetToHave___lam__3(v_h_2550_, v___x_1848__boxed_2561_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2(uint8_t v___x_2563_, lean_object* v_h_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(v___x_2563_);
v___f_2575_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__3___boxed), 11, 2);
lean_closure_set(v___f_2575_, 0, v_h_2564_);
lean_closure_set(v___f_2575_, 1, v___x_2574_);
v___x_2576_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_2575_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed(lean_object* v___x_2577_, lean_object* v_h_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
uint8_t v___x_1924__boxed_2588_; lean_object* v_res_2589_; 
v___x_1924__boxed_2588_ = lean_unbox(v___x_2577_);
v_res_2589_ = l_Lean_Elab_Tactic_evalLetToHave___lam__2(v___x_1924__boxed_2588_, v_h_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave(lean_object* v_x_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
lean_inc(v_x_2597_);
v___x_2608_ = l_Lean_Syntax_isOfKind(v_x_2597_, v___x_2607_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
lean_dec(v_x_2597_);
v___x_2609_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2609_;
}
else
{
lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___f_2615_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___f_2610_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__2));
v___x_2611_ = lean_box(v___x_2608_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2612_, 0, v___x_2611_);
v___f_2613_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLiftLets___lam__2___boxed), 10, 1);
lean_closure_set(v___f_2613_, 0, v___f_2612_);
v___x_2614_ = lean_box(v___x_2608_);
v___f_2615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___lam__2___boxed), 11, 1);
lean_closure_set(v___f_2615_, 0, v___x_2614_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = l_Lean_Syntax_getArg(v_x_2597_, v___x_2629_);
lean_dec(v_x_2597_);
v___x_2631_ = l_Lean_Syntax_isNone(v___x_2630_);
if (v___x_2631_ == 0)
{
uint8_t v___x_2632_; 
lean_inc(v___x_2630_);
v___x_2632_ = l_Lean_Syntax_matchesNull(v___x_2630_, v___x_2629_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v___x_2630_);
lean_dec_ref(v___f_2615_);
lean_dec_ref(v___f_2613_);
v___x_2633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v_loc_x3f_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v_loc_x3f_2635_ = l_Lean_Syntax_getArg(v___x_2630_, v___x_2634_);
lean_dec(v___x_2630_);
v___x_2636_ = ((lean_object*)(l_Lean_Elab_Tactic_evalExtractLets___closed__7));
lean_inc(v_loc_x3f_2635_);
v___x_2637_ = l_Lean_Syntax_isOfKind(v_loc_x3f_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec(v_loc_x3f_2635_);
lean_dec_ref(v___f_2615_);
lean_dec_ref(v___f_2613_);
v___x_2638_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalExtractLets_spec__0___redArg();
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_loc_x3f_2635_);
v___y_2617_ = v_a_2600_;
v___y_2618_ = v_a_2604_;
v___y_2619_ = v_a_2602_;
v___y_2620_ = v_a_2605_;
v___y_2621_ = v_a_2599_;
v___y_2622_ = v_a_2598_;
v___y_2623_ = v_a_2601_;
v___y_2624_ = v_a_2603_;
v___y_2625_ = v___x_2639_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v___x_2640_; 
lean_dec(v___x_2630_);
v___x_2640_ = lean_box(0);
v___y_2617_ = v_a_2600_;
v___y_2618_ = v_a_2604_;
v___y_2619_ = v_a_2602_;
v___y_2620_ = v_a_2605_;
v___y_2621_ = v_a_2599_;
v___y_2622_ = v_a_2598_;
v___y_2623_ = v_a_2601_;
v___y_2624_ = v_a_2603_;
v___y_2625_ = v___x_2640_;
goto v___jp_2616_;
}
v___jp_2616_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = l_Lean_mkOptionalNode(v___y_2625_);
v___x_2627_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2626_);
lean_dec(v___x_2626_);
v___x_2628_ = l_Lean_Elab_Tactic_withLocation(v___x_2627_, v___f_2615_, v___f_2613_, v___f_2610_, v___y_2622_, v___y_2621_, v___y_2617_, v___y_2623_, v___y_2619_, v___y_2624_, v___y_2618_, v___y_2620_);
lean_dec(v___x_2627_);
return v___x_2628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___boxed(lean_object* v_x_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_Elab_Tactic_evalLetToHave(v_x_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1(){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2659_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_2660_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___closed__1));
v___x_2661_ = ((lean_object*)(l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___closed__1));
v___x_2662_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalLetToHave___boxed), 10, 0);
v___x_2663_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2659_, v___x_2660_, v___x_2661_, v___x_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1___boxed(lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
return v_res_2665_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Lets_363591437____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_linter_tactic_unusedName = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_linter_tactic_unusedName);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalExtractLets___regBuiltin_Lean_Elab_Tactic_evalExtractLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalLiftLets___regBuiltin_Lean_Elab_Tactic_evalLiftLets__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalLetToHave___regBuiltin_Lean_Elab_Tactic_evalLetToHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Lets(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Lets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Lets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Lets(builtin);
}
#ifdef __cplusplus
}
#endif
