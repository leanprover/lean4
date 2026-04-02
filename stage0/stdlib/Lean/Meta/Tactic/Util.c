// Lean compiler output
// Module: Lean.Meta.Tactic.Util
// Imports: public import Lean.Util.ForEachExprWhere public import Lean.Meta.PPGoal import Lean.Meta.AppBuilder
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "terminalTacticsAsSorry"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 90, 215, 151, 242, 202, 226, 151)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 139, .m_capacity = 139, .m_length = 138, .m_data = "when enabled, terminal tactics such as `grind` and `omega` are replaced with `sorry`. Useful for debugging and fixing bootstrapping issues"};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 233, 55, 94, 186, 188, 252, 158)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 217, 134, 189, 91, 246, 107, 44)}};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_debug_terminalTacticsAsSorry;
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__0 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__1;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed: "};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__2 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__3;
static const lean_string_object l_Lean_Meta_mkTacticExMsg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Meta_mkTacticExMsg___closed__4 = (const lean_object*)&l_Lean_Meta_mkTacticExMsg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_mkTacticExMsg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkTacticExMsg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` failed\n\n"};
static const lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwTacticEx___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "` failed with a nested error:\n"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__1;
static const lean_string_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nested"};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 50, 115, 245, 92, 68, 45, 137)}};
static const lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "The metavariable below has already been assigned"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__0 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__0_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__1;
static const lean_string_object l_Lean_MVarId_checkNotAssigned___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "This likely indicates an internal error in this tactic or a prior one"};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__2 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value;
static const lean_ctor_object l_Lean_MVarId_checkNotAssigned___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__2_value)}};
static const lean_object* l_Lean_MVarId_checkNotAssigned___closed__3 = (const lean_object*)&l_Lean_MVarId_checkNotAssigned___closed__3_value;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__4;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__5;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__6;
static lean_once_cell_t l_Lean_MVarId_checkNotAssigned___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_checkNotAssigned___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 80, 134, 96, 135, 241, 87, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 105, 212, 82, 205, 98, 36, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 108, 151, 68, 40, 185, 49, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 35, 20, 40, 241, 13, 114, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 161, 8, 73, 13, 24, 41, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 240, 21, 38, 82, 97, 50, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 251, 182, 143, 63, 208, 115, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 226, 182, 237, 212, 141, 147, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 251, 116, 130, 175, 2, 54, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 96, 175, 63, 15, 15, 160, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1901113268) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 118, 41, 237, 158, 247, 69, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 149, 39, 205, 173, 64, 129, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 101, 131, 162, 224, 178, 204, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(23, 46, 117, 252, 169, 255, 192, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_admit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "admit"};
static const lean_object* l_Lean_MVarId_admit___closed__0 = (const lean_object*)&l_Lean_MVarId_admit___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_admit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_admit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 138, 207, 107, 141, 184, 85, 68)}};
static const lean_object* l_Lean_MVarId_admit___closed__1 = (const lean_object*)&l_Lean_MVarId_admit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__0 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__0_value;
static const lean_closure_object l_Lean_MVarId_getNondepPropHyps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MVarId_getNondepPropHyps___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MVarId_getNondepPropHyps___closed__1 = (const lean_object*)&l_Lean_MVarId_getNondepPropHyps___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "`infer_instance` tactic failed to assign instance"};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__0_value)}};
static const lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__2;
static lean_once_cell_t l_Lean_MVarId_inferInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MVarId_inferInstance___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_inferInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "infer_instance"};
static const lean_object* l_Lean_MVarId_inferInstance___closed__0 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_inferInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_inferInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 181, 58, 140, 126, 222, 16, 71)}};
static const lean_object* l_Lean_MVarId_inferInstance___closed__1 = (const lean_object*)&l_Lean_MVarId_inferInstance___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MVarId_isSubsingleton___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Subsingleton"};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__0 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value;
static const lean_ctor_object l_Lean_MVarId_isSubsingleton___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MVarId_isSubsingleton___closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 130, 42, 228, 248, 162, 23, 186)}};
static const lean_object* l_Lean_MVarId_isSubsingleton___closed__1 = (const lean_object*)&l_Lean_MVarId_isSubsingleton___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "skipAssignedInstances"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 172, 231, 36, 182, 217, 37, 75)}};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "in the `rw` and `simp` tactics, if an instance implicit argument is assigned, do not try to synthesize instance."};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 5, 107, 131, 111, 226, 218, 126)}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_MVarId_getDecl(v_mvarId_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_userName_74_; lean_object* v___x_76_; 
v_userName_74_ = lean_ctor_get(v_a_70_, 0);
lean_inc(v_userName_74_);
lean_dec(v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v_userName_74_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_userName_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_69_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_69_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_MVarId_getTag(v_mvarId_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_94_, lean_object* v_tag_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; lean_object* v_mctx_99_; lean_object* v_cache_100_; lean_object* v_zetaDeltaFVarIds_101_; lean_object* v_postponed_102_; lean_object* v_diag_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_114_; 
v___x_98_ = lean_st_ref_take(v_a_96_);
v_mctx_99_ = lean_ctor_get(v___x_98_, 0);
v_cache_100_ = lean_ctor_get(v___x_98_, 1);
v_zetaDeltaFVarIds_101_ = lean_ctor_get(v___x_98_, 2);
v_postponed_102_ = lean_ctor_get(v___x_98_, 3);
v_diag_103_ = lean_ctor_get(v___x_98_, 4);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_114_ == 0)
{
v___x_105_ = v___x_98_;
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_diag_103_);
lean_inc(v_postponed_102_);
lean_inc(v_zetaDeltaFVarIds_101_);
lean_inc(v_cache_100_);
lean_inc(v_mctx_99_);
lean_dec(v___x_98_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_114_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_99_, v_mvarId_94_, v_tag_95_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_109_ = v___x_105_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_zetaDeltaFVarIds_101_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_postponed_102_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v_diag_103_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_st_ref_set(v_a_96_, v___x_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object* v_mvarId_115_, lean_object* v_tag_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_MVarId_setTag___redArg(v_mvarId_115_, v_tag_116_, v_a_117_);
lean_dec(v_a_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_120_, lean_object* v_tag_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_MVarId_setTag___redArg(v_mvarId_120_, v_tag_121_, v_a_123_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_128_, lean_object* v_tag_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_MVarId_setTag(v_mvarId_128_, v_tag_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_136_, lean_object* v_x_137_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_erase_macro_scopes(v_suffix_136_);
v___x_139_ = l_Lean_Name_append(v_x_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_140_, lean_object* v_suffix_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = l_Lean_Name_hasMacroScopes(v_tag_140_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_appendTag___lam__0(v_suffix_141_, v_tag_140_);
return v___x_143_;
}
else
{
lean_object* v_view_144_; lean_object* v_name_145_; lean_object* v_imported_146_; lean_object* v_ctx_147_; lean_object* v_scopes_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_157_; 
v_view_144_ = l_Lean_extractMacroScopes(v_tag_140_);
v_name_145_ = lean_ctor_get(v_view_144_, 0);
v_imported_146_ = lean_ctor_get(v_view_144_, 1);
v_ctx_147_ = lean_ctor_get(v_view_144_, 2);
v_scopes_148_ = lean_ctor_get(v_view_144_, 3);
v_isSharedCheck_157_ = !lean_is_exclusive(v_view_144_);
if (v_isSharedCheck_157_ == 0)
{
v___x_150_ = v_view_144_;
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_scopes_148_);
lean_inc(v_ctx_147_);
lean_inc(v_imported_146_);
lean_inc(v_name_145_);
lean_dec(v_view_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_Meta_appendTag___lam__0(v_suffix_141_, v_name_145_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_152_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_imported_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_ctx_147_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_scopes_148_);
v___x_154_ = v_reuseFailAlloc_156_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_MacroScopesView_review(v___x_154_);
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_158_, lean_object* v_suffix_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_165_; 
lean_inc(v_mvarId_158_);
v___x_165_ = l_Lean_MVarId_getTag(v_mvarId_158_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Lean_Meta_appendTag(v_a_166_, v_suffix_159_);
v___x_168_ = l_Lean_MVarId_setTag___redArg(v_mvarId_158_, v___x_167_, v_a_161_);
return v___x_168_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_suffix_159_);
lean_dec(v_mvarId_158_);
v_a_169_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_165_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_177_, lean_object* v_suffix_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_appendTagSuffix(v_mvarId_177_, v_suffix_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_185_, lean_object* v_tag_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_type_185_);
v___x_193_ = 2;
v___x_194_ = l_Lean_Meta_mkFreshExprMVar(v___x_192_, v___x_193_, v_tag_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_195_, lean_object* v_tag_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_195_, v_tag_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_202_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_212_, lean_object* v_mvarId_213_, lean_object* v_msg_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_215_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_216_ = l_Lean_MessageData_ofName(v_tacticName_212_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v_msg_214_);
v___x_221_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_mvarId_213_);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v_mctx_234_; lean_object* v_lctx_235_; lean_object* v_options_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_231_ = lean_st_ref_get(v___y_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = lean_st_ref_get(v___y_227_);
v_mctx_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_mctx_234_);
lean_dec(v___x_233_);
v_lctx_235_ = lean_ctor_get(v___y_226_, 2);
v_options_236_ = lean_ctor_get(v___y_228_, 2);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_lctx_235_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_232_);
lean_ctor_set(v___x_237_, 1, v_mctx_234_);
lean_ctor_set(v___x_237_, 2, v_lctx_235_);
lean_ctor_set(v___x_237_, 3, v_options_236_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_225_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_ref_253_ = lean_ctor_get(v___y_250_, 5);
v___x_254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_ref_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_ref_253_);
lean_ctor_set(v___x_259_, 1, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_274_, lean_object* v_mvarId_275_, lean_object* v_msg_x3f_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
if (lean_obj_tag(v_msg_x3f_276_) == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_282_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_283_ = l_Lean_MessageData_ofName(v_tacticName_274_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v_mvarId_275_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_288_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_289_;
}
else
{
lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_val_290_ = lean_ctor_get(v_msg_x3f_276_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v_msg_x3f_276_);
v___x_291_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_274_, v_mvarId_275_, v_val_290_);
v___x_292_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_291_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_293_, lean_object* v_mvarId_294_, lean_object* v_msg_x3f_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_293_, v_mvarId_294_, v_msg_x3f_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_302_, lean_object* v_tacticName_303_, lean_object* v_mvarId_304_, lean_object* v_msg_x3f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_303_, v_mvarId_304_, v_msg_x3f_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_312_, lean_object* v_tacticName_313_, lean_object* v_mvarId_314_, lean_object* v_msg_x3f_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_312_, v_tacticName_313_, v_mvarId_314_, v_msg_x3f_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_322_, lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_330_, v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_340_ = l_Lean_stringToMessageData(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_344_, lean_object* v_ex_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_nestedMsg_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_msg_357_; lean_object* v_kind_358_; uint8_t v___x_359_; 
v_nestedMsg_351_ = l_Lean_Exception_toMessageData(v_ex_345_);
v___x_352_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_353_ = l_Lean_MessageData_ofName(v_tacticName_344_);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc_ref(v_nestedMsg_351_);
v_msg_357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_357_, 0, v___x_356_);
lean_ctor_set(v_msg_357_, 1, v_nestedMsg_351_);
v_kind_358_ = l_Lean_MessageData_kind(v_nestedMsg_351_);
lean_dec_ref(v_nestedMsg_351_);
v___x_359_ = l_Lean_Name_isAnonymous(v_kind_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_361_ = l_Lean_Name_append(v___x_360_, v_kind_358_);
v___x_362_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v_msg_357_);
v___x_363_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_362_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_kind_358_);
v___x_364_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_357_, v_a_346_, v_a_347_, v_a_348_, v_a_349_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_365_, lean_object* v_ex_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_365_, v_ex_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_373_, lean_object* v_tacticName_374_, lean_object* v_ex_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_374_, v_ex_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_382_, lean_object* v_tacticName_383_, lean_object* v_ex_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_382_, v_tacticName_383_, v_ex_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_391_, lean_object* v_i_392_, lean_object* v_k_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_array_get_size(v_keys_391_);
v___x_395_ = lean_nat_dec_lt(v_i_392_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v_i_392_);
return v___x_395_;
}
else
{
lean_object* v_k_x27_396_; uint8_t v___x_397_; 
v_k_x27_396_ = lean_array_fget_borrowed(v_keys_391_, v_i_392_);
v___x_397_ = l_Lean_instBEqMVarId_beq(v_k_393_, v_k_x27_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_i_392_, v___x_398_);
lean_dec(v_i_392_);
v_i_392_ = v___x_399_;
goto _start;
}
else
{
lean_dec(v_i_392_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_401_, lean_object* v_i_402_, lean_object* v_k_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_401_, v_i_402_, v_k_403_);
lean_dec(v_k_403_);
lean_dec_ref(v_keys_401_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; 
v___x_406_ = ((size_t)5ULL);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_shift_left(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; 
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_411_ = lean_usize_sub(v___x_410_, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_412_, size_t v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v_es_415_; lean_object* v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v_j_420_; lean_object* v___x_421_; 
v_es_415_ = lean_ctor_get(v_x_412_, 0);
v___x_416_ = lean_box(2);
v___x_417_ = ((size_t)5ULL);
v___x_418_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_419_ = lean_usize_land(v_x_413_, v___x_418_);
v_j_420_ = lean_usize_to_nat(v___x_419_);
v___x_421_ = lean_array_get_borrowed(v___x_416_, v_es_415_, v_j_420_);
lean_dec(v_j_420_);
switch(lean_obj_tag(v___x_421_))
{
case 0:
{
lean_object* v_key_422_; uint8_t v___x_423_; 
v_key_422_ = lean_ctor_get(v___x_421_, 0);
v___x_423_ = l_Lean_instBEqMVarId_beq(v_x_414_, v_key_422_);
return v___x_423_;
}
case 1:
{
lean_object* v_node_424_; size_t v___x_425_; 
v_node_424_ = lean_ctor_get(v___x_421_, 0);
v___x_425_ = lean_usize_shift_right(v_x_413_, v___x_417_);
v_x_412_ = v_node_424_;
v_x_413_ = v___x_425_;
goto _start;
}
default: 
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
}
}
else
{
lean_object* v_ks_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_ks_428_ = lean_ctor_get(v_x_412_, 0);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_428_, v___x_429_, v_x_414_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_595__boxed_434_; uint8_t v_res_435_; lean_object* v_r_436_; 
v_x_595__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_431_, v_x_595__boxed_434_, v_x_433_);
lean_dec(v_x_433_);
lean_dec_ref(v_x_431_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
uint64_t v___x_439_; size_t v___x_440_; uint8_t v___x_441_; 
v___x_439_ = l_Lean_instHashableMVarId_hash(v_x_438_);
v___x_440_ = lean_uint64_to_usize(v___x_439_);
v___x_441_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_437_, v___x_440_, v_x_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_442_, v_x_443_);
lean_dec(v_x_443_);
lean_dec_ref(v_x_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_eAssignment_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = lean_st_ref_get(v___y_447_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_mctx_450_);
lean_dec(v___x_449_);
v_eAssignment_451_ = lean_ctor_get(v_mctx_450_, 8);
lean_inc_ref(v_eAssignment_451_);
lean_dec_ref(v_mctx_450_);
v___x_452_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_451_, v_mvarId_446_);
lean_dec_ref(v_eAssignment_451_);
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec(v_mvarId_455_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_466_ = l_Lean_MessageData_ofFormat(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_468_ = l_Lean_MessageData_note(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_470_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_474_, lean_object* v_tacticName_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_493_; 
v___x_481_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_474_, v_a_477_);
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_493_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_493_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
uint8_t v___x_486_; 
v___x_486_ = lean_unbox(v_a_482_);
lean_dec(v_a_482_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v_tacticName_475_);
lean_dec(v_mvarId_474_);
v___x_487_ = lean_box(0);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_del_object(v___x_484_);
v___x_491_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_492_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_475_, v_mvarId_474_, v___x_491_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_494_, lean_object* v_tacticName_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_494_, v_tacticName_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_502_, v___y_504_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v_mvarId_509_);
return v_res_515_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_520_, v_x_521_, v_x_522_);
lean_dec(v_x_522_);
lean_dec_ref(v_x_521_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_525_, lean_object* v_x_526_, size_t v_x_527_, lean_object* v_x_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_526_, v_x_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
size_t v_x_768__boxed_534_; uint8_t v_res_535_; lean_object* v_r_536_; 
v_x_768__boxed_534_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_res_535_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_530_, v_x_531_, v_x_768__boxed_534_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_x_531_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_537_, lean_object* v_keys_538_, lean_object* v_vals_539_, lean_object* v_heq_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_538_, v_i_541_, v_k_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_544_, lean_object* v_keys_545_, lean_object* v_vals_546_, lean_object* v_heq_547_, lean_object* v_i_548_, lean_object* v_k_549_){
_start:
{
uint8_t v_res_550_; lean_object* v_r_551_; 
v_res_550_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_544_, v_keys_545_, v_vals_546_, v_heq_547_, v_i_548_, v_k_549_);
lean_dec(v_k_549_);
lean_dec_ref(v_vals_546_);
lean_dec_ref(v_keys_545_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_MVarId_getDecl(v_mvarId_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_type_563_; lean_object* v___x_565_; 
v_type_563_ = lean_ctor_get(v_a_559_, 2);
lean_inc_ref(v_type_563_);
lean_dec(v_a_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_type_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_type_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_558_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_MVarId_getType(v_mvarId_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_583_, lean_object* v___y_584_){
_start:
{
uint8_t v___x_586_; 
v___x_586_ = l_Lean_Expr_hasMVar(v_e_583_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_e_583_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; lean_object* v_mctx_589_; lean_object* v___x_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; lean_object* v_cache_594_; lean_object* v_zetaDeltaFVarIds_595_; lean_object* v_postponed_596_; lean_object* v_diag_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_606_; 
v___x_588_ = lean_st_ref_get(v___y_584_);
v_mctx_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_mctx_589_);
lean_dec(v___x_588_);
v___x_590_ = l_Lean_instantiateMVarsCore(v_mctx_589_, v_e_583_);
v_fst_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_590_);
v___x_593_ = lean_st_ref_take(v___y_584_);
v_cache_594_ = lean_ctor_get(v___x_593_, 1);
v_zetaDeltaFVarIds_595_ = lean_ctor_get(v___x_593_, 2);
v_postponed_596_ = lean_ctor_get(v___x_593_, 3);
v_diag_597_ = lean_ctor_get(v___x_593_, 4);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_607_);
v___x_599_ = v___x_593_;
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_diag_597_);
lean_inc(v_postponed_596_);
lean_inc(v_zetaDeltaFVarIds_595_);
lean_inc(v_cache_594_);
lean_dec(v___x_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_606_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_snd_592_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_snd_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_cache_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_zetaDeltaFVarIds_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_postponed_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_diag_597_);
v___x_602_ = v_reuseFailAlloc_605_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_st_ref_set(v___y_584_, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_fst_591_);
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_608_, v___y_609_);
lean_dec(v___y_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_612_, v___y_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_MVarId_getType(v_mvarId_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
lean_inc(v_a_630_);
lean_inc_ref(v_a_629_);
lean_inc(v_a_628_);
lean_inc_ref(v_a_627_);
v___x_634_ = lean_whnf(v_a_633_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_635_, v_a_628_);
return v___x_636_;
}
else
{
return v___x_634_;
}
}
else
{
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_MVarId_getType_x27(v_mvarId_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_710_ = 0;
v___x_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_712_ = l_Lean_registerTraceClass(v___x_709_, v___x_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_715_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_722_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_722_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_739_, v_x_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_747_, lean_object* v_mvarId_748_, lean_object* v_x_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_748_, v_x_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_756_, lean_object* v_mvarId_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_756_, v_mvarId_757_, v_x_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_ks_769_; lean_object* v_vs_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_794_; 
v_ks_769_ = lean_ctor_get(v_x_765_, 0);
v_vs_770_ = lean_ctor_get(v_x_765_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_794_ == 0)
{
v___x_772_ = v_x_765_;
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_vs_770_);
lean_inc(v_ks_769_);
lean_dec(v_x_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_794_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_ks_769_);
v___x_775_ = lean_nat_dec_lt(v_x_766_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_x_766_);
v___x_776_ = lean_array_push(v_ks_769_, v_x_767_);
v___x_777_ = lean_array_push(v_vs_770_, v_x_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_777_);
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v_k_x27_781_; uint8_t v___x_782_; 
v_k_x27_781_ = lean_array_fget_borrowed(v_ks_769_, v_x_766_);
v___x_782_ = l_Lean_instBEqMVarId_beq(v_x_767_, v_k_x27_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_784_; 
if (v_isShared_773_ == 0)
{
v___x_784_ = v___x_772_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_ks_769_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_vs_770_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_x_766_, v___x_785_);
lean_dec(v_x_766_);
v_x_765_ = v___x_784_;
v_x_766_ = v___x_786_;
goto _start;
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_array_fset(v_ks_769_, v_x_766_, v_x_767_);
v___x_790_ = lean_array_fset(v_vs_770_, v_x_766_, v_x_768_);
lean_dec(v_x_766_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_790_);
lean_ctor_set(v___x_772_, 0, v___x_789_);
v___x_792_ = v___x_772_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_795_, lean_object* v_k_796_, lean_object* v_v_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_795_, v___x_798_, v_k_796_, v_v_797_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_801_, size_t v_x_802_, size_t v_x_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v_es_806_; size_t v___x_807_; size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; lean_object* v_j_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_es_806_ = lean_ctor_get(v_x_801_, 0);
v___x_807_ = ((size_t)5ULL);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_810_ = lean_usize_land(v_x_802_, v___x_809_);
v_j_811_ = lean_usize_to_nat(v___x_810_);
v___x_812_ = lean_array_get_size(v_es_806_);
v___x_813_ = lean_nat_dec_lt(v_j_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_j_811_);
lean_dec(v_x_805_);
lean_dec(v_x_804_);
return v_x_801_;
}
else
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_850_; 
lean_inc_ref(v_es_806_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_x_801_, 0);
lean_dec(v_unused_851_);
v___x_815_ = v_x_801_;
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_x_801_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_850_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_v_817_; lean_object* v___x_818_; lean_object* v_xs_x27_819_; lean_object* v___y_821_; 
v_v_817_ = lean_array_fget(v_es_806_, v_j_811_);
v___x_818_ = lean_box(0);
v_xs_x27_819_ = lean_array_fset(v_es_806_, v_j_811_, v___x_818_);
switch(lean_obj_tag(v_v_817_))
{
case 0:
{
lean_object* v_key_826_; lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_837_; 
v_key_826_ = lean_ctor_get(v_v_817_, 0);
v_val_827_ = lean_ctor_get(v_v_817_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_837_ == 0)
{
v___x_829_ = v_v_817_;
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_inc(v_key_826_);
lean_dec(v_v_817_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_837_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_instBEqMVarId_beq(v_x_804_, v_key_826_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_829_);
v___x_832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_826_, v_val_827_, v_x_804_, v_x_805_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___y_821_ = v___x_833_;
goto v___jp_820_;
}
else
{
lean_object* v___x_835_; 
lean_dec(v_val_827_);
lean_dec(v_key_826_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v_x_805_);
lean_ctor_set(v___x_829_, 0, v_x_804_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_x_804_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_x_805_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
v___y_821_ = v___x_835_;
goto v___jp_820_;
}
}
}
}
case 1:
{
lean_object* v_node_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_848_; 
v_node_838_ = lean_ctor_get(v_v_817_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_v_817_);
if (v_isSharedCheck_848_ == 0)
{
v___x_840_ = v_v_817_;
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_node_838_);
lean_dec(v_v_817_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_842_ = lean_usize_shift_right(v_x_802_, v___x_807_);
v___x_843_ = lean_usize_add(v_x_803_, v___x_808_);
v___x_844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_838_, v___x_842_, v___x_843_, v_x_804_, v_x_805_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v___y_821_ = v___x_846_;
goto v___jp_820_;
}
}
}
default: 
{
lean_object* v___x_849_; 
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v_x_804_);
lean_ctor_set(v___x_849_, 1, v_x_805_);
v___y_821_ = v___x_849_;
goto v___jp_820_;
}
}
v___jp_820_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_array_fset(v_xs_x27_819_, v_j_811_, v___y_821_);
lean_dec(v_j_811_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_822_);
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_873_; 
v_ks_852_ = lean_ctor_get(v_x_801_, 0);
v_vs_853_ = lean_ctor_get(v_x_801_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_x_801_);
if (v_isSharedCheck_873_ == 0)
{
v___x_855_ = v_x_801_;
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_vs_853_);
lean_inc(v_ks_852_);
lean_dec(v_x_801_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_873_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_ks_852_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_vs_853_);
v___x_858_ = v_reuseFailAlloc_872_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v_newNode_859_; uint8_t v___y_861_; size_t v___x_867_; uint8_t v___x_868_; 
v_newNode_859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_858_, v_x_804_, v_x_805_);
v___x_867_ = ((size_t)7ULL);
v___x_868_ = lean_usize_dec_le(v___x_867_, v_x_803_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_869_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_859_);
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
lean_dec(v___x_869_);
v___y_861_ = v___x_871_;
goto v___jp_860_;
}
else
{
v___y_861_ = v___x_868_;
goto v___jp_860_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v_ks_862_; lean_object* v_vs_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_ks_862_ = lean_ctor_get(v_newNode_859_, 0);
lean_inc_ref(v_ks_862_);
v_vs_863_ = lean_ctor_get(v_newNode_859_, 1);
lean_inc_ref(v_vs_863_);
lean_dec_ref(v_newNode_859_);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_803_, v_ks_862_, v_vs_863_, v___x_864_, v___x_865_);
lean_dec_ref(v_vs_863_);
lean_dec_ref(v_ks_862_);
return v___x_866_;
}
else
{
return v_newNode_859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_874_, lean_object* v_keys_875_, lean_object* v_vals_876_, lean_object* v_i_877_, lean_object* v_entries_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_keys_875_);
v___x_880_ = lean_nat_dec_lt(v_i_877_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec(v_i_877_);
return v_entries_878_;
}
else
{
lean_object* v_k_881_; lean_object* v_v_882_; uint64_t v___x_883_; size_t v_h_884_; size_t v___x_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v_h_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_k_881_ = lean_array_fget_borrowed(v_keys_875_, v_i_877_);
v_v_882_ = lean_array_fget_borrowed(v_vals_876_, v_i_877_);
v___x_883_ = l_Lean_instHashableMVarId_hash(v_k_881_);
v_h_884_ = lean_uint64_to_usize(v___x_883_);
v___x_885_ = ((size_t)5ULL);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_sub(v_depth_874_, v___x_887_);
v___x_889_ = lean_usize_mul(v___x_885_, v___x_888_);
v_h_890_ = lean_usize_shift_right(v_h_884_, v___x_889_);
v___x_891_ = lean_nat_add(v_i_877_, v___x_886_);
lean_dec(v_i_877_);
lean_inc(v_v_882_);
lean_inc(v_k_881_);
v___x_892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_878_, v_h_890_, v_depth_874_, v_k_881_, v_v_882_);
v_i_877_ = v___x_891_;
v_entries_878_ = v___x_892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_i_897_, lean_object* v_entries_898_){
_start:
{
size_t v_depth_boxed_899_; lean_object* v_res_900_; 
v_depth_boxed_899_ = lean_unbox_usize(v_depth_894_);
lean_dec(v_depth_894_);
v_res_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_899_, v_keys_895_, v_vals_896_, v_i_897_, v_entries_898_);
lean_dec_ref(v_vals_896_);
lean_dec_ref(v_keys_895_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
size_t v_x_1015__boxed_906_; size_t v_x_1016__boxed_907_; lean_object* v_res_908_; 
v_x_1015__boxed_906_ = lean_unbox_usize(v_x_902_);
lean_dec(v_x_902_);
v_x_1016__boxed_907_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_901_, v_x_1015__boxed_906_, v_x_1016__boxed_907_, v_x_904_, v_x_905_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
v___x_912_ = l_Lean_instHashableMVarId_hash(v_x_910_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = ((size_t)1ULL);
v___x_915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_909_, v___x_913_, v___x_914_, v_x_910_, v_x_911_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_916_, lean_object* v_val_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_mctx_921_; lean_object* v_cache_922_; lean_object* v_zetaDeltaFVarIds_923_; lean_object* v_postponed_924_; lean_object* v_diag_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_953_; 
v___x_920_ = lean_st_ref_take(v___y_918_);
v_mctx_921_ = lean_ctor_get(v___x_920_, 0);
v_cache_922_ = lean_ctor_get(v___x_920_, 1);
v_zetaDeltaFVarIds_923_ = lean_ctor_get(v___x_920_, 2);
v_postponed_924_ = lean_ctor_get(v___x_920_, 3);
v_diag_925_ = lean_ctor_get(v___x_920_, 4);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_953_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_953_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_diag_925_);
lean_inc(v_postponed_924_);
lean_inc(v_zetaDeltaFVarIds_923_);
lean_inc(v_cache_922_);
lean_inc(v_mctx_921_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_953_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_depth_929_; lean_object* v_levelAssignDepth_930_; lean_object* v_lmvarCounter_931_; lean_object* v_mvarCounter_932_; lean_object* v_lDecls_933_; lean_object* v_decls_934_; lean_object* v_userNames_935_; lean_object* v_lAssignment_936_; lean_object* v_eAssignment_937_; lean_object* v_dAssignment_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_952_; 
v_depth_929_ = lean_ctor_get(v_mctx_921_, 0);
v_levelAssignDepth_930_ = lean_ctor_get(v_mctx_921_, 1);
v_lmvarCounter_931_ = lean_ctor_get(v_mctx_921_, 2);
v_mvarCounter_932_ = lean_ctor_get(v_mctx_921_, 3);
v_lDecls_933_ = lean_ctor_get(v_mctx_921_, 4);
v_decls_934_ = lean_ctor_get(v_mctx_921_, 5);
v_userNames_935_ = lean_ctor_get(v_mctx_921_, 6);
v_lAssignment_936_ = lean_ctor_get(v_mctx_921_, 7);
v_eAssignment_937_ = lean_ctor_get(v_mctx_921_, 8);
v_dAssignment_938_ = lean_ctor_get(v_mctx_921_, 9);
v_isSharedCheck_952_ = !lean_is_exclusive(v_mctx_921_);
if (v_isSharedCheck_952_ == 0)
{
v___x_940_ = v_mctx_921_;
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_dAssignment_938_);
lean_inc(v_eAssignment_937_);
lean_inc(v_lAssignment_936_);
lean_inc(v_userNames_935_);
lean_inc(v_decls_934_);
lean_inc(v_lDecls_933_);
lean_inc(v_mvarCounter_932_);
lean_inc(v_lmvarCounter_931_);
lean_inc(v_levelAssignDepth_930_);
lean_inc(v_depth_929_);
lean_dec(v_mctx_921_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_952_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_937_, v_mvarId_916_, v_val_917_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 8, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_depth_929_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_levelAssignDepth_930_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_lmvarCounter_931_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_mvarCounter_932_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v_lDecls_933_);
lean_ctor_set(v_reuseFailAlloc_951_, 5, v_decls_934_);
lean_ctor_set(v_reuseFailAlloc_951_, 6, v_userNames_935_);
lean_ctor_set(v_reuseFailAlloc_951_, 7, v_lAssignment_936_);
lean_ctor_set(v_reuseFailAlloc_951_, 8, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 9, v_dAssignment_938_);
v___x_944_ = v_reuseFailAlloc_951_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_944_);
v___x_946_ = v___x_927_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_cache_922_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_zetaDeltaFVarIds_923_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_postponed_924_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_diag_925_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_st_ref_set(v___y_918_, v___x_946_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_954_, lean_object* v_val_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_954_, v_val_955_, v___y_956_);
lean_dec(v___y_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_959_, lean_object* v___x_960_, uint8_t v_synthetic_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc(v_mvarId_959_);
v___x_967_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_959_, v___x_960_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
lean_dec_ref(v___x_967_);
lean_inc(v_mvarId_959_);
v___x_968_ = l_Lean_MVarId_getType(v_mvarId_959_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; uint8_t v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = 1;
v___x_971_ = l_Lean_Meta_mkLabeledSorry(v_a_969_, v_synthetic_961_, v___x_970_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_959_, v_a_972_, v___y_963_);
return v___x_973_;
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v_mvarId_959_);
v_a_974_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_971_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v_mvarId_959_);
v_a_982_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_968_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_968_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_dec(v_mvarId_959_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_990_, lean_object* v___x_991_, lean_object* v_synthetic_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
uint8_t v_synthetic_boxed_998_; lean_object* v_res_999_; 
v_synthetic_boxed_998_ = lean_unbox(v_synthetic_992_);
v_res_999_ = l_Lean_MVarId_admit___lam__0(v_mvarId_990_, v___x_991_, v_synthetic_boxed_998_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1003_, uint8_t v_synthetic_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; 
v___x_1010_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1011_ = lean_box(v_synthetic_1004_);
lean_inc(v_mvarId_1003_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1012_, 0, v_mvarId_1003_);
lean_closure_set(v___f_1012_, 1, v___x_1010_);
lean_closure_set(v___f_1012_, 2, v___x_1011_);
v___x_1013_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1003_, v___f_1012_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1014_, lean_object* v_synthetic_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
uint8_t v_synthetic_boxed_1021_; lean_object* v_res_1022_; 
v_synthetic_boxed_1021_ = lean_unbox(v_synthetic_1015_);
v_res_1022_ = l_Lean_MVarId_admit(v_mvarId_1014_, v_synthetic_boxed_1021_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1023_, lean_object* v_val_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1023_, v_val_1024_, v___y_1026_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1031_, lean_object* v_val_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1031_, v_val_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1040_, v_x_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1044_, lean_object* v_x_1045_, size_t v_x_1046_, size_t v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
size_t v_x_1340__boxed_1057_; size_t v_x_1341__boxed_1058_; lean_object* v_res_1059_; 
v_x_1340__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_x_1341__boxed_1058_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_res_1059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1051_, v_x_1052_, v_x_1340__boxed_1057_, v_x_1341__boxed_1058_, v_x_1055_, v_x_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1060_, lean_object* v_n_1061_, lean_object* v_k_1062_, lean_object* v_v_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1061_, v_k_1062_, v_v_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1065_, size_t v_depth_1066_, lean_object* v_keys_1067_, lean_object* v_vals_1068_, lean_object* v_heq_1069_, lean_object* v_i_1070_, lean_object* v_entries_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1066_, v_keys_1067_, v_vals_1068_, v_i_1070_, v_entries_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_depth_1074_, lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_heq_1077_, lean_object* v_i_1078_, lean_object* v_entries_1079_){
_start:
{
size_t v_depth_boxed_1080_; lean_object* v_res_1081_; 
v_depth_boxed_1080_ = lean_unbox_usize(v_depth_1074_);
lean_dec(v_depth_1074_);
v_res_1081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1073_, v_depth_boxed_1080_, v_keys_1075_, v_vals_1076_, v_heq_1077_, v_i_1078_, v_entries_1079_);
lean_dec_ref(v_vals_1076_);
lean_dec_ref(v_keys_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1094_; 
lean_inc(v_mvarId_1088_);
v___x_1094_ = l_Lean_MVarId_getType(v_mvarId_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref(v___x_1094_);
v___x_1096_ = l_Lean_Expr_headBeta(v_a_1095_);
v___x_1097_ = l_Lean_MVarId_setType___redArg(v_mvarId_1088_, v___x_1096_, v_a_1090_);
return v___x_1097_;
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_mvarId_1088_);
v_a_1098_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1094_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1094_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_MVarId_headBetaType(v_mvarId_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1112_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
uint8_t v___x_1115_; 
v___x_1115_ = 0;
return v___x_1115_;
}
else
{
lean_object* v_key_1116_; lean_object* v_tail_1117_; uint8_t v___x_1118_; 
v_key_1116_ = lean_ctor_get(v_x_1114_, 0);
v_tail_1117_ = lean_ctor_get(v_x_1114_, 2);
v___x_1118_ = l_Lean_instBEqFVarId_beq(v_key_1116_, v_a_1113_);
if (v___x_1118_ == 0)
{
v_x_1114_ = v_tail_1117_;
goto _start;
}
else
{
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1120_, v_x_1121_);
lean_dec(v_x_1121_);
lean_dec(v_a_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1124_, lean_object* v_x_1125_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
return v_x_1125_;
}
else
{
lean_object* v_key_1126_; lean_object* v_value_1127_; lean_object* v_tail_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
v_key_1126_ = lean_ctor_get(v_x_1125_, 0);
v_value_1127_ = lean_ctor_get(v_x_1125_, 1);
v_tail_1128_ = lean_ctor_get(v_x_1125_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1130_ = v_x_1125_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_tail_1128_);
lean_inc(v_value_1127_);
lean_inc(v_key_1126_);
lean_dec(v_x_1125_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Lean_instBEqFVarId_beq(v_key_1126_, v_a_1124_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1124_, v_tail_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 2, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_key_1126_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_value_1127_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_del_object(v___x_1130_);
lean_dec(v_value_1127_);
lean_dec(v_key_1126_);
return v_tail_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1138_, v_x_1139_);
lean_dec(v_a_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_size_1143_; lean_object* v_buckets_1144_; lean_object* v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; uint64_t v_fold_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; uint64_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; size_t v___x_1157_; lean_object* v_bkt_1158_; uint8_t v___x_1159_; 
v_size_1143_ = lean_ctor_get(v_m_1141_, 0);
v_buckets_1144_ = lean_ctor_get(v_m_1141_, 1);
v___x_1145_ = lean_array_get_size(v_buckets_1144_);
v___x_1146_ = l_Lean_instHashableFVarId_hash(v_a_1142_);
v___x_1147_ = 32ULL;
v___x_1148_ = lean_uint64_shift_right(v___x_1146_, v___x_1147_);
v_fold_1149_ = lean_uint64_xor(v___x_1146_, v___x_1148_);
v___x_1150_ = 16ULL;
v___x_1151_ = lean_uint64_shift_right(v_fold_1149_, v___x_1150_);
v___x_1152_ = lean_uint64_xor(v_fold_1149_, v___x_1151_);
v___x_1153_ = lean_uint64_to_usize(v___x_1152_);
v___x_1154_ = lean_usize_of_nat(v___x_1145_);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_sub(v___x_1154_, v___x_1155_);
v___x_1157_ = lean_usize_land(v___x_1153_, v___x_1156_);
v_bkt_1158_ = lean_array_uget_borrowed(v_buckets_1144_, v___x_1157_);
v___x_1159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1142_, v_bkt_1158_);
if (v___x_1159_ == 0)
{
return v_m_1141_;
}
else
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_bkt_1158_);
lean_inc_ref(v_buckets_1144_);
lean_inc(v_size_1143_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_m_1141_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1173_ = lean_ctor_get(v_m_1141_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_m_1141_, 0);
lean_dec(v_unused_1174_);
v___x_1161_ = v_m_1141_;
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v_m_1141_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1172_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v_buckets_x27_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1163_ = lean_box(0);
v_buckets_x27_1164_ = lean_array_uset(v_buckets_1144_, v___x_1157_, v___x_1163_);
v___x_1165_ = lean_unsigned_to_nat(1u);
v___x_1166_ = lean_nat_sub(v_size_1143_, v___x_1165_);
lean_dec(v_size_1143_);
v___x_1167_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1142_, v_bkt_1158_);
v___x_1168_ = lean_array_uset(v_buckets_x27_1164_, v___x_1157_, v___x_1167_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1168_);
lean_ctor_set(v___x_1161_, 0, v___x_1166_);
v___x_1170_ = v___x_1161_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1175_, v_a_1176_);
lean_dec(v_a_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1185_ = lean_st_ref_take(v___y_1179_);
v___x_1186_ = l_Lean_Expr_fvarId_x21(v_e_1178_);
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1185_, v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_st_ref_set(v___y_1179_, v___x_1187_);
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_e_1191_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_st_ref_get(v___y_1200_);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
return v_res_1215_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; 
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = ((size_t)8192ULL);
v___x_1218_ = lean_usize_sub(v___x_1217_, v___x_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v_visited_1223_; size_t v___x_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; size_t v___x_1228_; uint8_t v___x_1229_; 
v___x_1222_ = lean_st_ref_get(v_a_1220_);
v_visited_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_visited_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = lean_ptr_addr(v_e_1219_);
v___x_1225_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_1226_ = lean_usize_mod(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_array_uget(v_visited_1223_, v___x_1226_);
lean_dec_ref(v_visited_1223_);
v___x_1228_ = lean_ptr_addr(v___x_1227_);
lean_dec(v___x_1227_);
v___x_1229_ = lean_usize_dec_eq(v___x_1228_, v___x_1224_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v_visited_1231_; lean_object* v_checked_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v___x_1230_ = lean_st_ref_take(v_a_1220_);
v_visited_1231_ = lean_ctor_get(v___x_1230_, 0);
v_checked_1232_ = lean_ctor_get(v___x_1230_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1234_ = v___x_1230_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_checked_1232_);
lean_inc(v_visited_1231_);
lean_dec(v___x_1230_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_array_uset(v_visited_1231_, v___x_1226_, v_e_1219_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_checked_1232_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_st_ref_set(v_a_1220_, v___x_1238_);
v___x_1240_ = lean_box(v___x_1229_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_e_1219_);
v___x_1244_ = lean_box(v___x_1229_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1246_, v_a_1247_);
lean_dec(v_a_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
else
{
lean_object* v_key_1253_; lean_object* v_tail_1254_; uint8_t v___x_1255_; 
v_key_1253_ = lean_ctor_get(v_x_1251_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
v___x_1255_ = lean_expr_eqv(v_key_1253_, v_a_1250_);
if (v___x_1255_ == 0)
{
v_x_1251_ = v_tail_1254_;
goto _start;
}
else
{
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec_ref(v_a_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
return v_x_1261_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1288_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1267_ = v_x_1262_;
v_isShared_1268_ = v_isSharedCheck_1288_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_tail_1265_);
lean_inc(v_value_1264_);
lean_inc(v_key_1263_);
lean_dec(v_x_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1288_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; uint64_t v_fold_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1269_ = lean_array_get_size(v_x_1261_);
v___x_1270_ = l_Lean_Expr_hash(v_key_1263_);
v___x_1271_ = 32ULL;
v___x_1272_ = lean_uint64_shift_right(v___x_1270_, v___x_1271_);
v_fold_1273_ = lean_uint64_xor(v___x_1270_, v___x_1272_);
v___x_1274_ = 16ULL;
v___x_1275_ = lean_uint64_shift_right(v_fold_1273_, v___x_1274_);
v___x_1276_ = lean_uint64_xor(v_fold_1273_, v___x_1275_);
v___x_1277_ = lean_uint64_to_usize(v___x_1276_);
v___x_1278_ = lean_usize_of_nat(v___x_1269_);
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_sub(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_usize_land(v___x_1277_, v___x_1280_);
v___x_1282_ = lean_array_uget_borrowed(v_x_1261_, v___x_1281_);
lean_inc(v___x_1282_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1282_);
v___x_1284_ = v___x_1267_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_key_1263_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_value_1264_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_array_uset(v_x_1261_, v___x_1281_, v___x_1284_);
v_x_1261_ = v___x_1285_;
v_x_1262_ = v_tail_1265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1289_, lean_object* v_source_1290_, lean_object* v_target_1291_){
_start:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_array_get_size(v_source_1290_);
v___x_1293_ = lean_nat_dec_lt(v_i_1289_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_source_1290_);
lean_dec(v_i_1289_);
return v_target_1291_;
}
else
{
lean_object* v_es_1294_; lean_object* v___x_1295_; lean_object* v_source_1296_; lean_object* v_target_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_es_1294_ = lean_array_fget(v_source_1290_, v_i_1289_);
v___x_1295_ = lean_box(0);
v_source_1296_ = lean_array_fset(v_source_1290_, v_i_1289_, v___x_1295_);
v_target_1297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1291_, v_es_1294_);
v___x_1298_ = lean_unsigned_to_nat(1u);
v___x_1299_ = lean_nat_add(v_i_1289_, v___x_1298_);
lean_dec(v_i_1289_);
v_i_1289_ = v___x_1299_;
v_source_1290_ = v_source_1296_;
v_target_1291_ = v_target_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_nbuckets_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1302_ = lean_array_get_size(v_data_1301_);
v___x_1303_ = lean_unsigned_to_nat(2u);
v_nbuckets_1304_ = lean_nat_mul(v___x_1302_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_mk_array(v_nbuckets_1304_, v___x_1306_);
v___x_1308_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1305_, v_data_1301_, v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1309_, lean_object* v_a_1310_, lean_object* v_b_1311_){
_start:
{
lean_object* v_size_1312_; lean_object* v_buckets_1313_; lean_object* v___x_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v_fold_1318_; uint64_t v___x_1319_; uint64_t v___x_1320_; uint64_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v_bkt_1327_; uint8_t v___x_1328_; 
v_size_1312_ = lean_ctor_get(v_m_1309_, 0);
v_buckets_1313_ = lean_ctor_get(v_m_1309_, 1);
v___x_1314_ = lean_array_get_size(v_buckets_1313_);
v___x_1315_ = l_Lean_Expr_hash(v_a_1310_);
v___x_1316_ = 32ULL;
v___x_1317_ = lean_uint64_shift_right(v___x_1315_, v___x_1316_);
v_fold_1318_ = lean_uint64_xor(v___x_1315_, v___x_1317_);
v___x_1319_ = 16ULL;
v___x_1320_ = lean_uint64_shift_right(v_fold_1318_, v___x_1319_);
v___x_1321_ = lean_uint64_xor(v_fold_1318_, v___x_1320_);
v___x_1322_ = lean_uint64_to_usize(v___x_1321_);
v___x_1323_ = lean_usize_of_nat(v___x_1314_);
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_sub(v___x_1323_, v___x_1324_);
v___x_1326_ = lean_usize_land(v___x_1322_, v___x_1325_);
v_bkt_1327_ = lean_array_uget_borrowed(v_buckets_1313_, v___x_1326_);
v___x_1328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1310_, v_bkt_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1349_; 
lean_inc_ref(v_buckets_1313_);
lean_inc(v_size_1312_);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_m_1309_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1350_ = lean_ctor_get(v_m_1309_, 1);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_m_1309_, 0);
lean_dec(v_unused_1351_);
v___x_1330_ = v_m_1309_;
v_isShared_1331_ = v_isSharedCheck_1349_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v_m_1309_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1349_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v_size_x27_1333_; lean_object* v___x_1334_; lean_object* v_buckets_x27_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v_size_x27_1333_ = lean_nat_add(v_size_1312_, v___x_1332_);
lean_dec(v_size_1312_);
lean_inc(v_bkt_1327_);
v___x_1334_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1310_);
lean_ctor_set(v___x_1334_, 1, v_b_1311_);
lean_ctor_set(v___x_1334_, 2, v_bkt_1327_);
v_buckets_x27_1335_ = lean_array_uset(v_buckets_1313_, v___x_1326_, v___x_1334_);
v___x_1336_ = lean_unsigned_to_nat(4u);
v___x_1337_ = lean_nat_mul(v_size_x27_1333_, v___x_1336_);
v___x_1338_ = lean_unsigned_to_nat(3u);
v___x_1339_ = lean_nat_div(v___x_1337_, v___x_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_array_get_size(v_buckets_x27_1335_);
v___x_1341_ = lean_nat_dec_le(v___x_1339_, v___x_1340_);
lean_dec(v___x_1339_);
if (v___x_1341_ == 0)
{
lean_object* v_val_1342_; lean_object* v___x_1344_; 
v_val_1342_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1335_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v_val_1342_);
lean_ctor_set(v___x_1330_, 0, v_size_x27_1333_);
v___x_1344_ = v___x_1330_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_size_x27_1333_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_val_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_object* v___x_1347_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v_buckets_x27_1335_);
lean_ctor_set(v___x_1330_, 0, v_size_x27_1333_);
v___x_1347_ = v___x_1330_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_size_x27_1333_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_buckets_x27_1335_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_dec(v_b_1311_);
lean_dec_ref(v_a_1310_);
return v_m_1309_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_buckets_1354_; lean_object* v___x_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v_fold_1359_; uint64_t v___x_1360_; uint64_t v___x_1361_; uint64_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_buckets_1354_ = lean_ctor_get(v_m_1352_, 1);
v___x_1355_ = lean_array_get_size(v_buckets_1354_);
v___x_1356_ = l_Lean_Expr_hash(v_a_1353_);
v___x_1357_ = 32ULL;
v___x_1358_ = lean_uint64_shift_right(v___x_1356_, v___x_1357_);
v_fold_1359_ = lean_uint64_xor(v___x_1356_, v___x_1358_);
v___x_1360_ = 16ULL;
v___x_1361_ = lean_uint64_shift_right(v_fold_1359_, v___x_1360_);
v___x_1362_ = lean_uint64_xor(v_fold_1359_, v___x_1361_);
v___x_1363_ = lean_uint64_to_usize(v___x_1362_);
v___x_1364_ = lean_usize_of_nat(v___x_1355_);
v___x_1365_ = ((size_t)1ULL);
v___x_1366_ = lean_usize_sub(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_usize_land(v___x_1363_, v___x_1366_);
v___x_1368_ = lean_array_uget_borrowed(v_buckets_1354_, v___x_1367_);
v___x_1369_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1353_, v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1370_, lean_object* v_a_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1370_, v_a_1371_);
lean_dec_ref(v_a_1371_);
lean_dec_ref(v_m_1370_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_checked_1378_; uint8_t v___x_1379_; 
v___x_1377_ = lean_st_ref_get(v_a_1375_);
v_checked_1378_ = lean_ctor_get(v___x_1377_, 1);
lean_inc_ref(v_checked_1378_);
lean_dec(v___x_1377_);
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1378_, v_e_1374_);
lean_dec_ref(v_checked_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v_visited_1381_; lean_object* v_checked_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1394_; 
v___x_1380_ = lean_st_ref_take(v_a_1375_);
v_visited_1381_ = lean_ctor_get(v___x_1380_, 0);
v_checked_1382_ = lean_ctor_get(v___x_1380_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1384_ = v___x_1380_;
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_checked_1382_);
lean_inc(v_visited_1381_);
lean_dec(v___x_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1394_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1382_, v_e_1374_, v___x_1386_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_visited_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_st_ref_set(v_a_1375_, v___x_1389_);
v___x_1391_ = lean_box(v___x_1379_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v_e_1374_);
v___x_1395_ = lean_box(v___x_1379_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1397_, lean_object* v_a_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1397_, v_a_1398_);
lean_dec(v_a_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1401_, lean_object* v_f_1402_, uint8_t v_stopWhenVisited_1403_, lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v_d_1418_; lean_object* v_b_1419_; lean_object* v___y_1420_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1450_; 
lean_inc_ref(v_e_1404_);
v___x_1450_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1483_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1483_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1483_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_unbox(v_a_1451_);
lean_dec(v_a_1451_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; uint8_t v___x_1457_; 
lean_del_object(v___x_1453_);
lean_inc_ref(v_p_1401_);
lean_inc_ref(v_e_1404_);
v___x_1456_ = lean_apply_1(v_p_1401_, v_e_1404_);
v___x_1457_ = lean_unbox(v___x_1456_);
if (v___x_1457_ == 0)
{
v___y_1424_ = v_a_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
v___y_1429_ = v___y_1410_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1458_; 
lean_inc_ref(v_e_1404_);
v___x_1458_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; uint8_t v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = lean_unbox(v_a_1459_);
lean_dec(v_a_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_inc_ref(v_f_1402_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v_e_1404_);
v___x_1461_ = lean_apply_7(v_f_1402_, v_e_1404_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v___x_1461_, 0);
lean_dec(v_unused_1470_);
v___x_1463_ = v___x_1461_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v___x_1461_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (v_stopWhenVisited_1403_ == 0)
{
lean_del_object(v___x_1463_);
v___y_1424_ = v_a_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
v___y_1429_ = v___y_1410_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
v___x_1465_ = lean_box(0);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
return v___x_1461_;
}
}
else
{
v___y_1424_ = v_a_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
v___y_1427_ = v___y_1408_;
v___y_1428_ = v___y_1409_;
v___y_1429_ = v___y_1410_;
goto v___jp_1423_;
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
v_a_1471_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1458_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1458_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
v___x_1479_ = lean_box(0);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1479_);
v___x_1481_ = v___x_1453_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
v_a_1484_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1450_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1450_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
v___jp_1412_:
{
lean_object* v___x_1421_; 
lean_inc_ref(v_f_1402_);
lean_inc_ref(v_p_1401_);
v___x_1421_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1401_, v_f_1402_, v_stopWhenVisited_1403_, v_d_1418_, v___y_1420_, v___y_1417_, v___y_1414_, v___y_1416_, v___y_1413_, v___y_1415_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v___x_1421_);
v_e_1404_ = v_b_1419_;
v_a_1405_ = v___y_1420_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1414_;
v___y_1408_ = v___y_1416_;
v___y_1409_ = v___y_1413_;
v___y_1410_ = v___y_1415_;
goto _start;
}
else
{
lean_dec_ref(v_b_1419_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
return v___x_1421_;
}
}
v___jp_1423_:
{
switch(lean_obj_tag(v_e_1404_))
{
case 7:
{
lean_object* v_binderType_1430_; lean_object* v_body_1431_; 
v_binderType_1430_ = lean_ctor_get(v_e_1404_, 1);
lean_inc_ref(v_binderType_1430_);
v_body_1431_ = lean_ctor_get(v_e_1404_, 2);
lean_inc_ref(v_body_1431_);
lean_dec_ref(v_e_1404_);
v___y_1413_ = v___y_1428_;
v___y_1414_ = v___y_1426_;
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1425_;
v_d_1418_ = v_binderType_1430_;
v_b_1419_ = v_body_1431_;
v___y_1420_ = v___y_1424_;
goto v___jp_1412_;
}
case 6:
{
lean_object* v_binderType_1432_; lean_object* v_body_1433_; 
v_binderType_1432_ = lean_ctor_get(v_e_1404_, 1);
lean_inc_ref(v_binderType_1432_);
v_body_1433_ = lean_ctor_get(v_e_1404_, 2);
lean_inc_ref(v_body_1433_);
lean_dec_ref(v_e_1404_);
v___y_1413_ = v___y_1428_;
v___y_1414_ = v___y_1426_;
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1425_;
v_d_1418_ = v_binderType_1432_;
v_b_1419_ = v_body_1433_;
v___y_1420_ = v___y_1424_;
goto v___jp_1412_;
}
case 8:
{
lean_object* v_type_1434_; lean_object* v_value_1435_; lean_object* v_body_1436_; lean_object* v___x_1437_; 
v_type_1434_ = lean_ctor_get(v_e_1404_, 1);
lean_inc_ref(v_type_1434_);
v_value_1435_ = lean_ctor_get(v_e_1404_, 2);
lean_inc_ref(v_value_1435_);
v_body_1436_ = lean_ctor_get(v_e_1404_, 3);
lean_inc_ref(v_body_1436_);
lean_dec_ref(v_e_1404_);
lean_inc_ref(v_f_1402_);
lean_inc_ref(v_p_1401_);
v___x_1437_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1401_, v_f_1402_, v_stopWhenVisited_1403_, v_type_1434_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref(v___x_1437_);
lean_inc_ref(v_f_1402_);
lean_inc_ref(v_p_1401_);
v___x_1438_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1401_, v_f_1402_, v_stopWhenVisited_1403_, v_value_1435_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref(v___x_1438_);
v_e_1404_ = v_body_1436_;
v_a_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
goto _start;
}
else
{
lean_dec_ref(v_body_1436_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
return v___x_1438_;
}
}
else
{
lean_dec_ref(v_body_1436_);
lean_dec_ref(v_value_1435_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
return v___x_1437_;
}
}
case 5:
{
lean_object* v_fn_1440_; lean_object* v_arg_1441_; lean_object* v___x_1442_; 
v_fn_1440_ = lean_ctor_get(v_e_1404_, 0);
lean_inc_ref(v_fn_1440_);
v_arg_1441_ = lean_ctor_get(v_e_1404_, 1);
lean_inc_ref(v_arg_1441_);
lean_dec_ref(v_e_1404_);
lean_inc_ref(v_f_1402_);
lean_inc_ref(v_p_1401_);
v___x_1442_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1401_, v_f_1402_, v_stopWhenVisited_1403_, v_fn_1440_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref(v___x_1442_);
v_e_1404_ = v_arg_1441_;
v_a_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1441_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
return v___x_1442_;
}
}
case 10:
{
lean_object* v_expr_1444_; 
v_expr_1444_ = lean_ctor_get(v_e_1404_, 1);
lean_inc_ref(v_expr_1444_);
lean_dec_ref(v_e_1404_);
v_e_1404_ = v_expr_1444_;
v_a_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
goto _start;
}
case 11:
{
lean_object* v_struct_1446_; 
v_struct_1446_ = lean_ctor_get(v_e_1404_, 2);
lean_inc_ref(v_struct_1446_);
lean_dec_ref(v_e_1404_);
v_e_1404_ = v_struct_1446_;
v_a_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
goto _start;
}
default: 
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_f_1402_);
lean_dec_ref(v_p_1401_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1492_, lean_object* v_f_1493_, lean_object* v_stopWhenVisited_1494_, lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1503_; lean_object* v_res_1504_; 
v_stopWhenVisited_boxed_1503_ = lean_unbox(v_stopWhenVisited_1494_);
v_res_1504_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1492_, v_f_1493_, v_stopWhenVisited_boxed_1503_, v_e_1495_, v_a_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v_a_1496_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1505_, lean_object* v_f_1506_, lean_object* v_e_1507_, uint8_t v_stopWhenVisited_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = l_Lean_ForEachExprWhere_initCache;
v___x_1516_ = lean_st_mk_ref(v___x_1515_);
v___x_1517_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1505_, v_f_1506_, v_stopWhenVisited_1508_, v_e_1507_, v___x_1516_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1526_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1526_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1522_ = lean_st_ref_get(v___x_1516_);
lean_dec(v___x_1516_);
lean_dec(v___x_1522_);
if (v_isShared_1521_ == 0)
{
v___x_1524_ = v___x_1520_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1518_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
else
{
lean_dec(v___x_1516_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1527_, lean_object* v_f_1528_, lean_object* v_e_1529_, lean_object* v_stopWhenVisited_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1537_; lean_object* v_res_1538_; 
v_stopWhenVisited_boxed_1537_ = lean_unbox(v_stopWhenVisited_1530_);
v_res_1538_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1527_, v_f_1528_, v_e_1529_, v_stopWhenVisited_boxed_1537_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1540_, lean_object* v___f_1541_, uint8_t v___x_1542_, lean_object* v_e_1543_, lean_object* v_candidates_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1543_, v___y_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; lean_object* v___y_1554_; uint8_t v___x_1564_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = lean_st_mk_ref(v_candidates_1544_);
v___x_1564_ = l_Lean_Expr_hasFVar(v_a_1551_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1551_);
lean_dec_ref(v___f_1541_);
v___x_1565_ = lean_box(0);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___x_1552_);
v___x_1566_ = lean_apply_7(v___f_1540_, v___x_1565_, v___x_1552_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, lean_box(0));
v___y_1554_ = v___x_1566_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1568_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1567_, v___f_1541_, v_a_1551_, v___x_1542_, v___x_1552_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___x_1552_);
v___x_1570_ = lean_apply_7(v___f_1540_, v_a_1569_, v___x_1552_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, lean_box(0));
v___y_1554_ = v___x_1570_;
goto v___jp_1553_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v___x_1552_);
lean_dec_ref(v___f_1540_);
v_a_1571_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1568_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1568_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
v___jp_1553_:
{
if (lean_obj_tag(v___y_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1563_; 
v_a_1555_ = lean_ctor_get(v___y_1554_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___y_1554_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1557_ = v___y_1554_;
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___y_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_st_ref_get(v___x_1552_);
lean_dec(v___x_1552_);
lean_dec(v___x_1559_);
if (v_isShared_1558_ == 0)
{
v___x_1561_ = v___x_1557_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1555_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_dec(v___x_1552_);
return v___y_1554_;
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_candidates_1544_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v___f_1540_);
v_a_1579_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1550_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1550_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1587_, lean_object* v___f_1588_, lean_object* v___x_1589_, lean_object* v_e_1590_, lean_object* v_candidates_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_17596__boxed_1597_; lean_object* v_res_1598_; 
v___x_17596__boxed_1597_ = lean_unbox(v___x_1589_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1587_, v___f_1588_, v___x_17596__boxed_1597_, v_e_1590_, v_candidates_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_e_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = lean_st_ref_take(v___y_1600_);
v___x_1607_ = l_Lean_Expr_fvarId_x21(v_e_1599_);
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1606_, v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_st_ref_set(v___y_1600_, v___x_1608_);
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_e_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v_e_1612_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_____r_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_st_ref_get(v___y_1621_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_____r_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
return v_x_1637_;
}
else
{
lean_object* v_key_1639_; lean_object* v_value_1640_; lean_object* v_tail_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1664_; 
v_key_1639_ = lean_ctor_get(v_x_1638_, 0);
v_value_1640_ = lean_ctor_get(v_x_1638_, 1);
v_tail_1641_ = lean_ctor_get(v_x_1638_, 2);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1638_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1643_ = v_x_1638_;
v_isShared_1644_ = v_isSharedCheck_1664_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_tail_1641_);
lean_inc(v_value_1640_);
lean_inc(v_key_1639_);
lean_dec(v_x_1638_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1664_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; uint64_t v_fold_1649_; uint64_t v___x_1650_; uint64_t v___x_1651_; uint64_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1645_ = lean_array_get_size(v_x_1637_);
v___x_1646_ = l_Lean_instHashableFVarId_hash(v_key_1639_);
v___x_1647_ = 32ULL;
v___x_1648_ = lean_uint64_shift_right(v___x_1646_, v___x_1647_);
v_fold_1649_ = lean_uint64_xor(v___x_1646_, v___x_1648_);
v___x_1650_ = 16ULL;
v___x_1651_ = lean_uint64_shift_right(v_fold_1649_, v___x_1650_);
v___x_1652_ = lean_uint64_xor(v_fold_1649_, v___x_1651_);
v___x_1653_ = lean_uint64_to_usize(v___x_1652_);
v___x_1654_ = lean_usize_of_nat(v___x_1645_);
v___x_1655_ = ((size_t)1ULL);
v___x_1656_ = lean_usize_sub(v___x_1654_, v___x_1655_);
v___x_1657_ = lean_usize_land(v___x_1653_, v___x_1656_);
v___x_1658_ = lean_array_uget_borrowed(v_x_1637_, v___x_1657_);
lean_inc(v___x_1658_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 2, v___x_1658_);
v___x_1660_ = v___x_1643_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_key_1639_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_value_1640_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_array_uset(v_x_1637_, v___x_1657_, v___x_1660_);
v_x_1637_ = v___x_1661_;
v_x_1638_ = v_tail_1641_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1665_, lean_object* v_source_1666_, lean_object* v_target_1667_){
_start:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_array_get_size(v_source_1666_);
v___x_1669_ = lean_nat_dec_lt(v_i_1665_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec_ref(v_source_1666_);
lean_dec(v_i_1665_);
return v_target_1667_;
}
else
{
lean_object* v_es_1670_; lean_object* v___x_1671_; lean_object* v_source_1672_; lean_object* v_target_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_es_1670_ = lean_array_fget(v_source_1666_, v_i_1665_);
v___x_1671_ = lean_box(0);
v_source_1672_ = lean_array_fset(v_source_1666_, v_i_1665_, v___x_1671_);
v_target_1673_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1667_, v_es_1670_);
v___x_1674_ = lean_unsigned_to_nat(1u);
v___x_1675_ = lean_nat_add(v_i_1665_, v___x_1674_);
lean_dec(v_i_1665_);
v_i_1665_ = v___x_1675_;
v_source_1666_ = v_source_1672_;
v_target_1667_ = v_target_1673_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_nbuckets_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1678_ = lean_array_get_size(v_data_1677_);
v___x_1679_ = lean_unsigned_to_nat(2u);
v_nbuckets_1680_ = lean_nat_mul(v___x_1678_, v___x_1679_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_box(0);
v___x_1683_ = lean_mk_array(v_nbuckets_1680_, v___x_1682_);
v___x_1684_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1681_, v_data_1677_, v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1685_, lean_object* v_a_1686_, lean_object* v_b_1687_){
_start:
{
lean_object* v_size_1688_; lean_object* v_buckets_1689_; lean_object* v___x_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v_fold_1694_; uint64_t v___x_1695_; uint64_t v___x_1696_; uint64_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v_bkt_1703_; uint8_t v___x_1704_; 
v_size_1688_ = lean_ctor_get(v_m_1685_, 0);
v_buckets_1689_ = lean_ctor_get(v_m_1685_, 1);
v___x_1690_ = lean_array_get_size(v_buckets_1689_);
v___x_1691_ = l_Lean_instHashableFVarId_hash(v_a_1686_);
v___x_1692_ = 32ULL;
v___x_1693_ = lean_uint64_shift_right(v___x_1691_, v___x_1692_);
v_fold_1694_ = lean_uint64_xor(v___x_1691_, v___x_1693_);
v___x_1695_ = 16ULL;
v___x_1696_ = lean_uint64_shift_right(v_fold_1694_, v___x_1695_);
v___x_1697_ = lean_uint64_xor(v_fold_1694_, v___x_1696_);
v___x_1698_ = lean_uint64_to_usize(v___x_1697_);
v___x_1699_ = lean_usize_of_nat(v___x_1690_);
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_sub(v___x_1699_, v___x_1700_);
v___x_1702_ = lean_usize_land(v___x_1698_, v___x_1701_);
v_bkt_1703_ = lean_array_uget_borrowed(v_buckets_1689_, v___x_1702_);
v___x_1704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1686_, v_bkt_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1725_; 
lean_inc_ref(v_buckets_1689_);
lean_inc(v_size_1688_);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_m_1685_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; lean_object* v_unused_1727_; 
v_unused_1726_ = lean_ctor_get(v_m_1685_, 1);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v_m_1685_, 0);
lean_dec(v_unused_1727_);
v___x_1706_ = v_m_1685_;
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
else
{
lean_dec(v_m_1685_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1725_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v_size_x27_1709_; lean_object* v___x_1710_; lean_object* v_buckets_x27_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1708_ = lean_unsigned_to_nat(1u);
v_size_x27_1709_ = lean_nat_add(v_size_1688_, v___x_1708_);
lean_dec(v_size_1688_);
lean_inc(v_bkt_1703_);
v___x_1710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1710_, 0, v_a_1686_);
lean_ctor_set(v___x_1710_, 1, v_b_1687_);
lean_ctor_set(v___x_1710_, 2, v_bkt_1703_);
v_buckets_x27_1711_ = lean_array_uset(v_buckets_1689_, v___x_1702_, v___x_1710_);
v___x_1712_ = lean_unsigned_to_nat(4u);
v___x_1713_ = lean_nat_mul(v_size_x27_1709_, v___x_1712_);
v___x_1714_ = lean_unsigned_to_nat(3u);
v___x_1715_ = lean_nat_div(v___x_1713_, v___x_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_array_get_size(v_buckets_x27_1711_);
v___x_1717_ = lean_nat_dec_le(v___x_1715_, v___x_1716_);
lean_dec(v___x_1715_);
if (v___x_1717_ == 0)
{
lean_object* v_val_1718_; lean_object* v___x_1720_; 
v_val_1718_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1711_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_val_1718_);
lean_ctor_set(v___x_1706_, 0, v_size_x27_1709_);
v___x_1720_ = v___x_1706_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_size_x27_1709_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_val_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
else
{
lean_object* v___x_1723_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v_buckets_x27_1711_);
lean_ctor_set(v___x_1706_, 0, v_size_x27_1709_);
v___x_1723_ = v___x_1706_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_size_x27_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_buckets_x27_1711_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_dec(v_b_1687_);
lean_dec(v_a_1686_);
return v_m_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1730_, size_t v_sz_1731_, size_t v_i_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_lt(v_i_1732_, v_sz_1731_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v_b_1733_);
return v___x_1740_;
}
else
{
lean_object* v_snd_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1805_; 
v_snd_1741_ = lean_ctor_get(v_b_1733_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_b_1733_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v_b_1733_, 0);
lean_dec(v_unused_1806_);
v___x_1743_ = v_b_1733_;
v_isShared_1744_ = v_isSharedCheck_1805_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snd_1741_);
lean_dec(v_b_1733_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1805_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v_a_1747_; lean_object* v_a_1754_; 
v___x_1745_ = lean_box(0);
v_a_1754_ = lean_array_uget_borrowed(v_as_1730_, v_i_1732_);
if (lean_obj_tag(v_a_1754_) == 0)
{
v_a_1747_ = v_snd_1741_;
goto v___jp_1746_;
}
else
{
lean_object* v_val_1755_; lean_object* v___y_1757_; uint8_t v___x_1761_; 
v_val_1755_ = lean_ctor_get(v_a_1754_, 0);
v___x_1761_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1755_);
if (v___x_1761_ == 0)
{
lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v_candidates_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___x_1783_; 
v___f_1762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1764_ = l_Lean_LocalDecl_type(v_val_1755_);
lean_inc_ref(v___x_1764_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1763_, v___f_1762_, v___x_1761_, v___x_1764_, v_snd_1741_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = l_Lean_LocalDecl_value_x3f(v_val_1755_, v___x_1761_);
if (lean_obj_tag(v___x_1785_) == 0)
{
v_candidates_1766_ = v_a_1784_;
v___y_1767_ = v___y_1734_;
v___y_1768_ = v___y_1735_;
v___y_1769_ = v___y_1736_;
v___y_1770_ = v___y_1737_;
goto v___jp_1765_;
}
else
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
v_val_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref(v___x_1785_);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1763_, v___f_1762_, v___x_1761_, v_val_1786_, v_a_1784_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1787_);
v_candidates_1766_ = v_a_1788_;
v___y_1767_ = v___y_1734_;
v___y_1768_ = v___y_1735_;
v___y_1769_ = v___y_1736_;
v___y_1770_ = v___y_1737_;
goto v___jp_1765_;
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___x_1764_);
lean_del_object(v___x_1743_);
v_a_1789_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1787_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v___x_1764_);
lean_del_object(v___x_1743_);
v_a_1797_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1783_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1783_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
v___jp_1765_:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_isProp(v___x_1764_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; uint8_t v___x_1773_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = lean_unbox(v_a_1772_);
lean_dec(v_a_1772_);
if (v___x_1773_ == 0)
{
v_a_1747_ = v_candidates_1766_;
goto v___jp_1746_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = l_Lean_LocalDecl_hasValue(v_val_1755_, v___x_1761_);
if (v___x_1774_ == 0)
{
v___y_1757_ = v_candidates_1766_;
goto v___jp_1756_;
}
else
{
if (v___x_1761_ == 0)
{
v_a_1747_ = v_candidates_1766_;
goto v___jp_1746_;
}
else
{
v___y_1757_ = v_candidates_1766_;
goto v___jp_1756_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v_candidates_1766_);
lean_del_object(v___x_1743_);
v_a_1775_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1771_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1771_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
else
{
v_a_1747_ = v_snd_1741_;
goto v___jp_1746_;
}
v___jp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = l_Lean_LocalDecl_fvarId(v_val_1755_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1757_, v___x_1758_, v___x_1759_);
v_a_1747_ = v___x_1760_;
goto v___jp_1746_;
}
}
v___jp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v_a_1747_);
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1745_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_a_1747_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
size_t v___x_1750_; size_t v___x_1751_; 
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1732_, v___x_1750_);
v_i_1732_ = v___x_1751_;
v_b_1733_ = v___x_1749_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1807_, lean_object* v_sz_1808_, lean_object* v_i_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
size_t v_sz_boxed_1816_; size_t v_i_boxed_1817_; lean_object* v_res_1818_; 
v_sz_boxed_1816_ = lean_unbox_usize(v_sz_1808_);
lean_dec(v_sz_1808_);
v_i_boxed_1817_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1807_, v_sz_boxed_1816_, v_i_boxed_1817_, v_b_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_as_1807_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1819_, size_t v_sz_1820_, size_t v_i_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_usize_dec_lt(v_i_1821_, v_sz_1820_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_b_1822_);
return v___x_1829_;
}
else
{
lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1894_; 
v_snd_1830_ = lean_ctor_get(v_b_1822_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_b_1822_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; 
v_unused_1895_ = lean_ctor_get(v_b_1822_, 0);
lean_dec(v_unused_1895_);
v___x_1832_ = v_b_1822_;
v_isShared_1833_ = v_isSharedCheck_1894_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_dec(v_b_1822_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1894_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v_a_1836_; lean_object* v_a_1843_; 
v___x_1834_ = lean_box(0);
v_a_1843_ = lean_array_uget_borrowed(v_as_1819_, v_i_1821_);
if (lean_obj_tag(v_a_1843_) == 0)
{
v_a_1836_ = v_snd_1830_;
goto v___jp_1835_;
}
else
{
lean_object* v_val_1844_; lean_object* v___y_1846_; uint8_t v___x_1850_; 
v_val_1844_ = lean_ctor_get(v_a_1843_, 0);
v___x_1850_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1844_);
if (v___x_1850_ == 0)
{
lean_object* v___f_1851_; lean_object* v___f_1852_; lean_object* v___x_1853_; lean_object* v_candidates_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___x_1872_; 
v___f_1851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1853_ = l_Lean_LocalDecl_type(v_val_1844_);
lean_inc_ref(v___x_1853_);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1852_, v___f_1851_, v___x_1850_, v___x_1853_, v_snd_1830_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l_Lean_LocalDecl_value_x3f(v_val_1844_, v___x_1850_);
if (lean_obj_tag(v___x_1874_) == 0)
{
v_candidates_1855_ = v_a_1873_;
v___y_1856_ = v___y_1823_;
v___y_1857_ = v___y_1824_;
v___y_1858_ = v___y_1825_;
v___y_1859_ = v___y_1826_;
goto v___jp_1854_;
}
else
{
lean_object* v_val_1875_; lean_object* v___x_1876_; 
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1852_, v___f_1851_, v___x_1850_, v_val_1875_, v_a_1873_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v_candidates_1855_ = v_a_1877_;
v___y_1856_ = v___y_1823_;
v___y_1857_ = v___y_1824_;
v___y_1858_ = v___y_1825_;
v___y_1859_ = v___y_1826_;
goto v___jp_1854_;
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v___x_1853_);
lean_del_object(v___x_1832_);
v_a_1878_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1876_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1876_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v___x_1853_);
lean_del_object(v___x_1832_);
v_a_1886_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1872_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1872_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
v___jp_1854_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_isProp(v___x_1853_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; uint8_t v___x_1862_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = lean_unbox(v_a_1861_);
lean_dec(v_a_1861_);
if (v___x_1862_ == 0)
{
v_a_1836_ = v_candidates_1855_;
goto v___jp_1835_;
}
else
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_LocalDecl_hasValue(v_val_1844_, v___x_1850_);
if (v___x_1863_ == 0)
{
v___y_1846_ = v_candidates_1855_;
goto v___jp_1845_;
}
else
{
if (v___x_1850_ == 0)
{
v_a_1836_ = v_candidates_1855_;
goto v___jp_1835_;
}
else
{
v___y_1846_ = v_candidates_1855_;
goto v___jp_1845_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec_ref(v_candidates_1855_);
lean_del_object(v___x_1832_);
v_a_1864_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1860_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1860_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
v_a_1836_ = v_snd_1830_;
goto v___jp_1835_;
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = l_Lean_LocalDecl_fvarId(v_val_1844_);
v___x_1848_ = lean_box(0);
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1846_, v___x_1847_, v___x_1848_);
v_a_1836_ = v___x_1849_;
goto v___jp_1835_;
}
}
v___jp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_a_1836_);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1836_);
v___x_1838_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1821_, v___x_1839_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1819_, v_sz_1820_, v___x_1840_, v___x_1838_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
return v___x_1841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1896_, lean_object* v_sz_1897_, lean_object* v_i_1898_, lean_object* v_b_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
size_t v_sz_boxed_1905_; size_t v_i_boxed_1906_; lean_object* v_res_1907_; 
v_sz_boxed_1905_ = lean_unbox_usize(v_sz_1897_);
lean_dec(v_sz_1897_);
v_i_boxed_1906_ = lean_unbox_usize(v_i_1898_);
lean_dec(v_i_1898_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1896_, v_sz_boxed_1905_, v_i_boxed_1906_, v_b_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec_ref(v_as_1896_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1908_, size_t v_sz_1909_, size_t v_i_1910_, lean_object* v_b_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_lt(v_i_1910_, v_sz_1909_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_b_1911_);
return v___x_1918_;
}
else
{
lean_object* v_snd_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1983_; 
v_snd_1919_ = lean_ctor_get(v_b_1911_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_b_1911_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_b_1911_, 0);
lean_dec(v_unused_1984_);
v___x_1921_ = v_b_1911_;
v_isShared_1922_ = v_isSharedCheck_1983_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snd_1919_);
lean_dec(v_b_1911_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1983_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v_a_1925_; lean_object* v_a_1932_; 
v___x_1923_ = lean_box(0);
v_a_1932_ = lean_array_uget_borrowed(v_as_1908_, v_i_1910_);
if (lean_obj_tag(v_a_1932_) == 0)
{
v_a_1925_ = v_snd_1919_;
goto v___jp_1924_;
}
else
{
lean_object* v_val_1933_; lean_object* v___y_1935_; uint8_t v___x_1939_; 
v_val_1933_ = lean_ctor_get(v_a_1932_, 0);
v___x_1939_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1933_);
if (v___x_1939_ == 0)
{
lean_object* v___f_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; lean_object* v_candidates_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___x_1961_; 
v___f_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1942_ = l_Lean_LocalDecl_type(v_val_1933_);
lean_inc_ref(v___x_1942_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1941_, v___f_1940_, v___x_1939_, v___x_1942_, v_snd_1919_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l_Lean_LocalDecl_value_x3f(v_val_1933_, v___x_1939_);
if (lean_obj_tag(v___x_1963_) == 0)
{
v_candidates_1944_ = v_a_1962_;
v___y_1945_ = v___y_1912_;
v___y_1946_ = v___y_1913_;
v___y_1947_ = v___y_1914_;
v___y_1948_ = v___y_1915_;
goto v___jp_1943_;
}
else
{
lean_object* v_val_1964_; lean_object* v___x_1965_; 
v_val_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_val_1964_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1941_, v___f_1940_, v___x_1939_, v_val_1964_, v_a_1962_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v_candidates_1944_ = v_a_1966_;
v___y_1945_ = v___y_1912_;
v___y_1946_ = v___y_1913_;
v___y_1947_ = v___y_1914_;
v___y_1948_ = v___y_1915_;
goto v___jp_1943_;
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v___x_1942_);
lean_del_object(v___x_1921_);
v_a_1967_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v___x_1942_);
lean_del_object(v___x_1921_);
v_a_1975_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1961_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1961_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
v___jp_1943_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Meta_isProp(v___x_1942_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; uint8_t v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = lean_unbox(v_a_1950_);
lean_dec(v_a_1950_);
if (v___x_1951_ == 0)
{
v_a_1925_ = v_candidates_1944_;
goto v___jp_1924_;
}
else
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_LocalDecl_hasValue(v_val_1933_, v___x_1939_);
if (v___x_1952_ == 0)
{
v___y_1935_ = v_candidates_1944_;
goto v___jp_1934_;
}
else
{
if (v___x_1939_ == 0)
{
v_a_1925_ = v_candidates_1944_;
goto v___jp_1924_;
}
else
{
v___y_1935_ = v_candidates_1944_;
goto v___jp_1934_;
}
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_candidates_1944_);
lean_del_object(v___x_1921_);
v_a_1953_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1949_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1949_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
v_a_1925_ = v_snd_1919_;
goto v___jp_1924_;
}
v___jp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = l_Lean_LocalDecl_fvarId(v_val_1933_);
v___x_1937_ = lean_box(0);
v___x_1938_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1935_, v___x_1936_, v___x_1937_);
v_a_1925_ = v___x_1938_;
goto v___jp_1924_;
}
}
v___jp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_a_1925_);
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_a_1925_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
size_t v___x_1928_; size_t v___x_1929_; 
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_add(v_i_1910_, v___x_1928_);
v_i_1910_ = v___x_1929_;
v_b_1911_ = v___x_1927_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1985_, lean_object* v_sz_1986_, lean_object* v_i_1987_, lean_object* v_b_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
size_t v_sz_boxed_1994_; size_t v_i_boxed_1995_; lean_object* v_res_1996_; 
v_sz_boxed_1994_ = lean_unbox_usize(v_sz_1986_);
lean_dec(v_sz_1986_);
v_i_boxed_1995_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1985_, v_sz_boxed_1994_, v_i_boxed_1995_, v_b_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v_as_1985_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1997_, size_t v_sz_1998_, size_t v_i_1999_, lean_object* v_b_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_lt(v_i_1999_, v_sz_1998_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_b_2000_);
return v___x_2007_;
}
else
{
lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2072_; 
v_snd_2008_ = lean_ctor_get(v_b_2000_, 1);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_b_2000_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v_b_2000_, 0);
lean_dec(v_unused_2073_);
v___x_2010_ = v_b_2000_;
v_isShared_2011_ = v_isSharedCheck_2072_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_dec(v_b_2000_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2072_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v_a_2014_; lean_object* v_a_2021_; 
v___x_2012_ = lean_box(0);
v_a_2021_ = lean_array_uget_borrowed(v_as_1997_, v_i_1999_);
if (lean_obj_tag(v_a_2021_) == 0)
{
v_a_2014_ = v_snd_2008_;
goto v___jp_2013_;
}
else
{
lean_object* v_val_2022_; lean_object* v___y_2024_; uint8_t v___x_2028_; 
v_val_2022_ = lean_ctor_get(v_a_2021_, 0);
v___x_2028_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2022_);
if (v___x_2028_ == 0)
{
lean_object* v___f_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v_candidates_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2050_; 
v___f_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2031_ = l_Lean_LocalDecl_type(v_val_2022_);
lean_inc_ref(v___x_2031_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2030_, v___f_2029_, v___x_2028_, v___x_2031_, v_snd_2008_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_LocalDecl_value_x3f(v_val_2022_, v___x_2028_);
if (lean_obj_tag(v___x_2052_) == 0)
{
v_candidates_2033_ = v_a_2051_;
v___y_2034_ = v___y_2001_;
v___y_2035_ = v___y_2002_;
v___y_2036_ = v___y_2003_;
v___y_2037_ = v___y_2004_;
goto v___jp_2032_;
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2054_; 
v_val_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_val_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2030_, v___f_2029_, v___x_2028_, v_val_2053_, v_a_2051_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v_candidates_2033_ = v_a_2055_;
v___y_2034_ = v___y_2001_;
v___y_2035_ = v___y_2002_;
v___y_2036_ = v___y_2003_;
v___y_2037_ = v___y_2004_;
goto v___jp_2032_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v___x_2031_);
lean_del_object(v___x_2010_);
v_a_2056_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2054_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2054_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v___x_2031_);
lean_del_object(v___x_2010_);
v_a_2064_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2050_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2050_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
v___jp_2032_:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Meta_isProp(v___x_2031_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; uint8_t v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2038_);
v___x_2040_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2040_ == 0)
{
v_a_2014_ = v_candidates_2033_;
goto v___jp_2013_;
}
else
{
uint8_t v___x_2041_; 
v___x_2041_ = l_Lean_LocalDecl_hasValue(v_val_2022_, v___x_2028_);
if (v___x_2041_ == 0)
{
v___y_2024_ = v_candidates_2033_;
goto v___jp_2023_;
}
else
{
if (v___x_2028_ == 0)
{
v_a_2014_ = v_candidates_2033_;
goto v___jp_2013_;
}
else
{
v___y_2024_ = v_candidates_2033_;
goto v___jp_2023_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_candidates_2033_);
lean_del_object(v___x_2010_);
v_a_2042_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2038_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
else
{
v_a_2014_ = v_snd_2008_;
goto v___jp_2013_;
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = l_Lean_LocalDecl_fvarId(v_val_2022_);
v___x_2026_ = lean_box(0);
v___x_2027_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2024_, v___x_2025_, v___x_2026_);
v_a_2014_ = v___x_2027_;
goto v___jp_2013_;
}
}
v___jp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_a_2014_);
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_a_2014_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_1999_, v___x_2017_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1997_, v_sz_1998_, v___x_2018_, v___x_2016_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2074_, lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_b_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
size_t v_sz_boxed_2083_; size_t v_i_boxed_2084_; lean_object* v_res_2085_; 
v_sz_boxed_2083_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2084_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2074_, v_sz_boxed_2083_, v_i_boxed_2084_, v_b_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec_ref(v_as_2074_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2086_, lean_object* v_n_2087_, lean_object* v_b_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
if (lean_obj_tag(v_n_2087_) == 0)
{
lean_object* v_cs_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2128_; 
v_cs_2094_ = lean_ctor_get(v_n_2087_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_n_2087_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2096_ = v_n_2087_;
v_isShared_2097_ = v_isSharedCheck_2128_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_cs_2094_);
lean_dec(v_n_2087_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2128_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; size_t v_sz_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_b_2088_);
v_sz_2100_ = lean_array_size(v_cs_2094_);
v___x_2101_ = ((size_t)0ULL);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2086_, v_cs_2094_, v_sz_2100_, v___x_2101_, v___x_2099_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec_ref(v_cs_2094_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2119_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2119_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2119_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_fst_2107_; 
v_fst_2107_ = lean_ctor_get(v_a_2103_, 0);
if (lean_obj_tag(v_fst_2107_) == 0)
{
lean_object* v_snd_2108_; lean_object* v___x_2110_; 
v_snd_2108_ = lean_ctor_get(v_a_2103_, 1);
lean_inc(v_snd_2108_);
lean_dec(v_a_2103_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
lean_ctor_set(v___x_2096_, 0, v_snd_2108_);
v___x_2110_ = v___x_2096_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_snd_2108_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2110_);
v___x_2112_ = v___x_2105_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_val_2115_; lean_object* v___x_2117_; 
lean_inc_ref(v_fst_2107_);
lean_dec(v_a_2103_);
lean_del_object(v___x_2096_);
v_val_2115_ = lean_ctor_get(v_fst_2107_, 0);
lean_inc(v_val_2115_);
lean_dec_ref(v_fst_2107_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v_val_2115_);
v___x_2117_ = v___x_2105_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_val_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_del_object(v___x_2096_);
v_a_2120_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2102_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2102_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
else
{
lean_object* v_vs_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2163_; 
v_vs_2129_ = lean_ctor_get(v_n_2087_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_n_2087_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2131_ = v_n_2087_;
v_isShared_2132_ = v_isSharedCheck_2163_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_vs_2129_);
lean_dec(v_n_2087_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2163_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; size_t v_sz_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2133_ = lean_box(0);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v_b_2088_);
v_sz_2135_ = lean_array_size(v_vs_2129_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2129_, v_sz_2135_, v___x_2136_, v___x_2134_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec_ref(v_vs_2129_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2154_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2154_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2154_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_fst_2142_; 
v_fst_2142_ = lean_ctor_get(v_a_2138_, 0);
if (lean_obj_tag(v_fst_2142_) == 0)
{
lean_object* v_snd_2143_; lean_object* v___x_2145_; 
v_snd_2143_ = lean_ctor_get(v_a_2138_, 1);
lean_inc(v_snd_2143_);
lean_dec(v_a_2138_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v_snd_2143_);
v___x_2145_ = v___x_2131_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2143_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2145_);
v___x_2147_ = v___x_2140_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v_val_2150_; lean_object* v___x_2152_; 
lean_inc_ref(v_fst_2142_);
lean_dec(v_a_2138_);
lean_del_object(v___x_2131_);
v_val_2150_ = lean_ctor_get(v_fst_2142_, 0);
lean_inc(v_val_2150_);
lean_dec_ref(v_fst_2142_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v_val_2150_);
v___x_2152_ = v___x_2140_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_val_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2131_);
v_a_2155_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2137_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2137_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2164_, lean_object* v_as_2165_, size_t v_sz_2166_, size_t v_i_2167_, lean_object* v_b_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_lt(v_i_2167_, v_sz_2166_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_b_2168_);
return v___x_2175_;
}
else
{
lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2210_; 
v_snd_2176_ = lean_ctor_get(v_b_2168_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_b_2168_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v_b_2168_, 0);
lean_dec(v_unused_2211_);
v___x_2178_ = v_b_2168_;
v_isShared_2179_ = v_isSharedCheck_2210_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_dec(v_b_2168_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2210_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_array_uget_borrowed(v_as_2165_, v_i_2167_);
lean_inc(v_snd_2176_);
lean_inc(v_a_2180_);
v___x_2181_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2164_, v_a_2180_, v_snd_2176_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2201_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2201_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2201_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
if (lean_obj_tag(v_a_2182_) == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2182_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2186_);
v___x_2188_ = v___x_2178_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_snd_2176_);
v___x_2188_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2190_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2188_);
v___x_2190_ = v___x_2184_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
lean_del_object(v___x_2184_);
lean_dec(v_snd_2176_);
v_a_2193_ = lean_ctor_get(v_a_2182_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v_a_2182_);
v___x_2194_ = lean_box(0);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v_a_2193_);
lean_ctor_set(v___x_2178_, 0, v___x_2194_);
v___x_2196_ = v___x_2178_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_a_2193_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
size_t v___x_2197_; size_t v___x_2198_; 
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = lean_usize_add(v_i_2167_, v___x_2197_);
v_i_2167_ = v___x_2198_;
v_b_2168_ = v___x_2196_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_del_object(v___x_2178_);
lean_dec(v_snd_2176_);
v_a_2202_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2181_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2181_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2212_, lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2212_, v_as_2213_, v_sz_boxed_2222_, v_i_boxed_2223_, v_b_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_as_2213_);
lean_dec_ref(v_init_2212_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2225_, lean_object* v_n_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2225_, v_n_2226_, v_b_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_init_2225_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2234_, lean_object* v_init_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_root_2241_; lean_object* v_tail_2242_; lean_object* v___x_2243_; 
v_root_2241_ = lean_ctor_get(v_t_2234_, 0);
lean_inc_ref(v_root_2241_);
v_tail_2242_ = lean_ctor_get(v_t_2234_, 1);
lean_inc_ref(v_tail_2242_);
lean_dec_ref(v_t_2234_);
lean_inc_ref(v_init_2235_);
v___x_2243_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2235_, v_root_2241_, v_init_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v_init_2235_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2280_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2280_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2280_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
if (lean_obj_tag(v_a_2244_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; 
lean_dec_ref(v_tail_2242_);
v_a_2248_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v_a_2244_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v_a_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; size_t v_sz_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
lean_del_object(v___x_2246_);
v_a_2252_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v_a_2244_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v_a_2252_);
v_sz_2255_ = lean_array_size(v_tail_2242_);
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2242_, v_sz_2255_, v___x_2256_, v___x_2254_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v_tail_2242_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2271_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2271_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v_fst_2262_; 
v_fst_2262_ = lean_ctor_get(v_a_2258_, 0);
if (lean_obj_tag(v_fst_2262_) == 0)
{
lean_object* v_snd_2263_; lean_object* v___x_2265_; 
v_snd_2263_ = lean_ctor_get(v_a_2258_, 1);
lean_inc(v_snd_2263_);
lean_dec(v_a_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v_snd_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_snd_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2269_; 
lean_inc_ref(v_fst_2262_);
lean_dec(v_a_2258_);
v_val_2267_ = lean_ctor_get(v_fst_2262_, 0);
lean_inc(v_val_2267_);
lean_dec_ref(v_fst_2262_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v_val_2267_);
v___x_2269_ = v___x_2260_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_val_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
v_a_2272_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2257_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2257_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec_ref(v_tail_2242_);
v_a_2281_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2243_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2243_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2289_, lean_object* v_init_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2289_, v_init_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2296_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_buckets_2299_; lean_object* v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; uint64_t v___x_2303_; uint64_t v_fold_2304_; uint64_t v___x_2305_; uint64_t v___x_2306_; uint64_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; size_t v___x_2311_; size_t v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_buckets_2299_ = lean_ctor_get(v_m_2297_, 1);
v___x_2300_ = lean_array_get_size(v_buckets_2299_);
v___x_2301_ = l_Lean_instHashableFVarId_hash(v_a_2298_);
v___x_2302_ = 32ULL;
v___x_2303_ = lean_uint64_shift_right(v___x_2301_, v___x_2302_);
v_fold_2304_ = lean_uint64_xor(v___x_2301_, v___x_2303_);
v___x_2305_ = 16ULL;
v___x_2306_ = lean_uint64_shift_right(v_fold_2304_, v___x_2305_);
v___x_2307_ = lean_uint64_xor(v_fold_2304_, v___x_2306_);
v___x_2308_ = lean_uint64_to_usize(v___x_2307_);
v___x_2309_ = lean_usize_of_nat(v___x_2300_);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_sub(v___x_2309_, v___x_2310_);
v___x_2312_ = lean_usize_land(v___x_2308_, v___x_2311_);
v___x_2313_ = lean_array_uget_borrowed(v_buckets_2299_, v___x_2312_);
v___x_2314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2298_, v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2315_, lean_object* v_a_2316_){
_start:
{
uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_res_2317_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_m_2315_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2319_, lean_object* v_as_2320_, size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_b_2323_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_b_2323_);
return v___x_2326_;
}
else
{
lean_object* v_snd_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2345_; 
v_snd_2327_ = lean_ctor_get(v_b_2323_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_b_2323_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_b_2323_, 0);
lean_dec(v_unused_2346_);
v___x_2329_ = v_b_2323_;
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_snd_2327_);
lean_dec(v_b_2323_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v_a_2333_; lean_object* v_a_2340_; 
v___x_2331_ = lean_box(0);
v_a_2340_ = lean_array_uget_borrowed(v_as_2320_, v_i_2322_);
if (lean_obj_tag(v_a_2340_) == 0)
{
v_a_2333_ = v_snd_2327_;
goto v___jp_2332_;
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_val_2341_ = lean_ctor_get(v_a_2340_, 0);
v___x_2342_ = l_Lean_LocalDecl_fvarId(v_val_2341_);
v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2319_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec(v___x_2342_);
v_a_2333_ = v_snd_2327_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_array_push(v_snd_2327_, v___x_2342_);
v_a_2333_ = v___x_2344_;
goto v___jp_2332_;
}
}
v___jp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 1, v_a_2333_);
lean_ctor_set(v___x_2329_, 0, v___x_2331_);
v___x_2335_ = v___x_2329_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_a_2333_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
size_t v___x_2336_; size_t v___x_2337_; 
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2322_, v___x_2336_);
v_i_2322_ = v___x_2337_;
v_b_2323_ = v___x_2335_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2347_, lean_object* v_as_2348_, lean_object* v_sz_2349_, lean_object* v_i_2350_, lean_object* v_b_2351_, lean_object* v___y_2352_){
_start:
{
size_t v_sz_boxed_2353_; size_t v_i_boxed_2354_; lean_object* v_res_2355_; 
v_sz_boxed_2353_ = lean_unbox_usize(v_sz_2349_);
lean_dec(v_sz_2349_);
v_i_boxed_2354_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_res_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2347_, v_as_2348_, v_sz_boxed_2353_, v_i_boxed_2354_, v_b_2351_);
lean_dec_ref(v_as_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2356_, lean_object* v_as_2357_, size_t v_sz_2358_, size_t v_i_2359_, lean_object* v_b_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_usize_dec_lt(v_i_2359_, v_sz_2358_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_b_2360_);
return v___x_2367_;
}
else
{
lean_object* v_snd_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2386_; 
v_snd_2368_ = lean_ctor_get(v_b_2360_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_b_2360_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v_b_2360_, 0);
lean_dec(v_unused_2387_);
v___x_2370_ = v_b_2360_;
v_isShared_2371_ = v_isSharedCheck_2386_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snd_2368_);
lean_dec(v_b_2360_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2386_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v_a_2374_; lean_object* v_a_2381_; 
v___x_2372_ = lean_box(0);
v_a_2381_ = lean_array_uget_borrowed(v_as_2357_, v_i_2359_);
if (lean_obj_tag(v_a_2381_) == 0)
{
v_a_2374_ = v_snd_2368_;
goto v___jp_2373_;
}
else
{
lean_object* v_val_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_val_2382_ = lean_ctor_get(v_a_2381_, 0);
v___x_2383_ = l_Lean_LocalDecl_fvarId(v_val_2382_);
v___x_2384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2356_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_dec(v___x_2383_);
v_a_2374_ = v_snd_2368_;
goto v___jp_2373_;
}
else
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_array_push(v_snd_2368_, v___x_2383_);
v_a_2374_ = v___x_2385_;
goto v___jp_2373_;
}
}
v___jp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v_a_2374_);
lean_ctor_set(v___x_2370_, 0, v___x_2372_);
v___x_2376_ = v___x_2370_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_a_2374_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_add(v_i_2359_, v___x_2377_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2356_, v_as_2357_, v_sz_2358_, v___x_2378_, v___x_2376_);
return v___x_2379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2388_, lean_object* v_as_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
size_t v_sz_boxed_2398_; size_t v_i_boxed_2399_; lean_object* v_res_2400_; 
v_sz_boxed_2398_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2399_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2388_, v_as_2389_, v_sz_boxed_2398_, v_i_boxed_2399_, v_b_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v_as_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2401_, lean_object* v_a_2402_, lean_object* v_n_2403_, lean_object* v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
if (lean_obj_tag(v_n_2403_) == 0)
{
lean_object* v_cs_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2444_; 
v_cs_2410_ = lean_ctor_get(v_n_2403_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_n_2403_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2412_ = v_n_2403_;
v_isShared_2413_ = v_isSharedCheck_2444_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_cs_2410_);
lean_dec(v_n_2403_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2444_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; size_t v_sz_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v_b_2404_);
v_sz_2416_ = lean_array_size(v_cs_2410_);
v___x_2417_ = ((size_t)0ULL);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2401_, v_a_2402_, v_cs_2410_, v_sz_2416_, v___x_2417_, v___x_2415_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v_cs_2410_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2435_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2435_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2435_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_fst_2423_; 
v_fst_2423_ = lean_ctor_get(v_a_2419_, 0);
if (lean_obj_tag(v_fst_2423_) == 0)
{
lean_object* v_snd_2424_; lean_object* v___x_2426_; 
v_snd_2424_ = lean_ctor_get(v_a_2419_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_a_2419_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set_tag(v___x_2412_, 1);
lean_ctor_set(v___x_2412_, 0, v_snd_2424_);
v___x_2426_ = v___x_2412_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_snd_2424_);
v___x_2426_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2426_);
v___x_2428_ = v___x_2421_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
lean_object* v_val_2431_; lean_object* v___x_2433_; 
lean_inc_ref(v_fst_2423_);
lean_dec(v_a_2419_);
lean_del_object(v___x_2412_);
v_val_2431_ = lean_ctor_get(v_fst_2423_, 0);
lean_inc(v_val_2431_);
lean_dec_ref(v_fst_2423_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_val_2431_);
v___x_2433_ = v___x_2421_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_val_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_del_object(v___x_2412_);
v_a_2436_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2418_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2418_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
else
{
lean_object* v_vs_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2479_; 
v_vs_2445_ = lean_ctor_get(v_n_2403_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_n_2403_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2447_ = v_n_2403_;
v_isShared_2448_ = v_isSharedCheck_2479_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_vs_2445_);
lean_dec(v_n_2403_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2479_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; size_t v_sz_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2449_ = lean_box(0);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v_b_2404_);
v_sz_2451_ = lean_array_size(v_vs_2445_);
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2402_, v_vs_2445_, v_sz_2451_, v___x_2452_, v___x_2450_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v_vs_2445_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2470_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2470_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2470_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v_fst_2458_; 
v_fst_2458_ = lean_ctor_get(v_a_2454_, 0);
if (lean_obj_tag(v_fst_2458_) == 0)
{
lean_object* v_snd_2459_; lean_object* v___x_2461_; 
v_snd_2459_ = lean_ctor_get(v_a_2454_, 1);
lean_inc(v_snd_2459_);
lean_dec(v_a_2454_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_snd_2459_);
v___x_2461_ = v___x_2447_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_snd_2459_);
v___x_2461_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2463_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2461_);
v___x_2463_ = v___x_2456_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
else
{
lean_object* v_val_2466_; lean_object* v___x_2468_; 
lean_inc_ref(v_fst_2458_);
lean_dec(v_a_2454_);
lean_del_object(v___x_2447_);
v_val_2466_ = lean_ctor_get(v_fst_2458_, 0);
lean_inc(v_val_2466_);
lean_dec_ref(v_fst_2458_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_val_2466_);
v___x_2468_ = v___x_2456_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_val_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_del_object(v___x_2447_);
v_a_2471_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2453_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2453_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2480_, lean_object* v_a_2481_, lean_object* v_as_2482_, size_t v_sz_2483_, size_t v_i_2484_, lean_object* v_b_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_usize_dec_lt(v_i_2484_, v_sz_2483_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_b_2485_);
return v___x_2492_;
}
else
{
lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2527_; 
v_snd_2493_ = lean_ctor_get(v_b_2485_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_b_2485_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v_b_2485_, 0);
lean_dec(v_unused_2528_);
v___x_2495_ = v_b_2485_;
v_isShared_2496_ = v_isSharedCheck_2527_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_dec(v_b_2485_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2527_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_a_2497_; lean_object* v___x_2498_; 
v_a_2497_ = lean_array_uget_borrowed(v_as_2482_, v_i_2484_);
lean_inc(v_snd_2493_);
lean_inc(v_a_2497_);
v___x_2498_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2480_, v_a_2481_, v_a_2497_, v_snd_2493_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2518_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2518_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2518_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
if (lean_obj_tag(v_a_2499_) == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2499_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2503_);
v___x_2505_ = v___x_2495_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_snd_2493_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2505_);
v___x_2507_ = v___x_2501_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
lean_del_object(v___x_2501_);
lean_dec(v_snd_2493_);
v_a_2510_ = lean_ctor_get(v_a_2499_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v_a_2499_);
v___x_2511_ = lean_box(0);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v_a_2510_);
lean_ctor_set(v___x_2495_, 0, v___x_2511_);
v___x_2513_ = v___x_2495_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_a_2510_);
v___x_2513_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
size_t v___x_2514_; size_t v___x_2515_; 
v___x_2514_ = ((size_t)1ULL);
v___x_2515_ = lean_usize_add(v_i_2484_, v___x_2514_);
v_i_2484_ = v___x_2515_;
v_b_2485_ = v___x_2513_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_del_object(v___x_2495_);
lean_dec(v_snd_2493_);
v_a_2519_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2498_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2498_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2529_, lean_object* v_a_2530_, lean_object* v_as_2531_, lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
size_t v_sz_boxed_2540_; size_t v_i_boxed_2541_; lean_object* v_res_2542_; 
v_sz_boxed_2540_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2541_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2529_, v_a_2530_, v_as_2531_, v_sz_boxed_2540_, v_i_boxed_2541_, v_b_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_as_2531_);
lean_dec_ref(v_a_2530_);
lean_dec_ref(v_init_2529_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2543_, lean_object* v_a_2544_, lean_object* v_n_2545_, lean_object* v_b_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2543_, v_a_2544_, v_n_2545_, v_b_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_init_2543_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2553_, lean_object* v_as_2554_, size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_b_2557_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_usize_dec_lt(v_i_2556_, v_sz_2555_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_b_2557_);
return v___x_2560_;
}
else
{
lean_object* v_snd_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2579_; 
v_snd_2561_ = lean_ctor_get(v_b_2557_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_b_2557_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v_b_2557_, 0);
lean_dec(v_unused_2580_);
v___x_2563_ = v_b_2557_;
v_isShared_2564_ = v_isSharedCheck_2579_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_snd_2561_);
lean_dec(v_b_2557_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2579_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v_a_2567_; lean_object* v_a_2574_; 
v___x_2565_ = lean_box(0);
v_a_2574_ = lean_array_uget_borrowed(v_as_2554_, v_i_2556_);
if (lean_obj_tag(v_a_2574_) == 0)
{
v_a_2567_ = v_snd_2561_;
goto v___jp_2566_;
}
else
{
lean_object* v_val_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v_val_2575_ = lean_ctor_get(v_a_2574_, 0);
v___x_2576_ = l_Lean_LocalDecl_fvarId(v_val_2575_);
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2553_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec(v___x_2576_);
v_a_2567_ = v_snd_2561_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_array_push(v_snd_2561_, v___x_2576_);
v_a_2567_ = v___x_2578_;
goto v___jp_2566_;
}
}
v___jp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v_a_2567_);
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2569_ = v___x_2563_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_a_2567_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
size_t v___x_2570_; size_t v___x_2571_; 
v___x_2570_ = ((size_t)1ULL);
v___x_2571_ = lean_usize_add(v_i_2556_, v___x_2570_);
v_i_2556_ = v___x_2571_;
v_b_2557_ = v___x_2569_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2581_, lean_object* v_as_2582_, lean_object* v_sz_2583_, lean_object* v_i_2584_, lean_object* v_b_2585_, lean_object* v___y_2586_){
_start:
{
size_t v_sz_boxed_2587_; size_t v_i_boxed_2588_; lean_object* v_res_2589_; 
v_sz_boxed_2587_ = lean_unbox_usize(v_sz_2583_);
lean_dec(v_sz_2583_);
v_i_boxed_2588_ = lean_unbox_usize(v_i_2584_);
lean_dec(v_i_2584_);
v_res_2589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2581_, v_as_2582_, v_sz_boxed_2587_, v_i_boxed_2588_, v_b_2585_);
lean_dec_ref(v_as_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2590_, lean_object* v_as_2591_, size_t v_sz_2592_, size_t v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_usize_dec_lt(v_i_2593_, v_sz_2592_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2594_);
return v___x_2601_;
}
else
{
lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2620_; 
v_snd_2602_ = lean_ctor_get(v_b_2594_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_b_2594_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v_b_2594_, 0);
lean_dec(v_unused_2621_);
v___x_2604_ = v_b_2594_;
v_isShared_2605_ = v_isSharedCheck_2620_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_dec(v_b_2594_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2620_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v_a_2608_; lean_object* v_a_2615_; 
v___x_2606_ = lean_box(0);
v_a_2615_ = lean_array_uget_borrowed(v_as_2591_, v_i_2593_);
if (lean_obj_tag(v_a_2615_) == 0)
{
v_a_2608_ = v_snd_2602_;
goto v___jp_2607_;
}
else
{
lean_object* v_val_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_val_2616_ = lean_ctor_get(v_a_2615_, 0);
v___x_2617_ = l_Lean_LocalDecl_fvarId(v_val_2616_);
v___x_2618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2590_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_dec(v___x_2617_);
v_a_2608_ = v_snd_2602_;
goto v___jp_2607_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_array_push(v_snd_2602_, v___x_2617_);
v_a_2608_ = v___x_2619_;
goto v___jp_2607_;
}
}
v___jp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v_a_2608_);
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2610_ = v___x_2604_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_a_2608_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = ((size_t)1ULL);
v___x_2612_ = lean_usize_add(v_i_2593_, v___x_2611_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2590_, v_as_2591_, v_sz_2592_, v___x_2612_, v___x_2610_);
return v___x_2613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2622_, lean_object* v_as_2623_, lean_object* v_sz_2624_, lean_object* v_i_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
size_t v_sz_boxed_2632_; size_t v_i_boxed_2633_; lean_object* v_res_2634_; 
v_sz_boxed_2632_ = lean_unbox_usize(v_sz_2624_);
lean_dec(v_sz_2624_);
v_i_boxed_2633_ = lean_unbox_usize(v_i_2625_);
lean_dec(v_i_2625_);
v_res_2634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2622_, v_as_2623_, v_sz_boxed_2632_, v_i_boxed_2633_, v_b_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v_as_2623_);
lean_dec_ref(v_a_2622_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2635_, lean_object* v_t_2636_, lean_object* v_init_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_root_2643_; lean_object* v_tail_2644_; lean_object* v___x_2645_; 
v_root_2643_ = lean_ctor_get(v_t_2636_, 0);
lean_inc_ref(v_root_2643_);
v_tail_2644_ = lean_ctor_get(v_t_2636_, 1);
lean_inc_ref(v_tail_2644_);
lean_dec_ref(v_t_2636_);
lean_inc_ref(v_init_2637_);
v___x_2645_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2637_, v_a_2635_, v_root_2643_, v_init_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v_init_2637_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2682_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2682_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2682_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
if (lean_obj_tag(v_a_2646_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2652_; 
lean_dec_ref(v_tail_2644_);
v_a_2650_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_a_2650_);
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; size_t v_sz_2657_; size_t v___x_2658_; lean_object* v___x_2659_; 
lean_del_object(v___x_2648_);
v_a_2654_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v_a_2646_);
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v_a_2654_);
v_sz_2657_ = lean_array_size(v_tail_2644_);
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2635_, v_tail_2644_, v_sz_2657_, v___x_2658_, v___x_2656_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v_tail_2644_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2673_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2673_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2673_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v_fst_2664_; 
v_fst_2664_ = lean_ctor_get(v_a_2660_, 0);
if (lean_obj_tag(v_fst_2664_) == 0)
{
lean_object* v_snd_2665_; lean_object* v___x_2667_; 
v_snd_2665_ = lean_ctor_get(v_a_2660_, 1);
lean_inc(v_snd_2665_);
lean_dec(v_a_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_snd_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_snd_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2671_; 
lean_inc_ref(v_fst_2664_);
lean_dec(v_a_2660_);
v_val_2669_ = lean_ctor_get(v_fst_2664_, 0);
lean_inc(v_val_2669_);
lean_dec_ref(v_fst_2664_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_val_2669_);
v___x_2671_ = v___x_2662_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_val_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
v_a_2674_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2659_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2659_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref(v_tail_2644_);
v_a_2683_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2645_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2645_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2691_, lean_object* v_t_2692_, lean_object* v_init_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2691_, v_t_2692_, v_init_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec_ref(v_a_2691_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2702_, lean_object* v_mvarId_2703_, lean_object* v___f_2704_, lean_object* v___f_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_lctx_2711_; lean_object* v_decls_2712_; lean_object* v___x_2713_; 
v_lctx_2711_ = lean_ctor_get(v___y_2706_, 2);
v_decls_2712_ = lean_ctor_get(v_lctx_2711_, 1);
lean_inc_ref_n(v_decls_2712_, 2);
v___x_2713_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2712_, v_candidates_2702_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = l_Lean_MVarId_getType(v_mvarId_2703_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2719_; lean_object* v___y_2721_; uint8_t v___x_2745_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2716_, v___y_2707_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
v___x_2719_ = lean_st_mk_ref(v_a_2714_);
v___x_2745_ = l_Lean_Expr_hasFVar(v_a_2718_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec(v_a_2718_);
lean_dec_ref(v___f_2705_);
v___x_2746_ = lean_box(0);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___x_2719_);
v___x_2747_ = lean_apply_7(v___f_2704_, v___x_2746_, v___x_2719_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, lean_box(0));
v___y_2721_ = v___x_2747_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2749_ = 0;
v___x_2750_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2748_, v___f_2705_, v_a_2718_, v___x_2749_, v___x_2719_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2750_);
lean_inc(v___y_2709_);
lean_inc_ref(v___y_2708_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___x_2719_);
v___x_2752_ = lean_apply_7(v___f_2704_, v_a_2751_, v___x_2719_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, lean_box(0));
v___y_2721_ = v___x_2752_;
goto v___jp_2720_;
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v___x_2719_);
lean_dec_ref(v_decls_2712_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v___f_2704_);
v_a_2753_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2750_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2750_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
v___jp_2720_:
{
if (lean_obj_tag(v___y_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2736_; 
v_a_2722_ = lean_ctor_get(v___y_2721_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___y_2721_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2724_ = v___y_2721_;
v_isShared_2725_ = v_isSharedCheck_2736_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___y_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2736_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v_size_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2726_ = lean_st_ref_get(v___x_2719_);
lean_dec(v___x_2719_);
lean_dec(v___x_2726_);
v_size_2727_ = lean_ctor_get(v_a_2722_, 0);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_nat_dec_eq(v_size_2727_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_del_object(v___x_2724_);
v___x_2730_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2731_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2722_, v_decls_2712_, v___x_2730_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v_a_2722_);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
lean_dec(v_a_2722_);
lean_dec_ref(v_decls_2712_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
v___x_2732_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2732_);
v___x_2734_ = v___x_2724_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v___x_2719_);
lean_dec_ref(v_decls_2712_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
v_a_2737_ = lean_ctor_get(v___y_2721_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___y_2721_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___y_2721_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___y_2721_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2714_);
lean_dec_ref(v_decls_2712_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v___f_2705_);
lean_dec_ref(v___f_2704_);
v_a_2761_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2715_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2715_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_decls_2712_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v___f_2705_);
lean_dec_ref(v___f_2704_);
lean_dec(v_mvarId_2703_);
v_a_2769_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2713_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2713_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2777_, lean_object* v_mvarId_2778_, lean_object* v___f_2779_, lean_object* v___f_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2777_, v_mvarId_2778_, v___f_2779_, v___f_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v___f_2795_; lean_object* v___f_2796_; lean_object* v_candidates_2797_; lean_object* v___f_2798_; lean_object* v___x_2799_; 
v___f_2795_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2796_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2797_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2789_);
v___f_2798_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2798_, 0, v_candidates_2797_);
lean_closure_set(v___f_2798_, 1, v_mvarId_2789_);
lean_closure_set(v___f_2798_, 2, v___f_2796_);
lean_closure_set(v___f_2798_, 3, v___f_2795_);
v___x_2799_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2789_, v___f_2798_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2807_, lean_object* v_m_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2808_, v_a_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2811_, lean_object* v_m_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2811_, v_m_2812_, v_a_2813_);
lean_dec(v_a_2813_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2815_, lean_object* v_m_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2816_, v_a_2817_, v_b_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2820_, lean_object* v_m_2821_, lean_object* v_a_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2821_, v_a_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2824_, lean_object* v_m_2825_, lean_object* v_a_2826_){
_start:
{
uint8_t v_res_2827_; lean_object* v_r_2828_; 
v_res_2827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2824_, v_m_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_m_2825_);
v_r_2828_ = lean_box(v_res_2827_);
return v_r_2828_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2829_, lean_object* v_a_2830_, lean_object* v_x_2831_){
_start:
{
uint8_t v___x_2832_; 
v___x_2832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2830_, v_x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2833_, lean_object* v_a_2834_, lean_object* v_x_2835_){
_start:
{
uint8_t v_res_2836_; lean_object* v_r_2837_; 
v_res_2836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2833_, v_a_2834_, v_x_2835_);
lean_dec(v_x_2835_);
lean_dec(v_a_2834_);
v_r_2837_ = lean_box(v_res_2836_);
return v_r_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2838_, lean_object* v_a_2839_, lean_object* v_x_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2839_, v_x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2842_, lean_object* v_a_2843_, lean_object* v_x_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2842_, v_a_2843_, v_x_2844_);
lean_dec(v_a_2843_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2846_, lean_object* v_a_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2846_, v_a_2847_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2855_, lean_object* v_a_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2855_, v_a_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v_a_2856_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2864_, lean_object* v_data_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2867_, v_a_2868_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2876_, lean_object* v_a_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2876_, v_a_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec(v_a_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2885_, lean_object* v_i_2886_, lean_object* v_source_2887_, lean_object* v_target_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2886_, v_source_2887_, v_target_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2890_, lean_object* v_as_2891_, size_t v_sz_2892_, size_t v_i_2893_, lean_object* v_b_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2890_, v_as_2891_, v_sz_2892_, v_i_2893_, v_b_2894_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2901_, lean_object* v_as_2902_, lean_object* v_sz_2903_, lean_object* v_i_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
size_t v_sz_boxed_2911_; size_t v_i_boxed_2912_; lean_object* v_res_2913_; 
v_sz_boxed_2911_ = lean_unbox_usize(v_sz_2903_);
lean_dec(v_sz_2903_);
v_i_boxed_2912_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_res_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2901_, v_as_2902_, v_sz_boxed_2911_, v_i_boxed_2912_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v_as_2902_);
lean_dec_ref(v_a_2901_);
return v_res_2913_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2914_, lean_object* v_m_2915_, lean_object* v_a_2916_){
_start:
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2915_, v_a_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2918_, lean_object* v_m_2919_, lean_object* v_a_2920_){
_start:
{
uint8_t v_res_2921_; lean_object* v_r_2922_; 
v_res_2921_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2918_, v_m_2919_, v_a_2920_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_m_2919_);
v_r_2922_ = lean_box(v_res_2921_);
return v_r_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2923_, lean_object* v_m_2924_, lean_object* v_a_2925_, lean_object* v_b_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2924_, v_a_2925_, v_b_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2928_, lean_object* v_x_2929_, lean_object* v_x_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2929_, v_x_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2932_, lean_object* v_as_2933_, size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2932_, v_as_2933_, v_sz_2934_, v_i_2935_, v_b_2936_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2943_, lean_object* v_as_2944_, lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_b_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
size_t v_sz_boxed_2953_; size_t v_i_boxed_2954_; lean_object* v_res_2955_; 
v_sz_boxed_2953_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2954_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2943_, v_as_2944_, v_sz_boxed_2953_, v_i_boxed_2954_, v_b_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v_as_2944_);
lean_dec_ref(v_a_2943_);
return v_res_2955_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2956_, lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_a_2961_, lean_object* v_x_2962_){
_start:
{
uint8_t v_res_2963_; lean_object* v_r_2964_; 
v_res_2963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2960_, v_a_2961_, v_x_2962_);
lean_dec(v_x_2962_);
lean_dec_ref(v_a_2961_);
v_r_2964_ = lean_box(v_res_2963_);
return v_r_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2965_, lean_object* v_data_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2968_, lean_object* v_i_2969_, lean_object* v_source_2970_, lean_object* v_target_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2969_, v_source_2970_, v_target_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2974_, v_x_2975_);
return v___x_2976_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = l_Lean_maxRecDepthErrorMessage;
v___x_2983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
return v___x_2983_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2985_ = l_Lean_MessageData_ofFormat(v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2987_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2988_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v___x_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v_ref_2989_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2997_, lean_object* v_ref_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2998_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_ref_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_3006_, v_ref_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3015_, lean_object* v_mvarId_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_fileName_3023_; lean_object* v_fileMap_3024_; lean_object* v_options_3025_; lean_object* v_currRecDepth_3026_; lean_object* v_maxRecDepth_3027_; lean_object* v_ref_3028_; lean_object* v_currNamespace_3029_; lean_object* v_openDecls_3030_; lean_object* v_initHeartbeats_3031_; lean_object* v_maxHeartbeats_3032_; lean_object* v_quotContext_3033_; lean_object* v_currMacroScope_3034_; uint8_t v_diag_3035_; lean_object* v_cancelTk_x3f_3036_; uint8_t v_suppressElabErrors_3037_; lean_object* v_inheritedTraceOptions_3038_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_fileName_3023_ = lean_ctor_get(v_a_3020_, 0);
v_fileMap_3024_ = lean_ctor_get(v_a_3020_, 1);
v_options_3025_ = lean_ctor_get(v_a_3020_, 2);
v_currRecDepth_3026_ = lean_ctor_get(v_a_3020_, 3);
v_maxRecDepth_3027_ = lean_ctor_get(v_a_3020_, 4);
v_ref_3028_ = lean_ctor_get(v_a_3020_, 5);
v_currNamespace_3029_ = lean_ctor_get(v_a_3020_, 6);
v_openDecls_3030_ = lean_ctor_get(v_a_3020_, 7);
v_initHeartbeats_3031_ = lean_ctor_get(v_a_3020_, 8);
v_maxHeartbeats_3032_ = lean_ctor_get(v_a_3020_, 9);
v_quotContext_3033_ = lean_ctor_get(v_a_3020_, 10);
v_currMacroScope_3034_ = lean_ctor_get(v_a_3020_, 11);
v_diag_3035_ = lean_ctor_get_uint8(v_a_3020_, sizeof(void*)*14);
v_cancelTk_x3f_3036_ = lean_ctor_get(v_a_3020_, 12);
v_suppressElabErrors_3037_ = lean_ctor_get_uint8(v_a_3020_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3038_ = lean_ctor_get(v_a_3020_, 13);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = lean_nat_dec_eq(v_maxRecDepth_3027_, v___x_3066_);
if (v___x_3067_ == 0)
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_nat_dec_eq(v_currRecDepth_3026_, v_maxRecDepth_3027_);
if (v___x_3068_ == 0)
{
goto v___jp_3039_;
}
else
{
lean_object* v___x_3069_; 
lean_dec(v_mvarId_3016_);
lean_dec_ref(v_x_3015_);
lean_inc(v_ref_3028_);
v___x_3069_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3028_);
return v___x_3069_;
}
}
else
{
goto v___jp_3039_;
}
v___jp_3039_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_unsigned_to_nat(1u);
v___x_3041_ = lean_nat_add(v_currRecDepth_3026_, v___x_3040_);
lean_inc_ref(v_inheritedTraceOptions_3038_);
lean_inc(v_cancelTk_x3f_3036_);
lean_inc(v_currMacroScope_3034_);
lean_inc(v_quotContext_3033_);
lean_inc(v_maxHeartbeats_3032_);
lean_inc(v_initHeartbeats_3031_);
lean_inc(v_openDecls_3030_);
lean_inc(v_currNamespace_3029_);
lean_inc(v_ref_3028_);
lean_inc(v_maxRecDepth_3027_);
lean_inc_ref(v_options_3025_);
lean_inc_ref(v_fileMap_3024_);
lean_inc_ref(v_fileName_3023_);
v___x_3042_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3042_, 0, v_fileName_3023_);
lean_ctor_set(v___x_3042_, 1, v_fileMap_3024_);
lean_ctor_set(v___x_3042_, 2, v_options_3025_);
lean_ctor_set(v___x_3042_, 3, v___x_3041_);
lean_ctor_set(v___x_3042_, 4, v_maxRecDepth_3027_);
lean_ctor_set(v___x_3042_, 5, v_ref_3028_);
lean_ctor_set(v___x_3042_, 6, v_currNamespace_3029_);
lean_ctor_set(v___x_3042_, 7, v_openDecls_3030_);
lean_ctor_set(v___x_3042_, 8, v_initHeartbeats_3031_);
lean_ctor_set(v___x_3042_, 9, v_maxHeartbeats_3032_);
lean_ctor_set(v___x_3042_, 10, v_quotContext_3033_);
lean_ctor_set(v___x_3042_, 11, v_currMacroScope_3034_);
lean_ctor_set(v___x_3042_, 12, v_cancelTk_x3f_3036_);
lean_ctor_set(v___x_3042_, 13, v_inheritedTraceOptions_3038_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*14, v_diag_3035_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*14 + 1, v_suppressElabErrors_3037_);
lean_inc_ref(v_x_3015_);
lean_inc(v_a_3021_);
lean_inc_ref(v___x_3042_);
lean_inc(v_a_3019_);
lean_inc_ref(v_a_3018_);
lean_inc(v_mvarId_3016_);
v___x_3043_ = lean_apply_6(v_x_3015_, v_mvarId_3016_, v_a_3018_, v_a_3019_, v___x_3042_, v_a_3021_, lean_box(0));
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3057_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3057_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3057_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
if (lean_obj_tag(v_a_3044_) == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
lean_dec_ref(v___x_3042_);
lean_dec_ref(v_x_3015_);
v___x_3048_ = lean_st_ref_take(v_a_3017_);
v___x_3049_ = lean_array_push(v___x_3048_, v_mvarId_3016_);
v___x_3050_ = lean_st_ref_set(v_a_3017_, v___x_3049_);
v___x_3051_ = lean_box(0);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3051_);
v___x_3053_ = v___x_3046_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
else
{
lean_object* v_val_3055_; lean_object* v___x_3056_; 
lean_del_object(v___x_3046_);
lean_dec(v_mvarId_3016_);
v_val_3055_ = lean_ctor_get(v_a_3044_, 0);
lean_inc(v_val_3055_);
lean_dec_ref(v_a_3044_);
v___x_3056_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3015_, v_val_3055_, v_a_3017_, v_a_3018_, v_a_3019_, v___x_3042_, v_a_3021_);
lean_dec_ref(v___x_3042_);
return v___x_3056_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___x_3042_);
lean_dec(v_mvarId_3016_);
lean_dec_ref(v_x_3015_);
v_a_3058_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3043_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3043_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3070_, lean_object* v_as_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
if (lean_obj_tag(v_as_3071_) == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec_ref(v_x_3070_);
v___x_3078_ = lean_box(0);
v___x_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
return v___x_3079_;
}
else
{
lean_object* v_head_3080_; lean_object* v_tail_3081_; lean_object* v___x_3082_; 
v_head_3080_ = lean_ctor_get(v_as_3071_, 0);
lean_inc(v_head_3080_);
v_tail_3081_ = lean_ctor_get(v_as_3071_, 1);
lean_inc(v_tail_3081_);
lean_dec_ref(v_as_3071_);
lean_inc_ref(v_x_3070_);
v___x_3082_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3070_, v_head_3080_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_dec_ref(v___x_3082_);
v_as_3071_ = v_tail_3081_;
goto _start;
}
else
{
lean_dec(v_tail_3081_);
lean_dec_ref(v_x_3070_);
return v___x_3082_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3084_, lean_object* v_as_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3084_, v_as_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3093_, lean_object* v_mvarId_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3093_, v_mvarId_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3102_, lean_object* v_x_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3110_ = lean_st_mk_ref(v___x_3109_);
v___x_3111_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3103_, v_mvarId_3102_, v___x_3110_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3120_; 
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v___x_3111_, 0);
lean_dec(v_unused_3121_);
v___x_3113_ = v___x_3111_;
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
else
{
lean_dec(v___x_3111_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3120_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_st_ref_get(v___x_3110_);
lean_dec(v___x_3110_);
v___x_3116_ = lean_array_to_list(v___x_3115_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3116_);
v___x_3118_ = v___x_3113_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v___x_3110_);
v_a_3122_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3111_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3111_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3130_, lean_object* v_x_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Lean_Meta_saturate(v_mvarId_3130_, v_x_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3138_, lean_object* v_msg_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
if (lean_obj_tag(v_mvarIds_3138_) == 1)
{
lean_object* v_tail_3145_; 
v_tail_3145_ = lean_ctor_get(v_mvarIds_3138_, 1);
if (lean_obj_tag(v_tail_3145_) == 0)
{
lean_object* v_head_3146_; lean_object* v___x_3147_; 
lean_dec_ref(v_msg_3139_);
v_head_3146_ = lean_ctor_get(v_mvarIds_3138_, 0);
lean_inc(v_head_3146_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_head_3146_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3148_;
}
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3150_, lean_object* v_msg_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Meta_exactlyOne(v_mvarIds_3150_, v_msg_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_mvarIds_3150_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3158_, lean_object* v_msg_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
if (lean_obj_tag(v_mvarIds_3158_) == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec_ref(v_msg_3159_);
v___x_3165_ = lean_box(0);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v_tail_3167_; 
v_tail_3167_ = lean_ctor_get(v_mvarIds_3158_, 1);
if (lean_obj_tag(v_tail_3167_) == 0)
{
lean_object* v_head_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
lean_dec_ref(v_msg_3159_);
v_head_3168_ = lean_ctor_get(v_mvarIds_3158_, 0);
lean_inc(v_head_3168_);
v___x_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_head_3168_);
v___x_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
return v___x_3170_;
}
else
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3172_, lean_object* v_msg_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3172_, v_msg_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_mvarIds_3172_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3180_, size_t v_sz_3181_, size_t v_i_3182_, lean_object* v_b_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_lt(v_i_3182_, v_sz_3181_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_b_3183_);
return v___x_3190_;
}
else
{
lean_object* v_snd_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3221_; 
v_snd_3191_ = lean_ctor_get(v_b_3183_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_b_3183_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_b_3183_, 0);
lean_dec(v_unused_3222_);
v___x_3193_ = v_b_3183_;
v_isShared_3194_ = v_isSharedCheck_3221_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_snd_3191_);
lean_dec(v_b_3183_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3221_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v_a_3197_; lean_object* v_a_3204_; 
v___x_3195_ = lean_box(0);
v_a_3204_ = lean_array_uget_borrowed(v_as_3180_, v_i_3182_);
if (lean_obj_tag(v_a_3204_) == 0)
{
v_a_3197_ = v_snd_3191_;
goto v___jp_3196_;
}
else
{
lean_object* v_val_3205_; uint8_t v___x_3206_; 
v_val_3205_ = lean_ctor_get(v_a_3204_, 0);
v___x_3206_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = l_Lean_LocalDecl_type(v_val_3205_);
v___x_3208_ = l_Lean_Meta_isProp(v___x_3207_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; uint8_t v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref(v___x_3208_);
v___x_3210_ = lean_unbox(v_a_3209_);
lean_dec(v_a_3209_);
if (v___x_3210_ == 0)
{
v_a_3197_ = v_snd_3191_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = l_Lean_LocalDecl_fvarId(v_val_3205_);
v___x_3212_ = lean_array_push(v_snd_3191_, v___x_3211_);
v_a_3197_ = v___x_3212_;
goto v___jp_3196_;
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_del_object(v___x_3193_);
lean_dec(v_snd_3191_);
v_a_3213_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3208_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3208_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
v_a_3197_ = v_snd_3191_;
goto v___jp_3196_;
}
}
v___jp_3196_:
{
lean_object* v___x_3199_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 1, v_a_3197_);
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3199_ = v___x_3193_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_a_3197_);
v___x_3199_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
size_t v___x_3200_; size_t v___x_3201_; 
v___x_3200_ = ((size_t)1ULL);
v___x_3201_ = lean_usize_add(v_i_3182_, v___x_3200_);
v_i_3182_ = v___x_3201_;
v_b_3183_ = v___x_3199_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3223_, lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_b_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
size_t v_sz_boxed_3232_; size_t v_i_boxed_3233_; lean_object* v_res_3234_; 
v_sz_boxed_3232_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3233_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3223_, v_sz_boxed_3232_, v_i_boxed_3233_, v_b_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v_as_3223_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3235_, size_t v_sz_3236_, size_t v_i_3237_, lean_object* v_b_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_usize_dec_lt(v_i_3237_, v_sz_3236_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_b_3238_);
return v___x_3245_;
}
else
{
lean_object* v_snd_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3276_; 
v_snd_3246_ = lean_ctor_get(v_b_3238_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_b_3238_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_b_3238_, 0);
lean_dec(v_unused_3277_);
v___x_3248_ = v_b_3238_;
v_isShared_3249_ = v_isSharedCheck_3276_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snd_3246_);
lean_dec(v_b_3238_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3276_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v_a_3252_; lean_object* v_a_3259_; 
v___x_3250_ = lean_box(0);
v_a_3259_ = lean_array_uget_borrowed(v_as_3235_, v_i_3237_);
if (lean_obj_tag(v_a_3259_) == 0)
{
v_a_3252_ = v_snd_3246_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3260_; uint8_t v___x_3261_; 
v_val_3260_ = lean_ctor_get(v_a_3259_, 0);
v___x_3261_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l_Lean_LocalDecl_type(v_val_3260_);
v___x_3263_ = l_Lean_Meta_isProp(v___x_3262_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; uint8_t v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = lean_unbox(v_a_3264_);
lean_dec(v_a_3264_);
if (v___x_3265_ == 0)
{
v_a_3252_ = v_snd_3246_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = l_Lean_LocalDecl_fvarId(v_val_3260_);
v___x_3267_ = lean_array_push(v_snd_3246_, v___x_3266_);
v_a_3252_ = v___x_3267_;
goto v___jp_3251_;
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_del_object(v___x_3248_);
lean_dec(v_snd_3246_);
v_a_3268_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3263_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3263_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
v_a_3252_ = v_snd_3246_;
goto v___jp_3251_;
}
}
v___jp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 1, v_a_3252_);
lean_ctor_set(v___x_3248_, 0, v___x_3250_);
v___x_3254_ = v___x_3248_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_a_3252_);
v___x_3254_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((size_t)1ULL);
v___x_3256_ = lean_usize_add(v_i_3237_, v___x_3255_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3235_, v_sz_3236_, v___x_3256_, v___x_3254_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
return v___x_3257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3278_, lean_object* v_sz_3279_, lean_object* v_i_3280_, lean_object* v_b_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
size_t v_sz_boxed_3287_; size_t v_i_boxed_3288_; lean_object* v_res_3289_; 
v_sz_boxed_3287_ = lean_unbox_usize(v_sz_3279_);
lean_dec(v_sz_3279_);
v_i_boxed_3288_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_res_3289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3278_, v_sz_boxed_3287_, v_i_boxed_3288_, v_b_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec_ref(v_as_3278_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3290_, lean_object* v_n_3291_, lean_object* v_b_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
if (lean_obj_tag(v_n_3291_) == 0)
{
lean_object* v_cs_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3332_; 
v_cs_3298_ = lean_ctor_get(v_n_3291_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_n_3291_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3300_ = v_n_3291_;
v_isShared_3301_ = v_isSharedCheck_3332_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_cs_3298_);
lean_dec(v_n_3291_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3332_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; size_t v_sz_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_b_3292_);
v_sz_3304_ = lean_array_size(v_cs_3298_);
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3290_, v_cs_3298_, v_sz_3304_, v___x_3305_, v___x_3303_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v_cs_3298_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3323_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3323_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3323_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_fst_3311_; 
v_fst_3311_ = lean_ctor_get(v_a_3307_, 0);
if (lean_obj_tag(v_fst_3311_) == 0)
{
lean_object* v_snd_3312_; lean_object* v___x_3314_; 
v_snd_3312_ = lean_ctor_get(v_a_3307_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_a_3307_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
lean_ctor_set(v___x_3300_, 0, v_snd_3312_);
v___x_3314_ = v___x_3300_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_snd_3312_);
v___x_3314_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v___x_3316_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3314_);
v___x_3316_ = v___x_3309_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_val_3319_; lean_object* v___x_3321_; 
lean_inc_ref(v_fst_3311_);
lean_dec(v_a_3307_);
lean_del_object(v___x_3300_);
v_val_3319_ = lean_ctor_get(v_fst_3311_, 0);
lean_inc(v_val_3319_);
lean_dec_ref(v_fst_3311_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v_val_3319_);
v___x_3321_ = v___x_3309_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_val_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
else
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
lean_del_object(v___x_3300_);
v_a_3324_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3306_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3306_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
}
else
{
lean_object* v_vs_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3367_; 
v_vs_3333_ = lean_ctor_get(v_n_3291_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_n_3291_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3335_ = v_n_3291_;
v_isShared_3336_ = v_isSharedCheck_3367_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_vs_3333_);
lean_dec(v_n_3291_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3367_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; size_t v_sz_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v_b_3292_);
v_sz_3339_ = lean_array_size(v_vs_3333_);
v___x_3340_ = ((size_t)0ULL);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3333_, v_sz_3339_, v___x_3340_, v___x_3338_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v_vs_3333_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3358_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3344_ = v___x_3341_;
v_isShared_3345_ = v_isSharedCheck_3358_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3341_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3358_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v_fst_3346_; 
v_fst_3346_ = lean_ctor_get(v_a_3342_, 0);
if (lean_obj_tag(v_fst_3346_) == 0)
{
lean_object* v_snd_3347_; lean_object* v___x_3349_; 
v_snd_3347_ = lean_ctor_get(v_a_3342_, 1);
lean_inc(v_snd_3347_);
lean_dec(v_a_3342_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v_snd_3347_);
v___x_3349_ = v___x_3335_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_snd_3347_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3349_);
v___x_3351_ = v___x_3344_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v_val_3354_; lean_object* v___x_3356_; 
lean_inc_ref(v_fst_3346_);
lean_dec(v_a_3342_);
lean_del_object(v___x_3335_);
v_val_3354_ = lean_ctor_get(v_fst_3346_, 0);
lean_inc(v_val_3354_);
lean_dec_ref(v_fst_3346_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v_val_3354_);
v___x_3356_ = v___x_3344_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_val_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_del_object(v___x_3335_);
v_a_3359_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3341_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3341_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3368_, lean_object* v_as_3369_, size_t v_sz_3370_, size_t v_i_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3371_, v_sz_3370_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_b_3372_);
return v___x_3379_;
}
else
{
lean_object* v_snd_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3414_; 
v_snd_3380_ = lean_ctor_get(v_b_3372_, 1);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_b_3372_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v_b_3372_, 0);
lean_dec(v_unused_3415_);
v___x_3382_ = v_b_3372_;
v_isShared_3383_ = v_isSharedCheck_3414_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_snd_3380_);
lean_dec(v_b_3372_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3414_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_array_uget_borrowed(v_as_3369_, v_i_3371_);
lean_inc(v_snd_3380_);
lean_inc(v_a_3384_);
v___x_3385_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3368_, v_a_3384_, v_snd_3380_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3405_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3405_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
if (lean_obj_tag(v_a_3386_) == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_a_3386_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3390_);
v___x_3392_ = v___x_3382_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_snd_3380_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3392_);
v___x_3394_ = v___x_3388_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_del_object(v___x_3388_);
lean_dec(v_snd_3380_);
v_a_3397_ = lean_ctor_get(v_a_3386_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v_a_3386_);
v___x_3398_ = lean_box(0);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v_a_3397_);
lean_ctor_set(v___x_3382_, 0, v___x_3398_);
v___x_3400_ = v___x_3382_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_a_3397_);
v___x_3400_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
size_t v___x_3401_; size_t v___x_3402_; 
v___x_3401_ = ((size_t)1ULL);
v___x_3402_ = lean_usize_add(v_i_3371_, v___x_3401_);
v_i_3371_ = v___x_3402_;
v_b_3372_ = v___x_3400_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_del_object(v___x_3382_);
lean_dec(v_snd_3380_);
v_a_3406_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3385_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3385_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3416_, lean_object* v_as_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_b_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
size_t v_sz_boxed_3426_; size_t v_i_boxed_3427_; lean_object* v_res_3428_; 
v_sz_boxed_3426_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3427_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3416_, v_as_3417_, v_sz_boxed_3426_, v_i_boxed_3427_, v_b_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v_as_3417_);
lean_dec_ref(v_init_3416_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3429_, lean_object* v_n_3430_, lean_object* v_b_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3429_, v_n_3430_, v_b_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_init_3429_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3438_, size_t v_sz_3439_, size_t v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_usize_dec_lt(v_i_3440_, v_sz_3439_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_b_3441_);
return v___x_3448_;
}
else
{
lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3479_; 
v_snd_3449_ = lean_ctor_get(v_b_3441_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_b_3441_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v_b_3441_, 0);
lean_dec(v_unused_3480_);
v___x_3451_ = v_b_3441_;
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_dec(v_b_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3479_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v_a_3455_; lean_object* v_a_3462_; 
v___x_3453_ = lean_box(0);
v_a_3462_ = lean_array_uget_borrowed(v_as_3438_, v_i_3440_);
if (lean_obj_tag(v_a_3462_) == 0)
{
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
else
{
lean_object* v_val_3463_; uint8_t v___x_3464_; 
v_val_3463_ = lean_ctor_get(v_a_3462_, 0);
v___x_3464_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = l_Lean_LocalDecl_type(v_val_3463_);
v___x_3466_ = l_Lean_Meta_isProp(v___x_3465_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; uint8_t v___x_3468_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref(v___x_3466_);
v___x_3468_ = lean_unbox(v_a_3467_);
lean_dec(v_a_3467_);
if (v___x_3468_ == 0)
{
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = l_Lean_LocalDecl_fvarId(v_val_3463_);
v___x_3470_ = lean_array_push(v_snd_3449_, v___x_3469_);
v_a_3455_ = v___x_3470_;
goto v___jp_3454_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3451_);
lean_dec(v_snd_3449_);
v_a_3471_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3466_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3466_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
v_a_3455_ = v_snd_3449_;
goto v___jp_3454_;
}
}
v___jp_3454_:
{
lean_object* v___x_3457_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v_a_3455_);
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3457_ = v___x_3451_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_a_3455_);
v___x_3457_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
size_t v___x_3458_; size_t v___x_3459_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3440_, v___x_3458_);
v_i_3440_ = v___x_3459_;
v_b_3441_ = v___x_3457_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3481_, lean_object* v_sz_3482_, lean_object* v_i_3483_, lean_object* v_b_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
size_t v_sz_boxed_3490_; size_t v_i_boxed_3491_; lean_object* v_res_3492_; 
v_sz_boxed_3490_ = lean_unbox_usize(v_sz_3482_);
lean_dec(v_sz_3482_);
v_i_boxed_3491_ = lean_unbox_usize(v_i_3483_);
lean_dec(v_i_3483_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3481_, v_sz_boxed_3490_, v_i_boxed_3491_, v_b_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_as_3481_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3493_, size_t v_sz_3494_, size_t v_i_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_lt(v_i_3495_, v_sz_3494_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_b_3496_);
return v___x_3503_;
}
else
{
lean_object* v_snd_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3534_; 
v_snd_3504_ = lean_ctor_get(v_b_3496_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_b_3496_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v_b_3496_, 0);
lean_dec(v_unused_3535_);
v___x_3506_ = v_b_3496_;
v_isShared_3507_ = v_isSharedCheck_3534_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_snd_3504_);
lean_dec(v_b_3496_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3534_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v_a_3510_; lean_object* v_a_3517_; 
v___x_3508_ = lean_box(0);
v_a_3517_ = lean_array_uget_borrowed(v_as_3493_, v_i_3495_);
if (lean_obj_tag(v_a_3517_) == 0)
{
v_a_3510_ = v_snd_3504_;
goto v___jp_3509_;
}
else
{
lean_object* v_val_3518_; uint8_t v___x_3519_; 
v_val_3518_ = lean_ctor_get(v_a_3517_, 0);
v___x_3519_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3518_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = l_Lean_LocalDecl_type(v_val_3518_);
v___x_3521_ = l_Lean_Meta_isProp(v___x_3520_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; uint8_t v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = lean_unbox(v_a_3522_);
lean_dec(v_a_3522_);
if (v___x_3523_ == 0)
{
v_a_3510_ = v_snd_3504_;
goto v___jp_3509_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = l_Lean_LocalDecl_fvarId(v_val_3518_);
v___x_3525_ = lean_array_push(v_snd_3504_, v___x_3524_);
v_a_3510_ = v___x_3525_;
goto v___jp_3509_;
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_del_object(v___x_3506_);
lean_dec(v_snd_3504_);
v_a_3526_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3521_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3521_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
v_a_3510_ = v_snd_3504_;
goto v___jp_3509_;
}
}
v___jp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_a_3510_);
lean_ctor_set(v___x_3506_, 0, v___x_3508_);
v___x_3512_ = v___x_3506_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_a_3510_);
v___x_3512_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
size_t v___x_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3495_, v___x_3513_);
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3493_, v_sz_3494_, v___x_3514_, v___x_3512_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
return v___x_3515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3536_, lean_object* v_sz_3537_, lean_object* v_i_3538_, lean_object* v_b_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
size_t v_sz_boxed_3545_; size_t v_i_boxed_3546_; lean_object* v_res_3547_; 
v_sz_boxed_3545_ = lean_unbox_usize(v_sz_3537_);
lean_dec(v_sz_3537_);
v_i_boxed_3546_ = lean_unbox_usize(v_i_3538_);
lean_dec(v_i_3538_);
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3536_, v_sz_boxed_3545_, v_i_boxed_3546_, v_b_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v_as_3536_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3548_, lean_object* v_init_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_root_3555_; lean_object* v_tail_3556_; lean_object* v___x_3557_; 
v_root_3555_ = lean_ctor_get(v_t_3548_, 0);
lean_inc_ref(v_root_3555_);
v_tail_3556_ = lean_ctor_get(v_t_3548_, 1);
lean_inc_ref(v_tail_3556_);
lean_dec_ref(v_t_3548_);
lean_inc_ref(v_init_3549_);
v___x_3557_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3549_, v_root_3555_, v_init_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec_ref(v_init_3549_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3594_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3594_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3594_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
if (lean_obj_tag(v_a_3558_) == 0)
{
lean_object* v_a_3562_; lean_object* v___x_3564_; 
lean_dec_ref(v_tail_3556_);
v_a_3562_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v_a_3558_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_a_3562_);
v___x_3564_ = v___x_3560_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; size_t v_sz_3569_; size_t v___x_3570_; lean_object* v___x_3571_; 
lean_del_object(v___x_3560_);
v_a_3566_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_a_3566_);
lean_dec_ref(v_a_3558_);
v___x_3567_ = lean_box(0);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v_a_3566_);
v_sz_3569_ = lean_array_size(v_tail_3556_);
v___x_3570_ = ((size_t)0ULL);
v___x_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3556_, v_sz_3569_, v___x_3570_, v___x_3568_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec_ref(v_tail_3556_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3585_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3585_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3585_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_fst_3576_; 
v_fst_3576_ = lean_ctor_get(v_a_3572_, 0);
if (lean_obj_tag(v_fst_3576_) == 0)
{
lean_object* v_snd_3577_; lean_object* v___x_3579_; 
v_snd_3577_ = lean_ctor_get(v_a_3572_, 1);
lean_inc(v_snd_3577_);
lean_dec(v_a_3572_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_snd_3577_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_snd_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
else
{
lean_object* v_val_3581_; lean_object* v___x_3583_; 
lean_inc_ref(v_fst_3576_);
lean_dec(v_a_3572_);
v_val_3581_ = lean_ctor_get(v_fst_3576_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v_fst_3576_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v_val_3581_);
v___x_3583_ = v___x_3574_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_val_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
v_a_3586_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3571_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3571_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v_tail_3556_);
v_a_3595_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3557_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3557_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3603_, lean_object* v_init_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3603_, v_init_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_lctx_3616_; lean_object* v_decls_3617_; lean_object* v_result_3618_; lean_object* v___x_3619_; 
v_lctx_3616_ = lean_ctor_get(v_a_3611_, 2);
v_decls_3617_ = lean_ctor_get(v_lctx_3616_, 1);
v_result_3618_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
lean_inc_ref(v_decls_3617_);
v___x_3619_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3617_, v_result_3618_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l_Lean_Meta_getPropHyps(v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
return v_res_3625_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3630_ = l_Lean_MessageData_ofFormat(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3633_, lean_object* v___x_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v___x_3640_; 
lean_inc(v___x_3634_);
lean_inc(v_mvarId_3633_);
v___x_3640_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3633_, v___x_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; 
lean_dec_ref(v___x_3640_);
lean_inc(v_mvarId_3633_);
v___x_3641_ = l_Lean_MVarId_getType(v_mvarId_3633_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref(v___x_3641_);
v___x_3643_ = lean_box(0);
v___x_3644_ = l_Lean_Meta_synthInstance(v_a_3642_, v___x_3643_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
lean_inc(v_mvarId_3633_);
v___x_3646_ = l_Lean_mkMVar(v_mvarId_3633_);
v___x_3647_ = l_Lean_Meta_isExprDefEq(v___x_3646_, v_a_3645_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3659_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3659_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3659_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_unbox(v_a_3648_);
lean_dec(v_a_3648_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_del_object(v___x_3650_);
v___x_3653_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3654_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3634_, v_mvarId_3633_, v___x_3653_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
return v___x_3654_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
lean_dec(v___x_3634_);
lean_dec(v_mvarId_3633_);
v___x_3655_ = lean_box(0);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3655_);
v___x_3657_ = v___x_3650_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v___x_3634_);
lean_dec(v_mvarId_3633_);
v_a_3660_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3647_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3647_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v___x_3634_);
lean_dec(v_mvarId_3633_);
v_a_3668_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3644_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3644_);
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
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v___x_3634_);
lean_dec(v_mvarId_3633_);
v_a_3676_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3641_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3641_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_dec(v___x_3634_);
lean_dec(v_mvarId_3633_);
return v___x_3640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3684_, lean_object* v___x_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3684_, v___x_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___x_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; 
v___x_3701_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3695_);
v___f_3702_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3702_, 0, v_mvarId_3695_);
lean_closure_set(v___f_3702_, 1, v___x_3701_);
v___x_3703_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3695_, v___f_3702_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_MVarId_inferInstance(v_mvarId_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3711_){
_start:
{
switch(lean_obj_tag(v_x_3711_))
{
case 0:
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
return v___x_3712_;
}
case 1:
{
lean_object* v___x_3713_; 
v___x_3713_ = lean_unsigned_to_nat(1u);
return v___x_3713_;
}
default: 
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_unsigned_to_nat(2u);
return v___x_3714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3715_);
lean_dec(v_x_3715_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3717_, lean_object* v_k_3718_){
_start:
{
if (lean_obj_tag(v_t_3717_) == 2)
{
lean_object* v_mvarId_3719_; lean_object* v___x_3720_; 
v_mvarId_3719_ = lean_ctor_get(v_t_3717_, 0);
lean_inc(v_mvarId_3719_);
lean_dec_ref(v_t_3717_);
v___x_3720_ = lean_apply_1(v_k_3718_, v_mvarId_3719_);
return v___x_3720_;
}
else
{
lean_dec(v_t_3717_);
return v_k_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3721_, lean_object* v_ctorIdx_3722_, lean_object* v_t_3723_, lean_object* v_h_3724_, lean_object* v_k_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3723_, v_k_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3727_, lean_object* v_ctorIdx_3728_, lean_object* v_t_3729_, lean_object* v_h_3730_, lean_object* v_k_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3727_, v_ctorIdx_3728_, v_t_3729_, v_h_3730_, v_k_3731_);
lean_dec(v_ctorIdx_3728_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3733_, lean_object* v_closed_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3733_, v_closed_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3736_, lean_object* v_t_3737_, lean_object* v_h_3738_, lean_object* v_closed_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3737_, v_closed_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3741_, lean_object* v_noChange_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3741_, v_noChange_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3744_, lean_object* v_t_3745_, lean_object* v_h_3746_, lean_object* v_noChange_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3745_, v_noChange_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3749_, lean_object* v_modified_3750_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3749_, v_modified_3750_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3752_, lean_object* v_t_3753_, lean_object* v_h_3754_, lean_object* v_modified_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3753_, v_modified_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v_a_3773_; lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_MVarId_getType(v_g_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3776_);
v___x_3778_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = lean_mk_empty_array_with_capacity(v___x_3779_);
v___x_3781_ = lean_array_push(v___x_3780_, v_a_3777_);
v___x_3782_ = l_Lean_Meta_mkAppM(v___x_3778_, v___x_3781_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref(v___x_3782_);
v___x_3784_ = lean_box(0);
v___x_3785_ = l_Lean_Meta_synthInstance(v_a_3783_, v___x_3784_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3794_; 
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v___x_3785_, 0);
lean_dec(v_unused_3795_);
v___x_3787_ = v___x_3785_;
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v___x_3785_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3794_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
uint8_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3789_ = 1;
v___x_3790_ = lean_box(v___x_3789_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3790_);
v___x_3792_ = v___x_3787_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
else
{
lean_object* v_a_3796_; 
v_a_3796_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3785_);
v_a_3773_ = v_a_3796_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3797_; 
v_a_3797_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3797_);
lean_dec_ref(v___x_3782_);
v_a_3773_ = v_a_3797_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3798_);
lean_dec_ref(v___x_3776_);
v_a_3773_ = v_a_3798_;
goto v___jp_3772_;
}
v___jp_3766_:
{
if (v___y_3768_ == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_dec_ref(v___y_3767_);
v___x_3769_ = lean_box(v___y_3768_);
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
return v___x_3770_;
}
else
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___y_3767_);
return v___x_3771_;
}
}
v___jp_3772_:
{
uint8_t v___x_3774_; 
v___x_3774_ = l_Lean_Exception_isInterrupt(v_a_3773_);
if (v___x_3774_ == 0)
{
uint8_t v___x_3775_; 
lean_inc_ref(v_a_3773_);
v___x_3775_ = l_Lean_Exception_isRuntime(v_a_3773_);
v___y_3767_ = v_a_3773_;
v___y_3768_ = v___x_3775_;
goto v___jp_3766_;
}
else
{
v___y_3767_ = v_a_3773_;
v___y_3768_ = v___x_3774_;
goto v___jp_3766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_MVarId_isSubsingleton(v_g_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3822_ = ((lean_object*)(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3823_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3824_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3825_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3822_, v___x_3823_, v___x_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3827_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_tactic_skipAssignedInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_tactic_skipAssignedInstances);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Util(builtin);
}
#ifdef __cplusplus
}
#endif
