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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "terminalTacticsAsSorry"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(232, 90, 215, 151, 242, 202, 226, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 139, .m_capacity = 139, .m_length = 138, .m_data = "when enabled, terminal tactics such as `grind` and `omega` are replaced with `sorry`. Useful for debugging and fixing bootstrapping issues"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 233, 55, 94, 186, 188, 252, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 217, 134, 189, 91, 246, 107, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Util"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 80, 134, 96, 135, 241, 87, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(12, 105, 212, 82, 205, 98, 36, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 108, 151, 68, 40, 185, 49, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(69, 35, 20, 40, 241, 13, 114, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 161, 8, 73, 13, 24, 41, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 240, 21, 38, 82, 97, 50, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(240, 251, 182, 143, 63, 208, 115, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(124, 226, 182, 237, 212, 141, 147, 41)}};
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
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "skipAssignedInstances"};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(166, 172, 231, 36, 182, 217, 37, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 113, .m_capacity = 113, .m_length = 112, .m_data = "in the `rw` and `simp` tactics, if an instance implicit argument is assigned, do not try to synthesize instance."};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 82, 89, 96, 183, 68, 254, 125)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 5, 107, 131, 111, 226, 218, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag(lean_object* v_mvarId_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_MVarId_getDecl(v_mvarId_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_userName_70_; lean_object* v___x_72_; 
v_userName_70_ = lean_ctor_get(v_a_66_, 0);
lean_inc(v_userName_70_);
lean_dec(v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v_userName_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_userName_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_65_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_65_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getTag___boxed(lean_object* v_mvarId_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_MVarId_getTag(v_mvarId_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg(lean_object* v_mvarId_90_, lean_object* v_tag_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_cache_96_; lean_object* v_zetaDeltaFVarIds_97_; lean_object* v_postponed_98_; lean_object* v_diag_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_110_; 
v___x_94_ = lean_st_ref_take(v_a_92_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
v_cache_96_ = lean_ctor_get(v___x_94_, 1);
v_zetaDeltaFVarIds_97_ = lean_ctor_get(v___x_94_, 2);
v_postponed_98_ = lean_ctor_get(v___x_94_, 3);
v_diag_99_ = lean_ctor_get(v___x_94_, 4);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_110_ == 0)
{
v___x_101_ = v___x_94_;
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_diag_99_);
lean_inc(v_postponed_98_);
lean_inc(v_zetaDeltaFVarIds_97_);
lean_inc(v_cache_96_);
lean_inc(v_mctx_95_);
lean_dec(v___x_94_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_95_, v_mvarId_90_, v_tag_91_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_cache_96_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_zetaDeltaFVarIds_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v_postponed_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_diag_99_);
v___x_105_ = v_reuseFailAlloc_109_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_st_ref_set(v_a_92_, v___x_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___redArg___boxed(lean_object* v_mvarId_111_, lean_object* v_tag_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_MVarId_setTag___redArg(v_mvarId_111_, v_tag_112_, v_a_113_);
lean_dec(v_a_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag(lean_object* v_mvarId_116_, lean_object* v_tag_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_MVarId_setTag___redArg(v_mvarId_116_, v_tag_117_, v_a_119_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_setTag___boxed(lean_object* v_mvarId_124_, lean_object* v_tag_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_MVarId_setTag(v_mvarId_124_, v_tag_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0(lean_object* v_suffix_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_erase_macro_scopes(v_suffix_132_);
v___x_135_ = l_Lean_Name_append(v_x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_136_, lean_object* v_suffix_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Lean_Name_hasMacroScopes(v_tag_136_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_appendTag___lam__0(v_suffix_137_, v_tag_136_);
return v___x_139_;
}
else
{
lean_object* v_view_140_; lean_object* v_name_141_; lean_object* v_imported_142_; lean_object* v_ctx_143_; lean_object* v_scopes_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
v_view_140_ = l_Lean_extractMacroScopes(v_tag_136_);
v_name_141_ = lean_ctor_get(v_view_140_, 0);
v_imported_142_ = lean_ctor_get(v_view_140_, 1);
v_ctx_143_ = lean_ctor_get(v_view_140_, 2);
v_scopes_144_ = lean_ctor_get(v_view_140_, 3);
v_isSharedCheck_153_ = !lean_is_exclusive(v_view_140_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v_view_140_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_scopes_144_);
lean_inc(v_ctx_143_);
lean_inc(v_imported_142_);
lean_inc(v_name_141_);
lean_dec(v_view_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = l_Lean_Meta_appendTag___lam__0(v_suffix_137_, v_name_141_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_imported_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_ctx_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_scopes_144_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_MacroScopesView_review(v___x_150_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_154_, lean_object* v_suffix_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; 
lean_inc(v_mvarId_154_);
v___x_161_ = l_Lean_MVarId_getTag(v_mvarId_154_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref(v___x_161_);
v___x_163_ = l_Lean_Meta_appendTag(v_a_162_, v_suffix_155_);
v___x_164_ = l_Lean_MVarId_setTag___redArg(v_mvarId_154_, v___x_163_, v_a_157_);
return v___x_164_;
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_suffix_155_);
lean_dec(v_mvarId_154_);
v_a_165_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_161_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_161_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_173_, lean_object* v_suffix_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_appendTagSuffix(v_mvarId_173_, v_suffix_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_181_, lean_object* v_tag_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_type_181_);
v___x_189_ = 2;
v___x_190_ = l_Lean_Meta_mkFreshExprMVar(v___x_188_, v___x_189_, v_tag_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_191_, lean_object* v_tag_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_191_, v_tag_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_198_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_208_, lean_object* v_mvarId_209_, lean_object* v_msg_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_211_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_212_ = l_Lean_MessageData_ofName(v_tacticName_208_);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v_msg_210_);
v___x_217_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v_mvarId_209_);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; lean_object* v_env_228_; lean_object* v___x_229_; lean_object* v_mctx_230_; lean_object* v_lctx_231_; lean_object* v_options_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_227_ = lean_st_ref_get(v___y_225_);
v_env_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc_ref(v_env_228_);
lean_dec(v___x_227_);
v___x_229_ = lean_st_ref_get(v___y_223_);
v_mctx_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_mctx_230_);
lean_dec(v___x_229_);
v_lctx_231_ = lean_ctor_get(v___y_222_, 2);
v_options_232_ = lean_ctor_get(v___y_224_, 2);
lean_inc_ref(v_options_232_);
lean_inc_ref(v_lctx_231_);
v___x_233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_233_, 0, v_env_228_);
lean_ctor_set(v___x_233_, 1, v_mctx_230_);
lean_ctor_set(v___x_233_, 2, v_lctx_231_);
lean_ctor_set(v___x_233_, 3, v_options_232_);
v___x_234_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v_msgData_221_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_ref_249_; lean_object* v___x_250_; lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
v_ref_249_ = lean_ctor_get(v___y_246_, 5);
v___x_250_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_259_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_inc(v_ref_249_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_ref_249_);
lean_ctor_set(v___x_255_, 1, v_a_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 1);
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_269_ = l_Lean_stringToMessageData(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_270_, lean_object* v_mvarId_271_, lean_object* v_msg_x3f_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
if (lean_obj_tag(v_msg_x3f_272_) == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_278_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_279_ = l_Lean_MessageData_ofName(v_tacticName_270_);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_mvarId_271_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_284_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_285_;
}
else
{
lean_object* v_val_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_val_286_ = lean_ctor_get(v_msg_x3f_272_, 0);
lean_inc(v_val_286_);
lean_dec_ref(v_msg_x3f_272_);
v___x_287_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_270_, v_mvarId_271_, v_val_286_);
v___x_288_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_287_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_289_, lean_object* v_mvarId_290_, lean_object* v_msg_x3f_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_289_, v_mvarId_290_, v_msg_x3f_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_298_, lean_object* v_tacticName_299_, lean_object* v_mvarId_300_, lean_object* v_msg_x3f_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_299_, v_mvarId_300_, v_msg_x3f_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_308_, lean_object* v_tacticName_309_, lean_object* v_mvarId_310_, lean_object* v_msg_x3f_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_308_, v_tacticName_309_, v_mvarId_310_, v_msg_x3f_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_318_, lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_326_, lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_326_, v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_336_ = l_Lean_stringToMessageData(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_340_, lean_object* v_ex_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_nestedMsg_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_msg_353_; lean_object* v_kind_354_; uint8_t v___x_355_; 
v_nestedMsg_347_ = l_Lean_Exception_toMessageData(v_ex_341_);
v___x_348_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_349_ = l_Lean_MessageData_ofName(v_tacticName_340_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_inc_ref(v_nestedMsg_347_);
v_msg_353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_353_, 0, v___x_352_);
lean_ctor_set(v_msg_353_, 1, v_nestedMsg_347_);
v_kind_354_ = l_Lean_MessageData_kind(v_nestedMsg_347_);
lean_dec_ref(v_nestedMsg_347_);
v___x_355_ = l_Lean_Name_isAnonymous(v_kind_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_357_ = l_Lean_Name_append(v___x_356_, v_kind_354_);
v___x_358_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_msg_353_);
v___x_359_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_358_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_359_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_kind_354_);
v___x_360_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_353_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_361_, lean_object* v_ex_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_361_, v_ex_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_369_, lean_object* v_tacticName_370_, lean_object* v_ex_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_370_, v_ex_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_378_, lean_object* v_tacticName_379_, lean_object* v_ex_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_378_, v_tacticName_379_, v_ex_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
return v_res_386_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_387_, lean_object* v_i_388_, lean_object* v_k_389_){
_start:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_get_size(v_keys_387_);
v___x_391_ = lean_nat_dec_lt(v_i_388_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v_i_388_);
return v___x_391_;
}
else
{
lean_object* v_k_x27_392_; uint8_t v___x_393_; 
v_k_x27_392_ = lean_array_fget_borrowed(v_keys_387_, v_i_388_);
v___x_393_ = l_Lean_instBEqMVarId_beq(v_k_389_, v_k_x27_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_i_388_, v___x_394_);
lean_dec(v_i_388_);
v_i_388_ = v___x_395_;
goto _start;
}
else
{
lean_dec(v_i_388_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_397_, lean_object* v_i_398_, lean_object* v_k_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_397_, v_i_398_, v_k_399_);
lean_dec(v_k_399_);
lean_dec_ref(v_keys_397_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; 
v___x_402_ = ((size_t)5ULL);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_shift_left(v___x_403_, v___x_402_);
return v___x_404_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; 
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_407_ = lean_usize_sub(v___x_406_, v___x_405_);
return v___x_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v_es_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v_j_416_; lean_object* v___x_417_; 
v_es_411_ = lean_ctor_get(v_x_408_, 0);
v___x_412_ = lean_box(2);
v___x_413_ = ((size_t)5ULL);
v___x_414_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_415_ = lean_usize_land(v_x_409_, v___x_414_);
v_j_416_ = lean_usize_to_nat(v___x_415_);
v___x_417_ = lean_array_get_borrowed(v___x_412_, v_es_411_, v_j_416_);
lean_dec(v_j_416_);
switch(lean_obj_tag(v___x_417_))
{
case 0:
{
lean_object* v_key_418_; uint8_t v___x_419_; 
v_key_418_ = lean_ctor_get(v___x_417_, 0);
v___x_419_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_key_418_);
return v___x_419_;
}
case 1:
{
lean_object* v_node_420_; size_t v___x_421_; 
v_node_420_ = lean_ctor_get(v___x_417_, 0);
v___x_421_ = lean_usize_shift_right(v_x_409_, v___x_413_);
v_x_408_ = v_node_420_;
v_x_409_ = v___x_421_;
goto _start;
}
default: 
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
}
else
{
lean_object* v_ks_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_ks_424_ = lean_ctor_get(v_x_408_, 0);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_424_, v___x_425_, v_x_410_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_595__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_595__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_427_, v_x_595__boxed_430_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint64_t v___x_435_; size_t v___x_436_; uint8_t v___x_437_; 
v___x_435_ = l_Lean_instHashableMVarId_hash(v_x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_433_, v___x_436_, v_x_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_x_438_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_mctx_446_; lean_object* v_eAssignment_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_445_ = lean_st_ref_get(v___y_443_);
v_mctx_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc_ref(v_mctx_446_);
lean_dec(v___x_445_);
v_eAssignment_447_ = lean_ctor_get(v_mctx_446_, 8);
lean_inc_ref(v_eAssignment_447_);
lean_dec_ref(v_mctx_446_);
v___x_448_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_447_, v_mvarId_442_);
lean_dec_ref(v_eAssignment_447_);
v___x_449_ = lean_box(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec(v_mvarId_451_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_462_ = l_Lean_MessageData_ofFormat(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_464_ = l_Lean_MessageData_note(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_470_, lean_object* v_tacticName_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v___x_477_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_470_, v_a_473_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint8_t v___x_482_; 
v___x_482_ = lean_unbox(v_a_478_);
lean_dec(v_a_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_tacticName_471_);
lean_dec(v_mvarId_470_);
v___x_483_ = lean_box(0);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_del_object(v___x_480_);
v___x_487_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_488_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_471_, v_mvarId_470_, v___x_487_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
return v___x_488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_490_, lean_object* v_tacticName_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_490_, v_tacticName_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_498_, v___y_500_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_mvarId_505_);
return v_res_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_513_, v_x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_516_, v_x_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_x_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_521_, lean_object* v_x_522_, size_t v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_522_, v_x_523_, v_x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_768__boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_768__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_526_, v_x_527_, v_x_768__boxed_530_, v_x_529_);
lean_dec(v_x_529_);
lean_dec_ref(v_x_527_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_533_, lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_heq_536_, lean_object* v_i_537_, lean_object* v_k_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_534_, v_i_537_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_540_, lean_object* v_keys_541_, lean_object* v_vals_542_, lean_object* v_heq_543_, lean_object* v_i_544_, lean_object* v_k_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_540_, v_keys_541_, v_vals_542_, v_heq_543_, v_i_544_, v_k_545_);
lean_dec(v_k_545_);
lean_dec_ref(v_vals_542_);
lean_dec_ref(v_keys_541_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_MVarId_getDecl(v_mvarId_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_type_559_; lean_object* v___x_561_; 
v_type_559_ = lean_ctor_get(v_a_555_, 2);
lean_inc_ref(v_type_559_);
lean_dec(v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_type_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_type_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_554_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_554_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_MVarId_getType(v_mvarId_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Expr_hasMVar(v_e_579_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_e_579_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v_mctx_585_; lean_object* v___x_586_; lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v_cache_590_; lean_object* v_zetaDeltaFVarIds_591_; lean_object* v_postponed_592_; lean_object* v_diag_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_602_; 
v___x_584_ = lean_st_ref_get(v___y_580_);
v_mctx_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_mctx_585_);
lean_dec(v___x_584_);
v___x_586_ = l_Lean_instantiateMVarsCore(v_mctx_585_, v_e_579_);
v_fst_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v___x_586_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v___x_586_);
v___x_589_ = lean_st_ref_take(v___y_580_);
v_cache_590_ = lean_ctor_get(v___x_589_, 1);
v_zetaDeltaFVarIds_591_ = lean_ctor_get(v___x_589_, 2);
v_postponed_592_ = lean_ctor_get(v___x_589_, 3);
v_diag_593_ = lean_ctor_get(v___x_589_, 4);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_603_);
v___x_595_ = v___x_589_;
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_diag_593_);
lean_inc(v_postponed_592_);
lean_inc(v_zetaDeltaFVarIds_591_);
lean_inc(v_cache_590_);
lean_dec(v___x_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_602_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v_snd_588_);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_snd_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_cache_590_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_zetaDeltaFVarIds_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_postponed_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_diag_593_);
v___x_598_ = v_reuseFailAlloc_601_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_st_ref_set(v___y_580_, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_fst_587_);
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_604_, v___y_605_);
lean_dec(v___y_605_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_608_, v___y_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_MVarId_getType(v_mvarId_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_628_);
lean_inc(v_a_626_);
lean_inc_ref(v_a_625_);
lean_inc(v_a_624_);
lean_inc_ref(v_a_623_);
v___x_630_ = lean_whnf(v_a_629_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_631_, v_a_624_);
return v___x_632_;
}
else
{
return v___x_630_;
}
}
else
{
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_MVarId_getType_x27(v_mvarId_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_706_ = 0;
v___x_707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_708_ = l_Lean_registerTraceClass(v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_711_, v_x_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_735_, v_x_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_743_, lean_object* v_mvarId_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_752_, lean_object* v_mvarId_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_752_, v_mvarId_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
lean_object* v_ks_765_; lean_object* v_vs_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_790_; 
v_ks_765_ = lean_ctor_get(v_x_761_, 0);
v_vs_766_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_790_ == 0)
{
v___x_768_ = v_x_761_;
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_vs_766_);
lean_inc(v_ks_765_);
lean_dec(v_x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = lean_array_get_size(v_ks_765_);
v___x_771_ = lean_nat_dec_lt(v_x_762_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec(v_x_762_);
v___x_772_ = lean_array_push(v_ks_765_, v_x_763_);
v___x_773_ = lean_array_push(v_vs_766_, v_x_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_773_);
lean_ctor_set(v___x_768_, 0, v___x_772_);
v___x_775_ = v___x_768_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
else
{
lean_object* v_k_x27_777_; uint8_t v___x_778_; 
v_k_x27_777_ = lean_array_fget_borrowed(v_ks_765_, v_x_762_);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_763_, v_k_x27_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_769_ == 0)
{
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_ks_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_vs_766_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_x_762_, v___x_781_);
lean_dec(v_x_762_);
v_x_761_ = v___x_780_;
v_x_762_ = v___x_782_;
goto _start;
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_785_ = lean_array_fset(v_ks_765_, v_x_762_, v_x_763_);
v___x_786_ = lean_array_fset(v_vs_766_, v_x_762_, v_x_764_);
lean_dec(v_x_762_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___x_786_);
lean_ctor_set(v___x_768_, 0, v___x_785_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_791_, lean_object* v_k_792_, lean_object* v_v_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_791_, v___x_794_, v_k_792_, v_v_793_);
return v___x_795_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_797_, size_t v_x_798_, size_t v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_es_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; size_t v___x_806_; lean_object* v_j_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_es_802_ = lean_ctor_get(v_x_797_, 0);
v___x_803_ = ((size_t)5ULL);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_806_ = lean_usize_land(v_x_798_, v___x_805_);
v_j_807_ = lean_usize_to_nat(v___x_806_);
v___x_808_ = lean_array_get_size(v_es_802_);
v___x_809_ = lean_nat_dec_lt(v_j_807_, v___x_808_);
if (v___x_809_ == 0)
{
lean_dec(v_j_807_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
return v_x_797_;
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_846_; 
lean_inc_ref(v_es_802_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_x_797_, 0);
lean_dec(v_unused_847_);
v___x_811_ = v_x_797_;
v_isShared_812_ = v_isSharedCheck_846_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_x_797_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_846_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_v_813_; lean_object* v___x_814_; lean_object* v_xs_x27_815_; lean_object* v___y_817_; 
v_v_813_ = lean_array_fget(v_es_802_, v_j_807_);
v___x_814_ = lean_box(0);
v_xs_x27_815_ = lean_array_fset(v_es_802_, v_j_807_, v___x_814_);
switch(lean_obj_tag(v_v_813_))
{
case 0:
{
lean_object* v_key_822_; lean_object* v_val_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_833_; 
v_key_822_ = lean_ctor_get(v_v_813_, 0);
v_val_823_ = lean_ctor_get(v_v_813_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_v_813_);
if (v_isSharedCheck_833_ == 0)
{
v___x_825_ = v_v_813_;
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_val_823_);
lean_inc(v_key_822_);
lean_dec(v_v_813_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_833_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; 
v___x_827_ = l_Lean_instBEqMVarId_beq(v_x_800_, v_key_822_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_825_);
v___x_828_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_822_, v_val_823_, v_x_800_, v_x_801_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
v___y_817_ = v___x_829_;
goto v___jp_816_;
}
else
{
lean_object* v___x_831_; 
lean_dec(v_val_823_);
lean_dec(v_key_822_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_x_801_);
lean_ctor_set(v___x_825_, 0, v_x_800_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_x_800_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_x_801_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v___y_817_ = v___x_831_;
goto v___jp_816_;
}
}
}
}
case 1:
{
lean_object* v_node_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_844_; 
v_node_834_ = lean_ctor_get(v_v_813_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_813_);
if (v_isSharedCheck_844_ == 0)
{
v___x_836_ = v_v_813_;
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_node_834_);
lean_dec(v_v_813_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_844_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_838_ = lean_usize_shift_right(v_x_798_, v___x_803_);
v___x_839_ = lean_usize_add(v_x_799_, v___x_804_);
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_834_, v___x_838_, v___x_839_, v_x_800_, v_x_801_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_840_);
v___x_842_ = v___x_836_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
v___y_817_ = v___x_842_;
goto v___jp_816_;
}
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_x_800_);
lean_ctor_set(v___x_845_, 1, v_x_801_);
v___y_817_ = v___x_845_;
goto v___jp_816_;
}
}
v___jp_816_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_array_fset(v_xs_x27_815_, v_j_807_, v___y_817_);
lean_dec(v_j_807_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_818_);
v___x_820_ = v___x_811_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_ks_848_; lean_object* v_vs_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_869_; 
v_ks_848_ = lean_ctor_get(v_x_797_, 0);
v_vs_849_ = lean_ctor_get(v_x_797_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_869_ == 0)
{
v___x_851_ = v_x_797_;
v_isShared_852_ = v_isSharedCheck_869_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_vs_849_);
lean_inc(v_ks_848_);
lean_dec(v_x_797_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_869_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_ks_848_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_vs_849_);
v___x_854_ = v_reuseFailAlloc_868_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v_newNode_855_; uint8_t v___y_857_; size_t v___x_863_; uint8_t v___x_864_; 
v_newNode_855_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_854_, v_x_800_, v_x_801_);
v___x_863_ = ((size_t)7ULL);
v___x_864_ = lean_usize_dec_le(v___x_863_, v_x_799_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_855_);
v___x_866_ = lean_unsigned_to_nat(4u);
v___x_867_ = lean_nat_dec_lt(v___x_865_, v___x_866_);
lean_dec(v___x_865_);
v___y_857_ = v___x_867_;
goto v___jp_856_;
}
else
{
v___y_857_ = v___x_864_;
goto v___jp_856_;
}
v___jp_856_:
{
if (v___y_857_ == 0)
{
lean_object* v_ks_858_; lean_object* v_vs_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_ks_858_ = lean_ctor_get(v_newNode_855_, 0);
lean_inc_ref(v_ks_858_);
v_vs_859_ = lean_ctor_get(v_newNode_855_, 1);
lean_inc_ref(v_vs_859_);
lean_dec_ref(v_newNode_855_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_862_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_799_, v_ks_858_, v_vs_859_, v___x_860_, v___x_861_);
lean_dec_ref(v_vs_859_);
lean_dec_ref(v_ks_858_);
return v___x_862_;
}
else
{
return v_newNode_855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_870_, lean_object* v_keys_871_, lean_object* v_vals_872_, lean_object* v_i_873_, lean_object* v_entries_874_){
_start:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_array_get_size(v_keys_871_);
v___x_876_ = lean_nat_dec_lt(v_i_873_, v___x_875_);
if (v___x_876_ == 0)
{
lean_dec(v_i_873_);
return v_entries_874_;
}
else
{
lean_object* v_k_877_; lean_object* v_v_878_; uint64_t v___x_879_; size_t v_h_880_; size_t v___x_881_; lean_object* v___x_882_; size_t v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v_h_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_k_877_ = lean_array_fget_borrowed(v_keys_871_, v_i_873_);
v_v_878_ = lean_array_fget_borrowed(v_vals_872_, v_i_873_);
v___x_879_ = l_Lean_instHashableMVarId_hash(v_k_877_);
v_h_880_ = lean_uint64_to_usize(v___x_879_);
v___x_881_ = ((size_t)5ULL);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = ((size_t)1ULL);
v___x_884_ = lean_usize_sub(v_depth_870_, v___x_883_);
v___x_885_ = lean_usize_mul(v___x_881_, v___x_884_);
v_h_886_ = lean_usize_shift_right(v_h_880_, v___x_885_);
v___x_887_ = lean_nat_add(v_i_873_, v___x_882_);
lean_dec(v_i_873_);
lean_inc(v_v_878_);
lean_inc(v_k_877_);
v___x_888_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_874_, v_h_886_, v_depth_870_, v_k_877_, v_v_878_);
v_i_873_ = v___x_887_;
v_entries_874_ = v___x_888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_i_893_, lean_object* v_entries_894_){
_start:
{
size_t v_depth_boxed_895_; lean_object* v_res_896_; 
v_depth_boxed_895_ = lean_unbox_usize(v_depth_890_);
lean_dec(v_depth_890_);
v_res_896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_895_, v_keys_891_, v_vals_892_, v_i_893_, v_entries_894_);
lean_dec_ref(v_vals_892_);
lean_dec_ref(v_keys_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_){
_start:
{
size_t v_x_1015__boxed_902_; size_t v_x_1016__boxed_903_; lean_object* v_res_904_; 
v_x_1015__boxed_902_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_x_1016__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_897_, v_x_1015__boxed_902_, v_x_1016__boxed_903_, v_x_900_, v_x_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
uint64_t v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v___x_911_; 
v___x_908_ = l_Lean_instHashableMVarId_hash(v_x_906_);
v___x_909_ = lean_uint64_to_usize(v___x_908_);
v___x_910_ = ((size_t)1ULL);
v___x_911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_905_, v___x_909_, v___x_910_, v_x_906_, v_x_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_912_, lean_object* v_val_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_mctx_917_; lean_object* v_cache_918_; lean_object* v_zetaDeltaFVarIds_919_; lean_object* v_postponed_920_; lean_object* v_diag_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_949_; 
v___x_916_ = lean_st_ref_take(v___y_914_);
v_mctx_917_ = lean_ctor_get(v___x_916_, 0);
v_cache_918_ = lean_ctor_get(v___x_916_, 1);
v_zetaDeltaFVarIds_919_ = lean_ctor_get(v___x_916_, 2);
v_postponed_920_ = lean_ctor_get(v___x_916_, 3);
v_diag_921_ = lean_ctor_get(v___x_916_, 4);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_949_ == 0)
{
v___x_923_ = v___x_916_;
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_diag_921_);
lean_inc(v_postponed_920_);
lean_inc(v_zetaDeltaFVarIds_919_);
lean_inc(v_cache_918_);
lean_inc(v_mctx_917_);
lean_dec(v___x_916_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_949_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_depth_925_; lean_object* v_levelAssignDepth_926_; lean_object* v_lmvarCounter_927_; lean_object* v_mvarCounter_928_; lean_object* v_lDecls_929_; lean_object* v_decls_930_; lean_object* v_userNames_931_; lean_object* v_lAssignment_932_; lean_object* v_eAssignment_933_; lean_object* v_dAssignment_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_948_; 
v_depth_925_ = lean_ctor_get(v_mctx_917_, 0);
v_levelAssignDepth_926_ = lean_ctor_get(v_mctx_917_, 1);
v_lmvarCounter_927_ = lean_ctor_get(v_mctx_917_, 2);
v_mvarCounter_928_ = lean_ctor_get(v_mctx_917_, 3);
v_lDecls_929_ = lean_ctor_get(v_mctx_917_, 4);
v_decls_930_ = lean_ctor_get(v_mctx_917_, 5);
v_userNames_931_ = lean_ctor_get(v_mctx_917_, 6);
v_lAssignment_932_ = lean_ctor_get(v_mctx_917_, 7);
v_eAssignment_933_ = lean_ctor_get(v_mctx_917_, 8);
v_dAssignment_934_ = lean_ctor_get(v_mctx_917_, 9);
v_isSharedCheck_948_ = !lean_is_exclusive(v_mctx_917_);
if (v_isSharedCheck_948_ == 0)
{
v___x_936_ = v_mctx_917_;
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_dAssignment_934_);
lean_inc(v_eAssignment_933_);
lean_inc(v_lAssignment_932_);
lean_inc(v_userNames_931_);
lean_inc(v_decls_930_);
lean_inc(v_lDecls_929_);
lean_inc(v_mvarCounter_928_);
lean_inc(v_lmvarCounter_927_);
lean_inc(v_levelAssignDepth_926_);
lean_inc(v_depth_925_);
lean_dec(v_mctx_917_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_933_, v_mvarId_912_, v_val_913_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 8, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_depth_925_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_levelAssignDepth_926_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_lmvarCounter_927_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_mvarCounter_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_lDecls_929_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_decls_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_userNames_931_);
lean_ctor_set(v_reuseFailAlloc_947_, 7, v_lAssignment_932_);
lean_ctor_set(v_reuseFailAlloc_947_, 8, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 9, v_dAssignment_934_);
v___x_940_ = v_reuseFailAlloc_947_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_940_);
v___x_942_ = v___x_923_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_cache_918_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_zetaDeltaFVarIds_919_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_postponed_920_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_diag_921_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_st_ref_set(v___y_914_, v___x_942_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_950_, lean_object* v_val_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_950_, v_val_951_, v___y_952_);
lean_dec(v___y_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_955_, lean_object* v___x_956_, uint8_t v_synthetic_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; 
lean_inc(v_mvarId_955_);
v___x_963_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_955_, v___x_956_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v___x_963_);
lean_inc(v_mvarId_955_);
v___x_964_ = l_Lean_MVarId_getType(v_mvarId_955_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref(v___x_964_);
v___x_966_ = 1;
v___x_967_ = l_Lean_Meta_mkLabeledSorry(v_a_965_, v_synthetic_957_, v___x_966_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref(v___x_967_);
v___x_969_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_955_, v_a_968_, v___y_959_);
return v___x_969_;
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v_mvarId_955_);
v_a_970_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_967_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_967_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_mvarId_955_);
v_a_978_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_964_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_964_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_dec(v_mvarId_955_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_986_, lean_object* v___x_987_, lean_object* v_synthetic_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
uint8_t v_synthetic_boxed_994_; lean_object* v_res_995_; 
v_synthetic_boxed_994_ = lean_unbox(v_synthetic_988_);
v_res_995_ = l_Lean_MVarId_admit___lam__0(v_mvarId_986_, v___x_987_, v_synthetic_boxed_994_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_999_, uint8_t v_synthetic_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; 
v___x_1006_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1007_ = lean_box(v_synthetic_1000_);
lean_inc(v_mvarId_999_);
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1008_, 0, v_mvarId_999_);
lean_closure_set(v___f_1008_, 1, v___x_1006_);
lean_closure_set(v___f_1008_, 2, v___x_1007_);
v___x_1009_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_999_, v___f_1008_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1010_, lean_object* v_synthetic_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
uint8_t v_synthetic_boxed_1017_; lean_object* v_res_1018_; 
v_synthetic_boxed_1017_ = lean_unbox(v_synthetic_1011_);
v_res_1018_ = l_Lean_MVarId_admit(v_mvarId_1010_, v_synthetic_boxed_1017_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1019_, lean_object* v_val_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1019_, v_val_1020_, v___y_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1027_, lean_object* v_val_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1027_, v_val_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1036_, v_x_1037_, v_x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1040_, lean_object* v_x_1041_, size_t v_x_1042_, size_t v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1041_, v_x_1042_, v_x_1043_, v_x_1044_, v_x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
size_t v_x_1340__boxed_1053_; size_t v_x_1341__boxed_1054_; lean_object* v_res_1055_; 
v_x_1340__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_x_1341__boxed_1054_ = lean_unbox_usize(v_x_1050_);
lean_dec(v_x_1050_);
v_res_1055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1047_, v_x_1048_, v_x_1340__boxed_1053_, v_x_1341__boxed_1054_, v_x_1051_, v_x_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1056_, lean_object* v_n_1057_, lean_object* v_k_1058_, lean_object* v_v_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1057_, v_k_1058_, v_v_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1061_, size_t v_depth_1062_, lean_object* v_keys_1063_, lean_object* v_vals_1064_, lean_object* v_heq_1065_, lean_object* v_i_1066_, lean_object* v_entries_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1062_, v_keys_1063_, v_vals_1064_, v_i_1066_, v_entries_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_depth_1070_, lean_object* v_keys_1071_, lean_object* v_vals_1072_, lean_object* v_heq_1073_, lean_object* v_i_1074_, lean_object* v_entries_1075_){
_start:
{
size_t v_depth_boxed_1076_; lean_object* v_res_1077_; 
v_depth_boxed_1076_ = lean_unbox_usize(v_depth_1070_);
lean_dec(v_depth_1070_);
v_res_1077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1069_, v_depth_boxed_1076_, v_keys_1071_, v_vals_1072_, v_heq_1073_, v_i_1074_, v_entries_1075_);
lean_dec_ref(v_vals_1072_);
lean_dec_ref(v_keys_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1079_, v_x_1080_, v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
lean_inc(v_mvarId_1084_);
v___x_1090_ = l_Lean_MVarId_getType(v_mvarId_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = l_Lean_Expr_headBeta(v_a_1091_);
v___x_1093_ = l_Lean_MVarId_setType___redArg(v_mvarId_1084_, v___x_1092_, v_a_1086_);
return v___x_1093_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_mvarId_1084_);
v_a_1094_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1090_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1090_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_MVarId_headBetaType(v_mvarId_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
uint8_t v___x_1111_; 
v___x_1111_ = 0;
return v___x_1111_;
}
else
{
lean_object* v_key_1112_; lean_object* v_tail_1113_; uint8_t v___x_1114_; 
v_key_1112_ = lean_ctor_get(v_x_1110_, 0);
v_tail_1113_ = lean_ctor_get(v_x_1110_, 2);
v___x_1114_ = l_Lean_instBEqFVarId_beq(v_key_1112_, v_a_1109_);
if (v___x_1114_ == 0)
{
v_x_1110_ = v_tail_1113_;
goto _start;
}
else
{
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1116_, v_x_1117_);
lean_dec(v_x_1117_);
lean_dec(v_a_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
return v_x_1121_;
}
else
{
lean_object* v_key_1122_; lean_object* v_value_1123_; lean_object* v_tail_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_key_1122_ = lean_ctor_get(v_x_1121_, 0);
v_value_1123_ = lean_ctor_get(v_x_1121_, 1);
v_tail_1124_ = lean_ctor_get(v_x_1121_, 2);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v_x_1121_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_tail_1124_);
lean_inc(v_value_1123_);
lean_inc(v_key_1122_);
lean_dec(v_x_1121_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_instBEqFVarId_beq(v_key_1122_, v_a_1120_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1120_, v_tail_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 2, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_key_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_value_1123_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
lean_del_object(v___x_1126_);
lean_dec(v_value_1123_);
lean_dec(v_key_1122_);
return v_tail_1124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1134_, lean_object* v_x_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1134_, v_x_1135_);
lean_dec(v_a_1134_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v_size_1139_; lean_object* v_buckets_1140_; lean_object* v___x_1141_; uint64_t v___x_1142_; uint64_t v___x_1143_; uint64_t v___x_1144_; uint64_t v_fold_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v___x_1148_; size_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v_bkt_1154_; uint8_t v___x_1155_; 
v_size_1139_ = lean_ctor_get(v_m_1137_, 0);
v_buckets_1140_ = lean_ctor_get(v_m_1137_, 1);
v___x_1141_ = lean_array_get_size(v_buckets_1140_);
v___x_1142_ = l_Lean_instHashableFVarId_hash(v_a_1138_);
v___x_1143_ = 32ULL;
v___x_1144_ = lean_uint64_shift_right(v___x_1142_, v___x_1143_);
v_fold_1145_ = lean_uint64_xor(v___x_1142_, v___x_1144_);
v___x_1146_ = 16ULL;
v___x_1147_ = lean_uint64_shift_right(v_fold_1145_, v___x_1146_);
v___x_1148_ = lean_uint64_xor(v_fold_1145_, v___x_1147_);
v___x_1149_ = lean_uint64_to_usize(v___x_1148_);
v___x_1150_ = lean_usize_of_nat(v___x_1141_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_sub(v___x_1150_, v___x_1151_);
v___x_1153_ = lean_usize_land(v___x_1149_, v___x_1152_);
v_bkt_1154_ = lean_array_uget_borrowed(v_buckets_1140_, v___x_1153_);
v___x_1155_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1138_, v_bkt_1154_);
if (v___x_1155_ == 0)
{
return v_m_1137_;
}
else
{
lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1168_; 
lean_inc(v_bkt_1154_);
lean_inc_ref(v_buckets_1140_);
lean_inc(v_size_1139_);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_m_1137_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; lean_object* v_unused_1170_; 
v_unused_1169_ = lean_ctor_get(v_m_1137_, 1);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_m_1137_, 0);
lean_dec(v_unused_1170_);
v___x_1157_ = v_m_1137_;
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
else
{
lean_dec(v_m_1137_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v_buckets_x27_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1159_ = lean_box(0);
v_buckets_x27_1160_ = lean_array_uset(v_buckets_1140_, v___x_1153_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_sub(v_size_1139_, v___x_1161_);
lean_dec(v_size_1139_);
v___x_1163_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1138_, v_bkt_1154_);
v___x_1164_ = lean_array_uset(v_buckets_x27_1160_, v___x_1153_, v___x_1163_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1164_);
lean_ctor_set(v___x_1157_, 0, v___x_1162_);
v___x_1166_ = v___x_1157_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1171_, v_a_1172_);
lean_dec(v_a_1172_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1181_ = lean_st_ref_take(v___y_1175_);
v___x_1182_ = l_Lean_Expr_fvarId_x21(v_e_1174_);
v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1181_, v___x_1182_);
lean_dec(v___x_1182_);
v___x_1184_ = lean_st_ref_set(v___y_1175_, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v_e_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_st_ref_get(v___y_1196_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
return v_res_1211_;
}
}
static size_t _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; 
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = ((size_t)8192ULL);
v___x_1214_ = lean_usize_sub(v___x_1213_, v___x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; lean_object* v_visited_1219_; size_t v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v___x_1218_ = lean_st_ref_get(v_a_1216_);
v_visited_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref(v_visited_1219_);
lean_dec(v___x_1218_);
v___x_1220_ = lean_ptr_addr(v_e_1215_);
v___x_1221_ = lean_usize_once(&l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0, &l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0);
v___x_1222_ = lean_usize_mod(v___x_1220_, v___x_1221_);
v___x_1223_ = lean_array_uget(v_visited_1219_, v___x_1222_);
lean_dec_ref(v_visited_1219_);
v___x_1224_ = lean_ptr_addr(v___x_1223_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_usize_dec_eq(v___x_1224_, v___x_1220_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_visited_1227_; lean_object* v_checked_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1239_; 
v___x_1226_ = lean_st_ref_take(v_a_1216_);
v_visited_1227_ = lean_ctor_get(v___x_1226_, 0);
v_checked_1228_ = lean_ctor_get(v___x_1226_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1230_ = v___x_1226_;
v_isShared_1231_ = v_isSharedCheck_1239_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_checked_1228_);
lean_inc(v_visited_1227_);
lean_dec(v___x_1226_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1239_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_array_uset(v_visited_1227_, v___x_1222_, v_e_1215_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_checked_1228_);
v___x_1234_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_st_ref_set(v_a_1216_, v___x_1234_);
v___x_1236_ = lean_box(v___x_1225_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_e_1215_);
v___x_1240_ = lean_box(v___x_1225_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1242_, v_a_1243_);
lean_dec(v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1246_, lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
return v___x_1248_;
}
else
{
lean_object* v_key_1249_; lean_object* v_tail_1250_; uint8_t v___x_1251_; 
v_key_1249_ = lean_ctor_get(v_x_1247_, 0);
v_tail_1250_ = lean_ctor_get(v_x_1247_, 2);
v___x_1251_ = lean_expr_eqv(v_key_1249_, v_a_1246_);
if (v___x_1251_ == 0)
{
v_x_1247_ = v_tail_1250_;
goto _start;
}
else
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_a_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
return v_x_1257_;
}
else
{
lean_object* v_key_1259_; lean_object* v_value_1260_; lean_object* v_tail_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1284_; 
v_key_1259_ = lean_ctor_get(v_x_1258_, 0);
v_value_1260_ = lean_ctor_get(v_x_1258_, 1);
v_tail_1261_ = lean_ctor_get(v_x_1258_, 2);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1263_ = v_x_1258_;
v_isShared_1264_ = v_isSharedCheck_1284_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_tail_1261_);
lean_inc(v_value_1260_);
lean_inc(v_key_1259_);
lean_dec(v_x_1258_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1284_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v_fold_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1265_ = lean_array_get_size(v_x_1257_);
v___x_1266_ = l_Lean_Expr_hash(v_key_1259_);
v___x_1267_ = 32ULL;
v___x_1268_ = lean_uint64_shift_right(v___x_1266_, v___x_1267_);
v_fold_1269_ = lean_uint64_xor(v___x_1266_, v___x_1268_);
v___x_1270_ = 16ULL;
v___x_1271_ = lean_uint64_shift_right(v_fold_1269_, v___x_1270_);
v___x_1272_ = lean_uint64_xor(v_fold_1269_, v___x_1271_);
v___x_1273_ = lean_uint64_to_usize(v___x_1272_);
v___x_1274_ = lean_usize_of_nat(v___x_1265_);
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_sub(v___x_1274_, v___x_1275_);
v___x_1277_ = lean_usize_land(v___x_1273_, v___x_1276_);
v___x_1278_ = lean_array_uget_borrowed(v_x_1257_, v___x_1277_);
lean_inc(v___x_1278_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 2, v___x_1278_);
v___x_1280_ = v___x_1263_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_key_1259_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_value_1260_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; 
v___x_1281_ = lean_array_uset(v_x_1257_, v___x_1277_, v___x_1280_);
v_x_1257_ = v___x_1281_;
v_x_1258_ = v_tail_1261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1285_, lean_object* v_source_1286_, lean_object* v_target_1287_){
_start:
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = lean_array_get_size(v_source_1286_);
v___x_1289_ = lean_nat_dec_lt(v_i_1285_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v_source_1286_);
lean_dec(v_i_1285_);
return v_target_1287_;
}
else
{
lean_object* v_es_1290_; lean_object* v___x_1291_; lean_object* v_source_1292_; lean_object* v_target_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_es_1290_ = lean_array_fget(v_source_1286_, v_i_1285_);
v___x_1291_ = lean_box(0);
v_source_1292_ = lean_array_fset(v_source_1286_, v_i_1285_, v___x_1291_);
v_target_1293_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1287_, v_es_1290_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_add(v_i_1285_, v___x_1294_);
lean_dec(v_i_1285_);
v_i_1285_ = v___x_1295_;
v_source_1286_ = v_source_1292_;
v_target_1287_ = v_target_1293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_nbuckets_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1298_ = lean_array_get_size(v_data_1297_);
v___x_1299_ = lean_unsigned_to_nat(2u);
v_nbuckets_1300_ = lean_nat_mul(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_mk_array(v_nbuckets_1300_, v___x_1302_);
v___x_1304_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1301_, v_data_1297_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1305_, lean_object* v_a_1306_, lean_object* v_b_1307_){
_start:
{
lean_object* v_size_1308_; lean_object* v_buckets_1309_; lean_object* v___x_1310_; uint64_t v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v_fold_1314_; uint64_t v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v_bkt_1323_; uint8_t v___x_1324_; 
v_size_1308_ = lean_ctor_get(v_m_1305_, 0);
v_buckets_1309_ = lean_ctor_get(v_m_1305_, 1);
v___x_1310_ = lean_array_get_size(v_buckets_1309_);
v___x_1311_ = l_Lean_Expr_hash(v_a_1306_);
v___x_1312_ = 32ULL;
v___x_1313_ = lean_uint64_shift_right(v___x_1311_, v___x_1312_);
v_fold_1314_ = lean_uint64_xor(v___x_1311_, v___x_1313_);
v___x_1315_ = 16ULL;
v___x_1316_ = lean_uint64_shift_right(v_fold_1314_, v___x_1315_);
v___x_1317_ = lean_uint64_xor(v_fold_1314_, v___x_1316_);
v___x_1318_ = lean_uint64_to_usize(v___x_1317_);
v___x_1319_ = lean_usize_of_nat(v___x_1310_);
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_sub(v___x_1319_, v___x_1320_);
v___x_1322_ = lean_usize_land(v___x_1318_, v___x_1321_);
v_bkt_1323_ = lean_array_uget_borrowed(v_buckets_1309_, v___x_1322_);
v___x_1324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1306_, v_bkt_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1345_; 
lean_inc_ref(v_buckets_1309_);
lean_inc(v_size_1308_);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_m_1305_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; lean_object* v_unused_1347_; 
v_unused_1346_ = lean_ctor_get(v_m_1305_, 1);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_m_1305_, 0);
lean_dec(v_unused_1347_);
v___x_1326_ = v_m_1305_;
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_m_1305_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1345_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v_size_x27_1329_; lean_object* v___x_1330_; lean_object* v_buckets_x27_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1328_ = lean_unsigned_to_nat(1u);
v_size_x27_1329_ = lean_nat_add(v_size_1308_, v___x_1328_);
lean_dec(v_size_1308_);
lean_inc(v_bkt_1323_);
v___x_1330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1306_);
lean_ctor_set(v___x_1330_, 1, v_b_1307_);
lean_ctor_set(v___x_1330_, 2, v_bkt_1323_);
v_buckets_x27_1331_ = lean_array_uset(v_buckets_1309_, v___x_1322_, v___x_1330_);
v___x_1332_ = lean_unsigned_to_nat(4u);
v___x_1333_ = lean_nat_mul(v_size_x27_1329_, v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(3u);
v___x_1335_ = lean_nat_div(v___x_1333_, v___x_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_array_get_size(v_buckets_x27_1331_);
v___x_1337_ = lean_nat_dec_le(v___x_1335_, v___x_1336_);
lean_dec(v___x_1335_);
if (v___x_1337_ == 0)
{
lean_object* v_val_1338_; lean_object* v___x_1340_; 
v_val_1338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1331_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_val_1338_);
lean_ctor_set(v___x_1326_, 0, v_size_x27_1329_);
v___x_1340_ = v___x_1326_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_size_x27_1329_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_val_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v___x_1343_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_buckets_x27_1331_);
lean_ctor_set(v___x_1326_, 0, v_size_x27_1329_);
v___x_1343_ = v___x_1326_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_size_x27_1329_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_buckets_x27_1331_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_dec(v_b_1307_);
lean_dec_ref(v_a_1306_);
return v_m_1305_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_buckets_1350_; lean_object* v___x_1351_; uint64_t v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v_fold_1355_; uint64_t v___x_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_buckets_1350_ = lean_ctor_get(v_m_1348_, 1);
v___x_1351_ = lean_array_get_size(v_buckets_1350_);
v___x_1352_ = l_Lean_Expr_hash(v_a_1349_);
v___x_1353_ = 32ULL;
v___x_1354_ = lean_uint64_shift_right(v___x_1352_, v___x_1353_);
v_fold_1355_ = lean_uint64_xor(v___x_1352_, v___x_1354_);
v___x_1356_ = 16ULL;
v___x_1357_ = lean_uint64_shift_right(v_fold_1355_, v___x_1356_);
v___x_1358_ = lean_uint64_xor(v_fold_1355_, v___x_1357_);
v___x_1359_ = lean_uint64_to_usize(v___x_1358_);
v___x_1360_ = lean_usize_of_nat(v___x_1351_);
v___x_1361_ = ((size_t)1ULL);
v___x_1362_ = lean_usize_sub(v___x_1360_, v___x_1361_);
v___x_1363_ = lean_usize_land(v___x_1359_, v___x_1362_);
v___x_1364_ = lean_array_uget_borrowed(v_buckets_1350_, v___x_1363_);
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1349_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1366_, lean_object* v_a_1367_){
_start:
{
uint8_t v_res_1368_; lean_object* v_r_1369_; 
v_res_1368_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1366_, v_a_1367_);
lean_dec_ref(v_a_1367_);
lean_dec_ref(v_m_1366_);
v_r_1369_ = lean_box(v_res_1368_);
return v_r_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1373_; lean_object* v_checked_1374_; uint8_t v___x_1375_; 
v___x_1373_ = lean_st_ref_get(v_a_1371_);
v_checked_1374_ = lean_ctor_get(v___x_1373_, 1);
lean_inc_ref(v_checked_1374_);
lean_dec(v___x_1373_);
v___x_1375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1374_, v_e_1370_);
lean_dec_ref(v_checked_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; lean_object* v_visited_1377_; lean_object* v_checked_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1390_; 
v___x_1376_ = lean_st_ref_take(v_a_1371_);
v_visited_1377_ = lean_ctor_get(v___x_1376_, 0);
v_checked_1378_ = lean_ctor_get(v___x_1376_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1380_ = v___x_1376_;
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_checked_1378_);
lean_inc(v_visited_1377_);
lean_dec(v___x_1376_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1378_, v_e_1370_, v___x_1382_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_visited_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_st_ref_set(v_a_1371_, v___x_1385_);
v___x_1387_ = lean_box(v___x_1375_);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v_e_1370_);
v___x_1391_ = lean_box(v___x_1375_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1393_, lean_object* v_a_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1393_, v_a_1394_);
lean_dec(v_a_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1397_, lean_object* v_f_1398_, uint8_t v_stopWhenVisited_1399_, lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v_d_1414_; lean_object* v_b_1415_; lean_object* v___y_1416_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___x_1446_; 
lean_inc_ref(v_e_1400_);
v___x_1446_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1479_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1479_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1479_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_unbox(v_a_1447_);
lean_dec(v_a_1447_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
lean_del_object(v___x_1449_);
lean_inc_ref(v_p_1397_);
lean_inc_ref(v_e_1400_);
v___x_1452_ = lean_apply_1(v_p_1397_, v_e_1400_);
v___x_1453_ = lean_unbox(v___x_1452_);
if (v___x_1453_ == 0)
{
v___y_1420_ = v_a_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1454_; 
lean_inc_ref(v_e_1400_);
v___x_1454_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; uint8_t v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = lean_unbox(v_a_1455_);
lean_dec(v_a_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
lean_inc_ref(v_f_1398_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc_ref(v___y_1403_);
lean_inc(v___y_1402_);
lean_inc_ref(v_e_1400_);
v___x_1457_ = lean_apply_7(v_f_1398_, v_e_1400_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, lean_box(0));
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1457_, 0);
lean_dec(v_unused_1466_);
v___x_1459_ = v___x_1457_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1457_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
if (v_stopWhenVisited_1399_ == 0)
{
lean_del_object(v___x_1459_);
v___y_1420_ = v_a_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
v___x_1461_ = lean_box(0);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
return v___x_1457_;
}
}
else
{
v___y_1420_ = v_a_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
goto v___jp_1419_;
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
v_a_1467_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1454_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1454_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
v___x_1475_ = lean_box(0);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1475_);
v___x_1477_ = v___x_1449_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
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
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
v_a_1480_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1446_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1446_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
v___jp_1408_:
{
lean_object* v___x_1417_; 
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1417_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_d_1414_, v___y_1416_, v___y_1409_, v___y_1412_, v___y_1411_, v___y_1410_, v___y_1413_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref(v___x_1417_);
v_e_1400_ = v_b_1415_;
v_a_1401_ = v___y_1416_;
v___y_1402_ = v___y_1409_;
v___y_1403_ = v___y_1412_;
v___y_1404_ = v___y_1411_;
v___y_1405_ = v___y_1410_;
v___y_1406_ = v___y_1413_;
goto _start;
}
else
{
lean_dec_ref(v_b_1415_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
return v___x_1417_;
}
}
v___jp_1419_:
{
switch(lean_obj_tag(v_e_1400_))
{
case 7:
{
lean_object* v_binderType_1426_; lean_object* v_body_1427_; 
v_binderType_1426_ = lean_ctor_get(v_e_1400_, 1);
lean_inc_ref(v_binderType_1426_);
v_body_1427_ = lean_ctor_get(v_e_1400_, 2);
lean_inc_ref(v_body_1427_);
lean_dec_ref(v_e_1400_);
v___y_1409_ = v___y_1421_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1423_;
v___y_1412_ = v___y_1422_;
v___y_1413_ = v___y_1425_;
v_d_1414_ = v_binderType_1426_;
v_b_1415_ = v_body_1427_;
v___y_1416_ = v___y_1420_;
goto v___jp_1408_;
}
case 6:
{
lean_object* v_binderType_1428_; lean_object* v_body_1429_; 
v_binderType_1428_ = lean_ctor_get(v_e_1400_, 1);
lean_inc_ref(v_binderType_1428_);
v_body_1429_ = lean_ctor_get(v_e_1400_, 2);
lean_inc_ref(v_body_1429_);
lean_dec_ref(v_e_1400_);
v___y_1409_ = v___y_1421_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1423_;
v___y_1412_ = v___y_1422_;
v___y_1413_ = v___y_1425_;
v_d_1414_ = v_binderType_1428_;
v_b_1415_ = v_body_1429_;
v___y_1416_ = v___y_1420_;
goto v___jp_1408_;
}
case 8:
{
lean_object* v_type_1430_; lean_object* v_value_1431_; lean_object* v_body_1432_; lean_object* v___x_1433_; 
v_type_1430_ = lean_ctor_get(v_e_1400_, 1);
lean_inc_ref(v_type_1430_);
v_value_1431_ = lean_ctor_get(v_e_1400_, 2);
lean_inc_ref(v_value_1431_);
v_body_1432_ = lean_ctor_get(v_e_1400_, 3);
lean_inc_ref(v_body_1432_);
lean_dec_ref(v_e_1400_);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1433_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_type_1430_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref(v___x_1433_);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_value_1431_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref(v___x_1434_);
v_e_1400_ = v_body_1432_;
v_a_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
goto _start;
}
else
{
lean_dec_ref(v_body_1432_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
return v___x_1434_;
}
}
else
{
lean_dec_ref(v_body_1432_);
lean_dec_ref(v_value_1431_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
return v___x_1433_;
}
}
case 5:
{
lean_object* v_fn_1436_; lean_object* v_arg_1437_; lean_object* v___x_1438_; 
v_fn_1436_ = lean_ctor_get(v_e_1400_, 0);
lean_inc_ref(v_fn_1436_);
v_arg_1437_ = lean_ctor_get(v_e_1400_, 1);
lean_inc_ref(v_arg_1437_);
lean_dec_ref(v_e_1400_);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1438_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_fn_1436_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref(v___x_1438_);
v_e_1400_ = v_arg_1437_;
v_a_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1437_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
return v___x_1438_;
}
}
case 10:
{
lean_object* v_expr_1440_; 
v_expr_1440_ = lean_ctor_get(v_e_1400_, 1);
lean_inc_ref(v_expr_1440_);
lean_dec_ref(v_e_1400_);
v_e_1400_ = v_expr_1440_;
v_a_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
goto _start;
}
case 11:
{
lean_object* v_struct_1442_; 
v_struct_1442_ = lean_ctor_get(v_e_1400_, 2);
lean_inc_ref(v_struct_1442_);
lean_dec_ref(v_e_1400_);
v_e_1400_ = v_struct_1442_;
v_a_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
goto _start;
}
default: 
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v_e_1400_);
lean_dec_ref(v_f_1398_);
lean_dec_ref(v_p_1397_);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1488_, lean_object* v_f_1489_, lean_object* v_stopWhenVisited_1490_, lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1499_; lean_object* v_res_1500_; 
v_stopWhenVisited_boxed_1499_ = lean_unbox(v_stopWhenVisited_1490_);
v_res_1500_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1488_, v_f_1489_, v_stopWhenVisited_boxed_1499_, v_e_1491_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v_a_1492_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1501_, lean_object* v_f_1502_, lean_object* v_e_1503_, uint8_t v_stopWhenVisited_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = l_Lean_ForEachExprWhere_initCache;
v___x_1512_ = lean_st_mk_ref(v___x_1511_);
v___x_1513_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1501_, v_f_1502_, v_stopWhenVisited_1504_, v_e_1503_, v___x_1512_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1522_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1522_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_st_ref_get(v___x_1512_);
lean_dec(v___x_1512_);
lean_dec(v___x_1518_);
if (v_isShared_1517_ == 0)
{
v___x_1520_ = v___x_1516_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1514_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_dec(v___x_1512_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1523_, lean_object* v_f_1524_, lean_object* v_e_1525_, lean_object* v_stopWhenVisited_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1533_; lean_object* v_res_1534_; 
v_stopWhenVisited_boxed_1533_ = lean_unbox(v_stopWhenVisited_1526_);
v_res_1534_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1523_, v_f_1524_, v_e_1525_, v_stopWhenVisited_boxed_1533_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1536_, lean_object* v___f_1537_, uint8_t v___x_1538_, lean_object* v_e_1539_, lean_object* v_candidates_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1539_, v___y_1542_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___y_1550_; uint8_t v___x_1560_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_st_mk_ref(v_candidates_1540_);
v___x_1560_ = l_Lean_Expr_hasFVar(v_a_1547_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_a_1547_);
lean_dec_ref(v___f_1537_);
v___x_1561_ = lean_box(0);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___x_1548_);
v___x_1562_ = lean_apply_7(v___f_1536_, v___x_1561_, v___x_1548_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___y_1550_ = v___x_1562_;
goto v___jp_1549_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1564_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1563_, v___f_1537_, v_a_1547_, v___x_1538_, v___x_1548_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___x_1548_);
v___x_1566_ = lean_apply_7(v___f_1536_, v_a_1565_, v___x_1548_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___y_1550_ = v___x_1566_;
goto v___jp_1549_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v___x_1548_);
lean_dec_ref(v___f_1536_);
v_a_1567_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1564_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1564_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
v___jp_1549_:
{
if (lean_obj_tag(v___y_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
v_a_1551_ = lean_ctor_get(v___y_1550_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___y_1550_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1553_ = v___y_1550_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___y_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = lean_st_ref_get(v___x_1548_);
lean_dec(v___x_1548_);
lean_dec(v___x_1555_);
if (v_isShared_1554_ == 0)
{
v___x_1557_ = v___x_1553_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1551_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_dec(v___x_1548_);
return v___y_1550_;
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_candidates_1540_);
lean_dec_ref(v___f_1537_);
lean_dec_ref(v___f_1536_);
v_a_1575_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1546_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1546_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1583_, lean_object* v___f_1584_, lean_object* v___x_1585_, lean_object* v_e_1586_, lean_object* v_candidates_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___x_17596__boxed_1593_; lean_object* v_res_1594_; 
v___x_17596__boxed_1593_ = lean_unbox(v___x_1585_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1583_, v___f_1584_, v___x_17596__boxed_1593_, v_e_1586_, v_candidates_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_e_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1602_ = lean_st_ref_take(v___y_1596_);
v___x_1603_ = l_Lean_Expr_fvarId_x21(v_e_1595_);
v___x_1604_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1602_, v___x_1603_);
lean_dec(v___x_1603_);
v___x_1605_ = lean_st_ref_set(v___y_1596_, v___x_1604_);
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_e_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v_e_1608_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_____r_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_st_ref_get(v___y_1617_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_____r_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 0)
{
return v_x_1633_;
}
else
{
lean_object* v_key_1635_; lean_object* v_value_1636_; lean_object* v_tail_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1660_; 
v_key_1635_ = lean_ctor_get(v_x_1634_, 0);
v_value_1636_ = lean_ctor_get(v_x_1634_, 1);
v_tail_1637_ = lean_ctor_get(v_x_1634_, 2);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1634_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1639_ = v_x_1634_;
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_tail_1637_);
lean_inc(v_value_1636_);
lean_inc(v_key_1635_);
lean_dec(v_x_1634_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v_fold_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1641_ = lean_array_get_size(v_x_1633_);
v___x_1642_ = l_Lean_instHashableFVarId_hash(v_key_1635_);
v___x_1643_ = 32ULL;
v___x_1644_ = lean_uint64_shift_right(v___x_1642_, v___x_1643_);
v_fold_1645_ = lean_uint64_xor(v___x_1642_, v___x_1644_);
v___x_1646_ = 16ULL;
v___x_1647_ = lean_uint64_shift_right(v_fold_1645_, v___x_1646_);
v___x_1648_ = lean_uint64_xor(v_fold_1645_, v___x_1647_);
v___x_1649_ = lean_uint64_to_usize(v___x_1648_);
v___x_1650_ = lean_usize_of_nat(v___x_1641_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_sub(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_usize_land(v___x_1649_, v___x_1652_);
v___x_1654_ = lean_array_uget_borrowed(v_x_1633_, v___x_1653_);
lean_inc(v___x_1654_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 2, v___x_1654_);
v___x_1656_ = v___x_1639_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_key_1635_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_value_1636_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_array_uset(v_x_1633_, v___x_1653_, v___x_1656_);
v_x_1633_ = v___x_1657_;
v_x_1634_ = v_tail_1637_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1661_, lean_object* v_source_1662_, lean_object* v_target_1663_){
_start:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = lean_array_get_size(v_source_1662_);
v___x_1665_ = lean_nat_dec_lt(v_i_1661_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v_source_1662_);
lean_dec(v_i_1661_);
return v_target_1663_;
}
else
{
lean_object* v_es_1666_; lean_object* v___x_1667_; lean_object* v_source_1668_; lean_object* v_target_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_es_1666_ = lean_array_fget(v_source_1662_, v_i_1661_);
v___x_1667_ = lean_box(0);
v_source_1668_ = lean_array_fset(v_source_1662_, v_i_1661_, v___x_1667_);
v_target_1669_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1663_, v_es_1666_);
v___x_1670_ = lean_unsigned_to_nat(1u);
v___x_1671_ = lean_nat_add(v_i_1661_, v___x_1670_);
lean_dec(v_i_1661_);
v_i_1661_ = v___x_1671_;
v_source_1662_ = v_source_1668_;
v_target_1663_ = v_target_1669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1673_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_nbuckets_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1674_ = lean_array_get_size(v_data_1673_);
v___x_1675_ = lean_unsigned_to_nat(2u);
v_nbuckets_1676_ = lean_nat_mul(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_mk_array(v_nbuckets_1676_, v___x_1678_);
v___x_1680_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1677_, v_data_1673_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1681_, lean_object* v_a_1682_, lean_object* v_b_1683_){
_start:
{
lean_object* v_size_1684_; lean_object* v_buckets_1685_; lean_object* v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v_fold_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v_bkt_1699_; uint8_t v___x_1700_; 
v_size_1684_ = lean_ctor_get(v_m_1681_, 0);
v_buckets_1685_ = lean_ctor_get(v_m_1681_, 1);
v___x_1686_ = lean_array_get_size(v_buckets_1685_);
v___x_1687_ = l_Lean_instHashableFVarId_hash(v_a_1682_);
v___x_1688_ = 32ULL;
v___x_1689_ = lean_uint64_shift_right(v___x_1687_, v___x_1688_);
v_fold_1690_ = lean_uint64_xor(v___x_1687_, v___x_1689_);
v___x_1691_ = 16ULL;
v___x_1692_ = lean_uint64_shift_right(v_fold_1690_, v___x_1691_);
v___x_1693_ = lean_uint64_xor(v_fold_1690_, v___x_1692_);
v___x_1694_ = lean_uint64_to_usize(v___x_1693_);
v___x_1695_ = lean_usize_of_nat(v___x_1686_);
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_sub(v___x_1695_, v___x_1696_);
v___x_1698_ = lean_usize_land(v___x_1694_, v___x_1697_);
v_bkt_1699_ = lean_array_uget_borrowed(v_buckets_1685_, v___x_1698_);
v___x_1700_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1682_, v_bkt_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1721_; 
lean_inc_ref(v_buckets_1685_);
lean_inc(v_size_1684_);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_m_1681_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; lean_object* v_unused_1723_; 
v_unused_1722_ = lean_ctor_get(v_m_1681_, 1);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_m_1681_, 0);
lean_dec(v_unused_1723_);
v___x_1702_ = v_m_1681_;
v_isShared_1703_ = v_isSharedCheck_1721_;
goto v_resetjp_1701_;
}
else
{
lean_dec(v_m_1681_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1721_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v_size_x27_1705_; lean_object* v___x_1706_; lean_object* v_buckets_x27_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1704_ = lean_unsigned_to_nat(1u);
v_size_x27_1705_ = lean_nat_add(v_size_1684_, v___x_1704_);
lean_dec(v_size_1684_);
lean_inc(v_bkt_1699_);
v___x_1706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1682_);
lean_ctor_set(v___x_1706_, 1, v_b_1683_);
lean_ctor_set(v___x_1706_, 2, v_bkt_1699_);
v_buckets_x27_1707_ = lean_array_uset(v_buckets_1685_, v___x_1698_, v___x_1706_);
v___x_1708_ = lean_unsigned_to_nat(4u);
v___x_1709_ = lean_nat_mul(v_size_x27_1705_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = lean_nat_div(v___x_1709_, v___x_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_array_get_size(v_buckets_x27_1707_);
v___x_1713_ = lean_nat_dec_le(v___x_1711_, v___x_1712_);
lean_dec(v___x_1711_);
if (v___x_1713_ == 0)
{
lean_object* v_val_1714_; lean_object* v___x_1716_; 
v_val_1714_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1707_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_val_1714_);
lean_ctor_set(v___x_1702_, 0, v_size_x27_1705_);
v___x_1716_ = v___x_1702_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_size_x27_1705_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_val_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
lean_object* v___x_1719_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v_buckets_x27_1707_);
lean_ctor_set(v___x_1702_, 0, v_size_x27_1705_);
v___x_1719_ = v___x_1702_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_size_x27_1705_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_buckets_x27_1707_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_dec(v_b_1683_);
lean_dec(v_a_1682_);
return v_m_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1726_, size_t v_sz_1727_, size_t v_i_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_lt(v_i_1728_, v_sz_1727_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_b_1729_);
return v___x_1736_;
}
else
{
lean_object* v_snd_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1801_; 
v_snd_1737_ = lean_ctor_get(v_b_1729_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_b_1729_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_b_1729_, 0);
lean_dec(v_unused_1802_);
v___x_1739_ = v_b_1729_;
v_isShared_1740_ = v_isSharedCheck_1801_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snd_1737_);
lean_dec(v_b_1729_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1801_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v_a_1743_; lean_object* v_a_1750_; 
v___x_1741_ = lean_box(0);
v_a_1750_ = lean_array_uget_borrowed(v_as_1726_, v_i_1728_);
if (lean_obj_tag(v_a_1750_) == 0)
{
v_a_1743_ = v_snd_1737_;
goto v___jp_1742_;
}
else
{
lean_object* v_val_1751_; lean_object* v___y_1753_; uint8_t v___x_1757_; 
v_val_1751_ = lean_ctor_get(v_a_1750_, 0);
v___x_1757_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1751_);
if (v___x_1757_ == 0)
{
lean_object* v___f_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v_candidates_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___x_1779_; 
v___f_1758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1760_ = l_Lean_LocalDecl_type(v_val_1751_);
lean_inc_ref(v___x_1760_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1759_, v___f_1758_, v___x_1757_, v___x_1760_, v_snd_1737_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = l_Lean_LocalDecl_value_x3f(v_val_1751_, v___x_1757_);
if (lean_obj_tag(v___x_1781_) == 0)
{
v_candidates_1762_ = v_a_1780_;
v___y_1763_ = v___y_1730_;
v___y_1764_ = v___y_1731_;
v___y_1765_ = v___y_1732_;
v___y_1766_ = v___y_1733_;
goto v___jp_1761_;
}
else
{
lean_object* v_val_1782_; lean_object* v___x_1783_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1759_, v___f_1758_, v___x_1757_, v_val_1782_, v_a_1780_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v_candidates_1762_ = v_a_1784_;
v___y_1763_ = v___y_1730_;
v___y_1764_ = v___y_1731_;
v___y_1765_ = v___y_1732_;
v___y_1766_ = v___y_1733_;
goto v___jp_1761_;
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___x_1760_);
lean_del_object(v___x_1739_);
v_a_1785_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1783_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___x_1760_);
lean_del_object(v___x_1739_);
v_a_1793_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1779_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1779_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
v___jp_1761_:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Meta_isProp(v___x_1760_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; uint8_t v___x_1769_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_unbox(v_a_1768_);
lean_dec(v_a_1768_);
if (v___x_1769_ == 0)
{
v_a_1743_ = v_candidates_1762_;
goto v___jp_1742_;
}
else
{
uint8_t v___x_1770_; 
v___x_1770_ = l_Lean_LocalDecl_hasValue(v_val_1751_, v___x_1757_);
if (v___x_1770_ == 0)
{
v___y_1753_ = v_candidates_1762_;
goto v___jp_1752_;
}
else
{
if (v___x_1757_ == 0)
{
v_a_1743_ = v_candidates_1762_;
goto v___jp_1742_;
}
else
{
v___y_1753_ = v_candidates_1762_;
goto v___jp_1752_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_candidates_1762_);
lean_del_object(v___x_1739_);
v_a_1771_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1767_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1767_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
else
{
v_a_1743_ = v_snd_1737_;
goto v___jp_1742_;
}
v___jp_1752_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_LocalDecl_fvarId(v_val_1751_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1753_, v___x_1754_, v___x_1755_);
v_a_1743_ = v___x_1756_;
goto v___jp_1742_;
}
}
v___jp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v_a_1743_);
lean_ctor_set(v___x_1739_, 0, v___x_1741_);
v___x_1745_ = v___x_1739_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_a_1743_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
size_t v___x_1746_; size_t v___x_1747_; 
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1728_, v___x_1746_);
v_i_1728_ = v___x_1747_;
v_b_1729_ = v___x_1745_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1803_, lean_object* v_sz_1804_, lean_object* v_i_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
size_t v_sz_boxed_1812_; size_t v_i_boxed_1813_; lean_object* v_res_1814_; 
v_sz_boxed_1812_ = lean_unbox_usize(v_sz_1804_);
lean_dec(v_sz_1804_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1805_);
lean_dec(v_i_1805_);
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1803_, v_sz_boxed_1812_, v_i_boxed_1813_, v_b_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_as_1803_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1815_, size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_lt(v_i_1817_, v_sz_1816_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1818_);
return v___x_1825_;
}
else
{
lean_object* v_snd_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1890_; 
v_snd_1826_ = lean_ctor_get(v_b_1818_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_b_1818_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v_b_1818_, 0);
lean_dec(v_unused_1891_);
v___x_1828_ = v_b_1818_;
v_isShared_1829_ = v_isSharedCheck_1890_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snd_1826_);
lean_dec(v_b_1818_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1890_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v_a_1832_; lean_object* v_a_1839_; 
v___x_1830_ = lean_box(0);
v_a_1839_ = lean_array_uget_borrowed(v_as_1815_, v_i_1817_);
if (lean_obj_tag(v_a_1839_) == 0)
{
v_a_1832_ = v_snd_1826_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1840_; lean_object* v___y_1842_; uint8_t v___x_1846_; 
v_val_1840_ = lean_ctor_get(v_a_1839_, 0);
v___x_1846_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1840_);
if (v___x_1846_ == 0)
{
lean_object* v___f_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; lean_object* v_candidates_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___x_1868_; 
v___f_1847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1849_ = l_Lean_LocalDecl_type(v_val_1840_);
lean_inc_ref(v___x_1849_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1848_, v___f_1847_, v___x_1846_, v___x_1849_, v_snd_1826_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
v___x_1870_ = l_Lean_LocalDecl_value_x3f(v_val_1840_, v___x_1846_);
if (lean_obj_tag(v___x_1870_) == 0)
{
v_candidates_1851_ = v_a_1869_;
v___y_1852_ = v___y_1819_;
v___y_1853_ = v___y_1820_;
v___y_1854_ = v___y_1821_;
v___y_1855_ = v___y_1822_;
goto v___jp_1850_;
}
else
{
lean_object* v_val_1871_; lean_object* v___x_1872_; 
v_val_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_val_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1848_, v___f_1847_, v___x_1846_, v_val_1871_, v_a_1869_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v_candidates_1851_ = v_a_1873_;
v___y_1852_ = v___y_1819_;
v___y_1853_ = v___y_1820_;
v___y_1854_ = v___y_1821_;
v___y_1855_ = v___y_1822_;
goto v___jp_1850_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v___x_1849_);
lean_del_object(v___x_1828_);
v_a_1874_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1872_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1872_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___x_1849_);
lean_del_object(v___x_1828_);
v_a_1882_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1868_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1868_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
v___jp_1850_:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Meta_isProp(v___x_1849_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; uint8_t v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = lean_unbox(v_a_1857_);
lean_dec(v_a_1857_);
if (v___x_1858_ == 0)
{
v_a_1832_ = v_candidates_1851_;
goto v___jp_1831_;
}
else
{
uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_LocalDecl_hasValue(v_val_1840_, v___x_1846_);
if (v___x_1859_ == 0)
{
v___y_1842_ = v_candidates_1851_;
goto v___jp_1841_;
}
else
{
if (v___x_1846_ == 0)
{
v_a_1832_ = v_candidates_1851_;
goto v___jp_1831_;
}
else
{
v___y_1842_ = v_candidates_1851_;
goto v___jp_1841_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_candidates_1851_);
lean_del_object(v___x_1828_);
v_a_1860_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1856_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1856_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
v_a_1832_ = v_snd_1826_;
goto v___jp_1831_;
}
v___jp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = l_Lean_LocalDecl_fvarId(v_val_1840_);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1842_, v___x_1843_, v___x_1844_);
v_a_1832_ = v___x_1845_;
goto v___jp_1831_;
}
}
v___jp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_a_1832_);
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1834_ = v___x_1828_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_a_1832_);
v___x_1834_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_i_1817_, v___x_1835_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1815_, v_sz_1816_, v___x_1836_, v___x_1834_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1892_, lean_object* v_sz_1893_, lean_object* v_i_1894_, lean_object* v_b_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
size_t v_sz_boxed_1901_; size_t v_i_boxed_1902_; lean_object* v_res_1903_; 
v_sz_boxed_1901_ = lean_unbox_usize(v_sz_1893_);
lean_dec(v_sz_1893_);
v_i_boxed_1902_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1892_, v_sz_boxed_1901_, v_i_boxed_1902_, v_b_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec_ref(v_as_1892_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1904_, size_t v_sz_1905_, size_t v_i_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_b_1907_);
return v___x_1914_;
}
else
{
lean_object* v_snd_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1979_; 
v_snd_1915_ = lean_ctor_get(v_b_1907_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_b_1907_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v_b_1907_, 0);
lean_dec(v_unused_1980_);
v___x_1917_ = v_b_1907_;
v_isShared_1918_ = v_isSharedCheck_1979_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_snd_1915_);
lean_dec(v_b_1907_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1979_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v_a_1921_; lean_object* v_a_1928_; 
v___x_1919_ = lean_box(0);
v_a_1928_ = lean_array_uget_borrowed(v_as_1904_, v_i_1906_);
if (lean_obj_tag(v_a_1928_) == 0)
{
v_a_1921_ = v_snd_1915_;
goto v___jp_1920_;
}
else
{
lean_object* v_val_1929_; lean_object* v___y_1931_; uint8_t v___x_1935_; 
v_val_1929_ = lean_ctor_get(v_a_1928_, 0);
v___x_1935_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1929_);
if (v___x_1935_ == 0)
{
lean_object* v___f_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v_candidates_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___x_1957_; 
v___f_1936_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1938_ = l_Lean_LocalDecl_type(v_val_1929_);
lean_inc_ref(v___x_1938_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1937_, v___f_1936_, v___x_1935_, v___x_1938_, v_snd_1915_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
v___x_1959_ = l_Lean_LocalDecl_value_x3f(v_val_1929_, v___x_1935_);
if (lean_obj_tag(v___x_1959_) == 0)
{
v_candidates_1940_ = v_a_1958_;
v___y_1941_ = v___y_1908_;
v___y_1942_ = v___y_1909_;
v___y_1943_ = v___y_1910_;
v___y_1944_ = v___y_1911_;
goto v___jp_1939_;
}
else
{
lean_object* v_val_1960_; lean_object* v___x_1961_; 
v_val_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_val_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1937_, v___f_1936_, v___x_1935_, v_val_1960_, v_a_1958_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v_candidates_1940_ = v_a_1962_;
v___y_1941_ = v___y_1908_;
v___y_1942_ = v___y_1909_;
v___y_1943_ = v___y_1910_;
v___y_1944_ = v___y_1911_;
goto v___jp_1939_;
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v___x_1938_);
lean_del_object(v___x_1917_);
v_a_1963_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v___x_1938_);
lean_del_object(v___x_1917_);
v_a_1971_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1957_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1957_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
v___jp_1939_:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Meta_isProp(v___x_1938_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; uint8_t v___x_1947_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
if (v___x_1947_ == 0)
{
v_a_1921_ = v_candidates_1940_;
goto v___jp_1920_;
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = l_Lean_LocalDecl_hasValue(v_val_1929_, v___x_1935_);
if (v___x_1948_ == 0)
{
v___y_1931_ = v_candidates_1940_;
goto v___jp_1930_;
}
else
{
if (v___x_1935_ == 0)
{
v_a_1921_ = v_candidates_1940_;
goto v___jp_1920_;
}
else
{
v___y_1931_ = v_candidates_1940_;
goto v___jp_1930_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_candidates_1940_);
lean_del_object(v___x_1917_);
v_a_1949_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1945_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1945_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
v_a_1921_ = v_snd_1915_;
goto v___jp_1920_;
}
v___jp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = l_Lean_LocalDecl_fvarId(v_val_1929_);
v___x_1933_ = lean_box(0);
v___x_1934_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1931_, v___x_1932_, v___x_1933_);
v_a_1921_ = v___x_1934_;
goto v___jp_1920_;
}
}
v___jp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v_a_1921_);
lean_ctor_set(v___x_1917_, 0, v___x_1919_);
v___x_1923_ = v___x_1917_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1921_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
size_t v___x_1924_; size_t v___x_1925_; 
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_add(v_i_1906_, v___x_1924_);
v_i_1906_ = v___x_1925_;
v_b_1907_ = v___x_1923_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1981_, lean_object* v_sz_1982_, lean_object* v_i_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1982_);
lean_dec(v_sz_1982_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1981_, v_sz_boxed_1990_, v_i_boxed_1991_, v_b_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v_as_1981_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1993_, size_t v_sz_1994_, size_t v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_b_1996_);
return v___x_2003_;
}
else
{
lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2068_; 
v_snd_2004_ = lean_ctor_get(v_b_1996_, 1);
v_isSharedCheck_2068_ = !lean_is_exclusive(v_b_1996_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v_b_1996_, 0);
lean_dec(v_unused_2069_);
v___x_2006_ = v_b_1996_;
v_isShared_2007_ = v_isSharedCheck_2068_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_dec(v_b_1996_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2068_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v_a_2010_; lean_object* v_a_2017_; 
v___x_2008_ = lean_box(0);
v_a_2017_ = lean_array_uget_borrowed(v_as_1993_, v_i_1995_);
if (lean_obj_tag(v_a_2017_) == 0)
{
v_a_2010_ = v_snd_2004_;
goto v___jp_2009_;
}
else
{
lean_object* v_val_2018_; lean_object* v___y_2020_; uint8_t v___x_2024_; 
v_val_2018_ = lean_ctor_get(v_a_2017_, 0);
v___x_2024_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2018_);
if (v___x_2024_ == 0)
{
lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v_candidates_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___x_2046_; 
v___f_2025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2027_ = l_Lean_LocalDecl_type(v_val_2018_);
lean_inc_ref(v___x_2027_);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2026_, v___f_2025_, v___x_2024_, v___x_2027_, v_snd_2004_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = l_Lean_LocalDecl_value_x3f(v_val_2018_, v___x_2024_);
if (lean_obj_tag(v___x_2048_) == 0)
{
v_candidates_2029_ = v_a_2047_;
v___y_2030_ = v___y_1997_;
v___y_2031_ = v___y_1998_;
v___y_2032_ = v___y_1999_;
v___y_2033_ = v___y_2000_;
goto v___jp_2028_;
}
else
{
lean_object* v_val_2049_; lean_object* v___x_2050_; 
v_val_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2026_, v___f_2025_, v___x_2024_, v_val_2049_, v_a_2047_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v_candidates_2029_ = v_a_2051_;
v___y_2030_ = v___y_1997_;
v___y_2031_ = v___y_1998_;
v___y_2032_ = v___y_1999_;
v___y_2033_ = v___y_2000_;
goto v___jp_2028_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v___x_2027_);
lean_del_object(v___x_2006_);
v_a_2052_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2050_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v___x_2027_);
lean_del_object(v___x_2006_);
v_a_2060_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2046_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2046_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
v___jp_2028_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Meta_isProp(v___x_2027_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; uint8_t v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___x_2036_ = lean_unbox(v_a_2035_);
lean_dec(v_a_2035_);
if (v___x_2036_ == 0)
{
v_a_2010_ = v_candidates_2029_;
goto v___jp_2009_;
}
else
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Lean_LocalDecl_hasValue(v_val_2018_, v___x_2024_);
if (v___x_2037_ == 0)
{
v___y_2020_ = v_candidates_2029_;
goto v___jp_2019_;
}
else
{
if (v___x_2024_ == 0)
{
v_a_2010_ = v_candidates_2029_;
goto v___jp_2009_;
}
else
{
v___y_2020_ = v_candidates_2029_;
goto v___jp_2019_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_candidates_2029_);
lean_del_object(v___x_2006_);
v_a_2038_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2034_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2034_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
v_a_2010_ = v_snd_2004_;
goto v___jp_2009_;
}
v___jp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = l_Lean_LocalDecl_fvarId(v_val_2018_);
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2020_, v___x_2021_, v___x_2022_);
v_a_2010_ = v___x_2023_;
goto v___jp_2009_;
}
}
v___jp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v_a_2010_);
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2012_ = v___x_2006_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_a_2010_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
size_t v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = ((size_t)1ULL);
v___x_2014_ = lean_usize_add(v_i_1995_, v___x_2013_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1993_, v_sz_1994_, v___x_2014_, v___x_2012_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2015_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2070_, lean_object* v_sz_2071_, lean_object* v_i_2072_, lean_object* v_b_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
size_t v_sz_boxed_2079_; size_t v_i_boxed_2080_; lean_object* v_res_2081_; 
v_sz_boxed_2079_ = lean_unbox_usize(v_sz_2071_);
lean_dec(v_sz_2071_);
v_i_boxed_2080_ = lean_unbox_usize(v_i_2072_);
lean_dec(v_i_2072_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2070_, v_sz_boxed_2079_, v_i_boxed_2080_, v_b_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec_ref(v_as_2070_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2082_, lean_object* v_n_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
if (lean_obj_tag(v_n_2083_) == 0)
{
lean_object* v_cs_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2124_; 
v_cs_2090_ = lean_ctor_get(v_n_2083_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_n_2083_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2092_ = v_n_2083_;
v_isShared_2093_ = v_isSharedCheck_2124_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_cs_2090_);
lean_dec(v_n_2083_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2124_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; size_t v_sz_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v_b_2084_);
v_sz_2096_ = lean_array_size(v_cs_2090_);
v___x_2097_ = ((size_t)0ULL);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2082_, v_cs_2090_, v_sz_2096_, v___x_2097_, v___x_2095_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec_ref(v_cs_2090_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2115_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_fst_2103_; 
v_fst_2103_ = lean_ctor_get(v_a_2099_, 0);
if (lean_obj_tag(v_fst_2103_) == 0)
{
lean_object* v_snd_2104_; lean_object* v___x_2106_; 
v_snd_2104_ = lean_ctor_get(v_a_2099_, 1);
lean_inc(v_snd_2104_);
lean_dec(v_a_2099_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 0, v_snd_2104_);
v___x_2106_ = v___x_2092_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_snd_2104_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2106_);
v___x_2108_ = v___x_2101_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_val_2111_; lean_object* v___x_2113_; 
lean_inc_ref(v_fst_2103_);
lean_dec(v_a_2099_);
lean_del_object(v___x_2092_);
v_val_2111_ = lean_ctor_get(v_fst_2103_, 0);
lean_inc(v_val_2111_);
lean_dec_ref(v_fst_2103_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v_val_2111_);
v___x_2113_ = v___x_2101_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_val_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_del_object(v___x_2092_);
v_a_2116_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2098_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2098_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
else
{
lean_object* v_vs_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2159_; 
v_vs_2125_ = lean_ctor_get(v_n_2083_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_n_2083_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2127_ = v_n_2083_;
v_isShared_2128_ = v_isSharedCheck_2159_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_vs_2125_);
lean_dec(v_n_2083_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2159_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_b_2084_);
v_sz_2131_ = lean_array_size(v_vs_2125_);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2125_, v_sz_2131_, v___x_2132_, v___x_2130_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
lean_dec_ref(v_vs_2125_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2150_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2150_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2150_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; 
v_fst_2138_ = lean_ctor_get(v_a_2134_, 0);
if (lean_obj_tag(v_fst_2138_) == 0)
{
lean_object* v_snd_2139_; lean_object* v___x_2141_; 
v_snd_2139_ = lean_ctor_get(v_a_2134_, 1);
lean_inc(v_snd_2139_);
lean_dec(v_a_2134_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v_snd_2139_);
v___x_2141_ = v___x_2127_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_snd_2139_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2141_);
v___x_2143_ = v___x_2136_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
lean_object* v_val_2146_; lean_object* v___x_2148_; 
lean_inc_ref(v_fst_2138_);
lean_dec(v_a_2134_);
lean_del_object(v___x_2127_);
v_val_2146_ = lean_ctor_get(v_fst_2138_, 0);
lean_inc(v_val_2146_);
lean_dec_ref(v_fst_2138_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_val_2146_);
v___x_2148_ = v___x_2136_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_val_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_del_object(v___x_2127_);
v_a_2151_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2133_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2133_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2160_, lean_object* v_as_2161_, size_t v_sz_2162_, size_t v_i_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_b_2164_);
return v___x_2171_;
}
else
{
lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2206_; 
v_snd_2172_ = lean_ctor_get(v_b_2164_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_b_2164_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v_b_2164_, 0);
lean_dec(v_unused_2207_);
v___x_2174_ = v_b_2164_;
v_isShared_2175_ = v_isSharedCheck_2206_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_dec(v_b_2164_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2206_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_array_uget_borrowed(v_as_2161_, v_i_2163_);
lean_inc(v_snd_2172_);
lean_inc(v_a_2176_);
v___x_2177_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2160_, v_a_2176_, v_snd_2172_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2197_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2197_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2197_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
if (lean_obj_tag(v_a_2178_) == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2178_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2182_);
v___x_2184_ = v___x_2174_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_snd_2172_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2184_);
v___x_2186_ = v___x_2180_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_del_object(v___x_2180_);
lean_dec(v_snd_2172_);
v_a_2189_ = lean_ctor_get(v_a_2178_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v_a_2178_);
v___x_2190_ = lean_box(0);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_a_2189_);
lean_ctor_set(v___x_2174_, 0, v___x_2190_);
v___x_2192_ = v___x_2174_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2189_);
v___x_2192_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
size_t v___x_2193_; size_t v___x_2194_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_add(v_i_2163_, v___x_2193_);
v_i_2163_ = v___x_2194_;
v_b_2164_ = v___x_2192_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_del_object(v___x_2174_);
lean_dec(v_snd_2172_);
v_a_2198_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2177_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2177_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2208_, lean_object* v_as_2209_, lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_b_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
size_t v_sz_boxed_2218_; size_t v_i_boxed_2219_; lean_object* v_res_2220_; 
v_sz_boxed_2218_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2219_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2208_, v_as_2209_, v_sz_boxed_2218_, v_i_boxed_2219_, v_b_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v_as_2209_);
lean_dec_ref(v_init_2208_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2221_, lean_object* v_n_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2221_, v_n_2222_, v_b_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_init_2221_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2230_, lean_object* v_init_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_root_2237_; lean_object* v_tail_2238_; lean_object* v___x_2239_; 
v_root_2237_ = lean_ctor_get(v_t_2230_, 0);
lean_inc_ref(v_root_2237_);
v_tail_2238_ = lean_ctor_get(v_t_2230_, 1);
lean_inc_ref(v_tail_2238_);
lean_dec_ref(v_t_2230_);
lean_inc_ref(v_init_2231_);
v___x_2239_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2231_, v_root_2237_, v_init_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec_ref(v_init_2231_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2276_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2276_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
if (lean_obj_tag(v_a_2240_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; 
lean_dec_ref(v_tail_2238_);
v_a_2244_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v_a_2240_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v_a_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
lean_del_object(v___x_2242_);
v_a_2248_ = lean_ctor_get(v_a_2240_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v_a_2240_);
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_a_2248_);
v_sz_2251_ = lean_array_size(v_tail_2238_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2238_, v_sz_2251_, v___x_2252_, v___x_2250_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec_ref(v_tail_2238_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2267_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_fst_2258_; 
v_fst_2258_ = lean_ctor_get(v_a_2254_, 0);
if (lean_obj_tag(v_fst_2258_) == 0)
{
lean_object* v_snd_2259_; lean_object* v___x_2261_; 
v_snd_2259_ = lean_ctor_get(v_a_2254_, 1);
lean_inc(v_snd_2259_);
lean_dec(v_a_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_snd_2259_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_snd_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_object* v_val_2263_; lean_object* v___x_2265_; 
lean_inc_ref(v_fst_2258_);
lean_dec(v_a_2254_);
v_val_2263_ = lean_ctor_get(v_fst_2258_, 0);
lean_inc(v_val_2263_);
lean_dec_ref(v_fst_2258_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_val_2263_);
v___x_2265_ = v___x_2256_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_val_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2253_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2253_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v_tail_2238_);
v_a_2277_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2239_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2239_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2285_, lean_object* v_init_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2285_, v_init_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_buckets_2295_; lean_object* v___x_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v___x_2299_; uint64_t v_fold_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; uint64_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_buckets_2295_ = lean_ctor_get(v_m_2293_, 1);
v___x_2296_ = lean_array_get_size(v_buckets_2295_);
v___x_2297_ = l_Lean_instHashableFVarId_hash(v_a_2294_);
v___x_2298_ = 32ULL;
v___x_2299_ = lean_uint64_shift_right(v___x_2297_, v___x_2298_);
v_fold_2300_ = lean_uint64_xor(v___x_2297_, v___x_2299_);
v___x_2301_ = 16ULL;
v___x_2302_ = lean_uint64_shift_right(v_fold_2300_, v___x_2301_);
v___x_2303_ = lean_uint64_xor(v_fold_2300_, v___x_2302_);
v___x_2304_ = lean_uint64_to_usize(v___x_2303_);
v___x_2305_ = lean_usize_of_nat(v___x_2296_);
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_sub(v___x_2305_, v___x_2306_);
v___x_2308_ = lean_usize_land(v___x_2304_, v___x_2307_);
v___x_2309_ = lean_array_uget_borrowed(v_buckets_2295_, v___x_2308_);
v___x_2310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2294_, v___x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2311_, lean_object* v_a_2312_){
_start:
{
uint8_t v_res_2313_; lean_object* v_r_2314_; 
v_res_2313_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_m_2311_);
v_r_2314_ = lean_box(v_res_2313_);
return v_r_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2315_, lean_object* v_as_2316_, size_t v_sz_2317_, size_t v_i_2318_, lean_object* v_b_2319_){
_start:
{
uint8_t v___x_2321_; 
v___x_2321_ = lean_usize_dec_lt(v_i_2318_, v_sz_2317_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v_b_2319_);
return v___x_2322_;
}
else
{
lean_object* v_snd_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2341_; 
v_snd_2323_ = lean_ctor_get(v_b_2319_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_b_2319_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v_b_2319_, 0);
lean_dec(v_unused_2342_);
v___x_2325_ = v_b_2319_;
v_isShared_2326_ = v_isSharedCheck_2341_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_snd_2323_);
lean_dec(v_b_2319_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2341_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v_a_2329_; lean_object* v_a_2336_; 
v___x_2327_ = lean_box(0);
v_a_2336_ = lean_array_uget_borrowed(v_as_2316_, v_i_2318_);
if (lean_obj_tag(v_a_2336_) == 0)
{
v_a_2329_ = v_snd_2323_;
goto v___jp_2328_;
}
else
{
lean_object* v_val_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_val_2337_ = lean_ctor_get(v_a_2336_, 0);
v___x_2338_ = l_Lean_LocalDecl_fvarId(v_val_2337_);
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2315_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_dec(v___x_2338_);
v_a_2329_ = v_snd_2323_;
goto v___jp_2328_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_array_push(v_snd_2323_, v___x_2338_);
v_a_2329_ = v___x_2340_;
goto v___jp_2328_;
}
}
v___jp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_a_2329_);
lean_ctor_set(v___x_2325_, 0, v___x_2327_);
v___x_2331_ = v___x_2325_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_a_2329_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
size_t v___x_2332_; size_t v___x_2333_; 
v___x_2332_ = ((size_t)1ULL);
v___x_2333_ = lean_usize_add(v_i_2318_, v___x_2332_);
v_i_2318_ = v___x_2333_;
v_b_2319_ = v___x_2331_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2343_, lean_object* v_as_2344_, lean_object* v_sz_2345_, lean_object* v_i_2346_, lean_object* v_b_2347_, lean_object* v___y_2348_){
_start:
{
size_t v_sz_boxed_2349_; size_t v_i_boxed_2350_; lean_object* v_res_2351_; 
v_sz_boxed_2349_ = lean_unbox_usize(v_sz_2345_);
lean_dec(v_sz_2345_);
v_i_boxed_2350_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2343_, v_as_2344_, v_sz_boxed_2349_, v_i_boxed_2350_, v_b_2347_);
lean_dec_ref(v_as_2344_);
lean_dec_ref(v_a_2343_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2352_, lean_object* v_as_2353_, size_t v_sz_2354_, size_t v_i_2355_, lean_object* v_b_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v___x_2362_; 
v___x_2362_ = lean_usize_dec_lt(v_i_2355_, v_sz_2354_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_b_2356_);
return v___x_2363_;
}
else
{
lean_object* v_snd_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2382_; 
v_snd_2364_ = lean_ctor_get(v_b_2356_, 1);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_b_2356_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v_b_2356_, 0);
lean_dec(v_unused_2383_);
v___x_2366_ = v_b_2356_;
v_isShared_2367_ = v_isSharedCheck_2382_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_snd_2364_);
lean_dec(v_b_2356_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2382_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v_a_2370_; lean_object* v_a_2377_; 
v___x_2368_ = lean_box(0);
v_a_2377_ = lean_array_uget_borrowed(v_as_2353_, v_i_2355_);
if (lean_obj_tag(v_a_2377_) == 0)
{
v_a_2370_ = v_snd_2364_;
goto v___jp_2369_;
}
else
{
lean_object* v_val_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v_val_2378_ = lean_ctor_get(v_a_2377_, 0);
v___x_2379_ = l_Lean_LocalDecl_fvarId(v_val_2378_);
v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2352_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec(v___x_2379_);
v_a_2370_ = v_snd_2364_;
goto v___jp_2369_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_array_push(v_snd_2364_, v___x_2379_);
v_a_2370_ = v___x_2381_;
goto v___jp_2369_;
}
}
v___jp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v_a_2370_);
lean_ctor_set(v___x_2366_, 0, v___x_2368_);
v___x_2372_ = v___x_2366_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_a_2370_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_add(v_i_2355_, v___x_2373_);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2352_, v_as_2353_, v_sz_2354_, v___x_2374_, v___x_2372_);
return v___x_2375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2384_, lean_object* v_as_2385_, lean_object* v_sz_2386_, lean_object* v_i_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
size_t v_sz_boxed_2394_; size_t v_i_boxed_2395_; lean_object* v_res_2396_; 
v_sz_boxed_2394_ = lean_unbox_usize(v_sz_2386_);
lean_dec(v_sz_2386_);
v_i_boxed_2395_ = lean_unbox_usize(v_i_2387_);
lean_dec(v_i_2387_);
v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2384_, v_as_2385_, v_sz_boxed_2394_, v_i_boxed_2395_, v_b_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v_as_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2397_, lean_object* v_a_2398_, lean_object* v_n_2399_, lean_object* v_b_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
if (lean_obj_tag(v_n_2399_) == 0)
{
lean_object* v_cs_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2440_; 
v_cs_2406_ = lean_ctor_get(v_n_2399_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_n_2399_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2408_ = v_n_2399_;
v_isShared_2409_ = v_isSharedCheck_2440_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_cs_2406_);
lean_dec(v_n_2399_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2440_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; size_t v_sz_2412_; size_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_b_2400_);
v_sz_2412_ = lean_array_size(v_cs_2406_);
v___x_2413_ = ((size_t)0ULL);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2397_, v_a_2398_, v_cs_2406_, v_sz_2412_, v___x_2413_, v___x_2411_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v_cs_2406_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2431_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2431_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_fst_2419_; 
v_fst_2419_ = lean_ctor_get(v_a_2415_, 0);
if (lean_obj_tag(v_fst_2419_) == 0)
{
lean_object* v_snd_2420_; lean_object* v___x_2422_; 
v_snd_2420_ = lean_ctor_get(v_a_2415_, 1);
lean_inc(v_snd_2420_);
lean_dec(v_a_2415_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set_tag(v___x_2408_, 1);
lean_ctor_set(v___x_2408_, 0, v_snd_2420_);
v___x_2422_ = v___x_2408_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_snd_2420_);
v___x_2422_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2422_);
v___x_2424_ = v___x_2417_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2429_; 
lean_inc_ref(v_fst_2419_);
lean_dec(v_a_2415_);
lean_del_object(v___x_2408_);
v_val_2427_ = lean_ctor_get(v_fst_2419_, 0);
lean_inc(v_val_2427_);
lean_dec_ref(v_fst_2419_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v_val_2427_);
v___x_2429_ = v___x_2417_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_del_object(v___x_2408_);
v_a_2432_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2414_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2414_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
else
{
lean_object* v_vs_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2475_; 
v_vs_2441_ = lean_ctor_get(v_n_2399_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_n_2399_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2443_ = v_n_2399_;
v_isShared_2444_ = v_isSharedCheck_2475_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_vs_2441_);
lean_dec(v_n_2399_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2475_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2445_ = lean_box(0);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v_b_2400_);
v_sz_2447_ = lean_array_size(v_vs_2441_);
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2398_, v_vs_2441_, v_sz_2447_, v___x_2448_, v___x_2446_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v_vs_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2466_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2466_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2466_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_fst_2454_; 
v_fst_2454_ = lean_ctor_get(v_a_2450_, 0);
if (lean_obj_tag(v_fst_2454_) == 0)
{
lean_object* v_snd_2455_; lean_object* v___x_2457_; 
v_snd_2455_ = lean_ctor_get(v_a_2450_, 1);
lean_inc(v_snd_2455_);
lean_dec(v_a_2450_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v_snd_2455_);
v___x_2457_ = v___x_2443_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_snd_2455_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2457_);
v___x_2459_ = v___x_2452_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; 
lean_inc_ref(v_fst_2454_);
lean_dec(v_a_2450_);
lean_del_object(v___x_2443_);
v_val_2462_ = lean_ctor_get(v_fst_2454_, 0);
lean_inc(v_val_2462_);
lean_dec_ref(v_fst_2454_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_val_2462_);
v___x_2464_ = v___x_2452_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_val_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_del_object(v___x_2443_);
v_a_2467_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2449_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2449_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2476_, lean_object* v_a_2477_, lean_object* v_as_2478_, size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_lt(v_i_2480_, v_sz_2479_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_b_2481_);
return v___x_2488_;
}
else
{
lean_object* v_snd_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2523_; 
v_snd_2489_ = lean_ctor_get(v_b_2481_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_b_2481_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v_b_2481_, 0);
lean_dec(v_unused_2524_);
v___x_2491_ = v_b_2481_;
v_isShared_2492_ = v_isSharedCheck_2523_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snd_2489_);
lean_dec(v_b_2481_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2523_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_array_uget_borrowed(v_as_2478_, v_i_2480_);
lean_inc(v_snd_2489_);
lean_inc(v_a_2493_);
v___x_2494_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2476_, v_a_2477_, v_a_2493_, v_snd_2489_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2514_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2514_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2514_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
if (lean_obj_tag(v_a_2495_) == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2495_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___x_2499_);
v___x_2501_ = v___x_2491_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_snd_2489_);
v___x_2501_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2503_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2501_);
v___x_2503_ = v___x_2497_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_del_object(v___x_2497_);
lean_dec(v_snd_2489_);
v_a_2506_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v_a_2495_);
v___x_2507_ = lean_box(0);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_a_2506_);
lean_ctor_set(v___x_2491_, 0, v___x_2507_);
v___x_2509_ = v___x_2491_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_a_2506_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
size_t v___x_2510_; size_t v___x_2511_; 
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2480_, v___x_2510_);
v_i_2480_ = v___x_2511_;
v_b_2481_ = v___x_2509_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_del_object(v___x_2491_);
lean_dec(v_snd_2489_);
v_a_2515_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2494_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2494_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2525_, lean_object* v_a_2526_, lean_object* v_as_2527_, lean_object* v_sz_2528_, lean_object* v_i_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
size_t v_sz_boxed_2536_; size_t v_i_boxed_2537_; lean_object* v_res_2538_; 
v_sz_boxed_2536_ = lean_unbox_usize(v_sz_2528_);
lean_dec(v_sz_2528_);
v_i_boxed_2537_ = lean_unbox_usize(v_i_2529_);
lean_dec(v_i_2529_);
v_res_2538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2525_, v_a_2526_, v_as_2527_, v_sz_boxed_2536_, v_i_boxed_2537_, v_b_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_as_2527_);
lean_dec_ref(v_a_2526_);
lean_dec_ref(v_init_2525_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2539_, lean_object* v_a_2540_, lean_object* v_n_2541_, lean_object* v_b_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2539_, v_a_2540_, v_n_2541_, v_b_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec_ref(v_a_2540_);
lean_dec_ref(v_init_2539_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2549_, lean_object* v_as_2550_, size_t v_sz_2551_, size_t v_i_2552_, lean_object* v_b_2553_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_lt(v_i_2552_, v_sz_2551_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_b_2553_);
return v___x_2556_;
}
else
{
lean_object* v_snd_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2575_; 
v_snd_2557_ = lean_ctor_get(v_b_2553_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_b_2553_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_b_2553_, 0);
lean_dec(v_unused_2576_);
v___x_2559_ = v_b_2553_;
v_isShared_2560_ = v_isSharedCheck_2575_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_snd_2557_);
lean_dec(v_b_2553_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2575_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v_a_2563_; lean_object* v_a_2570_; 
v___x_2561_ = lean_box(0);
v_a_2570_ = lean_array_uget_borrowed(v_as_2550_, v_i_2552_);
if (lean_obj_tag(v_a_2570_) == 0)
{
v_a_2563_ = v_snd_2557_;
goto v___jp_2562_;
}
else
{
lean_object* v_val_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_val_2571_ = lean_ctor_get(v_a_2570_, 0);
v___x_2572_ = l_Lean_LocalDecl_fvarId(v_val_2571_);
v___x_2573_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2549_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec(v___x_2572_);
v_a_2563_ = v_snd_2557_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_array_push(v_snd_2557_, v___x_2572_);
v_a_2563_ = v___x_2574_;
goto v___jp_2562_;
}
}
v___jp_2562_:
{
lean_object* v___x_2565_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v_a_2563_);
lean_ctor_set(v___x_2559_, 0, v___x_2561_);
v___x_2565_ = v___x_2559_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2563_);
v___x_2565_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
size_t v___x_2566_; size_t v___x_2567_; 
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_add(v_i_2552_, v___x_2566_);
v_i_2552_ = v___x_2567_;
v_b_2553_ = v___x_2565_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2577_, lean_object* v_as_2578_, lean_object* v_sz_2579_, lean_object* v_i_2580_, lean_object* v_b_2581_, lean_object* v___y_2582_){
_start:
{
size_t v_sz_boxed_2583_; size_t v_i_boxed_2584_; lean_object* v_res_2585_; 
v_sz_boxed_2583_ = lean_unbox_usize(v_sz_2579_);
lean_dec(v_sz_2579_);
v_i_boxed_2584_ = lean_unbox_usize(v_i_2580_);
lean_dec(v_i_2580_);
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2577_, v_as_2578_, v_sz_boxed_2583_, v_i_boxed_2584_, v_b_2581_);
lean_dec_ref(v_as_2578_);
lean_dec_ref(v_a_2577_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2586_, lean_object* v_as_2587_, size_t v_sz_2588_, size_t v_i_2589_, lean_object* v_b_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v___x_2596_; 
v___x_2596_ = lean_usize_dec_lt(v_i_2589_, v_sz_2588_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v_b_2590_);
return v___x_2597_;
}
else
{
lean_object* v_snd_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2616_; 
v_snd_2598_ = lean_ctor_get(v_b_2590_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_b_2590_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_b_2590_, 0);
lean_dec(v_unused_2617_);
v___x_2600_ = v_b_2590_;
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2598_);
lean_dec(v_b_2590_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v_a_2604_; lean_object* v_a_2611_; 
v___x_2602_ = lean_box(0);
v_a_2611_ = lean_array_uget_borrowed(v_as_2587_, v_i_2589_);
if (lean_obj_tag(v_a_2611_) == 0)
{
v_a_2604_ = v_snd_2598_;
goto v___jp_2603_;
}
else
{
lean_object* v_val_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v_val_2612_ = lean_ctor_get(v_a_2611_, 0);
v___x_2613_ = l_Lean_LocalDecl_fvarId(v_val_2612_);
v___x_2614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2586_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2613_);
v_a_2604_ = v_snd_2598_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_array_push(v_snd_2598_, v___x_2613_);
v_a_2604_ = v___x_2615_;
goto v___jp_2603_;
}
}
v___jp_2603_:
{
lean_object* v___x_2606_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v_a_2604_);
lean_ctor_set(v___x_2600_, 0, v___x_2602_);
v___x_2606_ = v___x_2600_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_a_2604_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = ((size_t)1ULL);
v___x_2608_ = lean_usize_add(v_i_2589_, v___x_2607_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2586_, v_as_2587_, v_sz_2588_, v___x_2608_, v___x_2606_);
return v___x_2609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2618_, lean_object* v_as_2619_, lean_object* v_sz_2620_, lean_object* v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
size_t v_sz_boxed_2628_; size_t v_i_boxed_2629_; lean_object* v_res_2630_; 
v_sz_boxed_2628_ = lean_unbox_usize(v_sz_2620_);
lean_dec(v_sz_2620_);
v_i_boxed_2629_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2618_, v_as_2619_, v_sz_boxed_2628_, v_i_boxed_2629_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v_as_2619_);
lean_dec_ref(v_a_2618_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2631_, lean_object* v_t_2632_, lean_object* v_init_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_root_2639_; lean_object* v_tail_2640_; lean_object* v___x_2641_; 
v_root_2639_ = lean_ctor_get(v_t_2632_, 0);
lean_inc_ref(v_root_2639_);
v_tail_2640_ = lean_ctor_get(v_t_2632_, 1);
lean_inc_ref(v_tail_2640_);
lean_dec_ref(v_t_2632_);
lean_inc_ref(v_init_2633_);
v___x_2641_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2633_, v_a_2631_, v_root_2639_, v_init_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec_ref(v_init_2633_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2678_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2678_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2678_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
if (lean_obj_tag(v_a_2642_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; 
lean_dec_ref(v_tail_2640_);
v_a_2646_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v_a_2642_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_a_2646_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; size_t v_sz_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
lean_del_object(v___x_2644_);
v_a_2650_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v_a_2642_);
v___x_2651_ = lean_box(0);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v_a_2650_);
v_sz_2653_ = lean_array_size(v_tail_2640_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2631_, v_tail_2640_, v_sz_2653_, v___x_2654_, v___x_2652_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec_ref(v_tail_2640_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2669_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2669_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2669_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_fst_2660_; 
v_fst_2660_ = lean_ctor_get(v_a_2656_, 0);
if (lean_obj_tag(v_fst_2660_) == 0)
{
lean_object* v_snd_2661_; lean_object* v___x_2663_; 
v_snd_2661_ = lean_ctor_get(v_a_2656_, 1);
lean_inc(v_snd_2661_);
lean_dec(v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_snd_2661_);
v___x_2663_ = v___x_2658_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_snd_2661_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
else
{
lean_object* v_val_2665_; lean_object* v___x_2667_; 
lean_inc_ref(v_fst_2660_);
lean_dec(v_a_2656_);
v_val_2665_ = lean_ctor_get(v_fst_2660_, 0);
lean_inc(v_val_2665_);
lean_dec_ref(v_fst_2660_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v_val_2665_);
v___x_2667_ = v___x_2658_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_val_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2655_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2655_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v_tail_2640_);
v_a_2679_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2641_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2641_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2687_, lean_object* v_t_2688_, lean_object* v_init_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2687_, v_t_2688_, v_init_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec_ref(v_a_2687_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2698_, lean_object* v_mvarId_2699_, lean_object* v___f_2700_, lean_object* v___f_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_lctx_2707_; lean_object* v_decls_2708_; lean_object* v___x_2709_; 
v_lctx_2707_ = lean_ctor_get(v___y_2702_, 2);
v_decls_2708_ = lean_ctor_get(v_lctx_2707_, 1);
lean_inc_ref_n(v_decls_2708_, 2);
v___x_2709_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2708_, v_candidates_2698_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref(v___x_2709_);
v___x_2711_ = l_Lean_MVarId_getType(v_mvarId_2699_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___y_2717_; uint8_t v___x_2741_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2712_, v___y_2703_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = lean_st_mk_ref(v_a_2710_);
v___x_2741_ = l_Lean_Expr_hasFVar(v_a_2714_);
if (v___x_2741_ == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec(v_a_2714_);
lean_dec_ref(v___f_2701_);
v___x_2742_ = lean_box(0);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___x_2715_);
v___x_2743_ = lean_apply_7(v___f_2700_, v___x_2742_, v___x_2715_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
v___y_2717_ = v___x_2743_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2745_ = 0;
v___x_2746_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2744_, v___f_2701_, v_a_2714_, v___x_2745_, v___x_2715_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___x_2715_);
v___x_2748_ = lean_apply_7(v___f_2700_, v_a_2747_, v___x_2715_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
v___y_2717_ = v___x_2748_;
goto v___jp_2716_;
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v___x_2715_);
lean_dec_ref(v_decls_2708_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___f_2700_);
v_a_2749_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2746_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2746_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
v___jp_2716_:
{
if (lean_obj_tag(v___y_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2732_; 
v_a_2718_ = lean_ctor_get(v___y_2717_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___y_2717_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2720_ = v___y_2717_;
v_isShared_2721_ = v_isSharedCheck_2732_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___y_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2732_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v_size_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2722_ = lean_st_ref_get(v___x_2715_);
lean_dec(v___x_2715_);
lean_dec(v___x_2722_);
v_size_2723_ = lean_ctor_get(v_a_2718_, 0);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_nat_dec_eq(v_size_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_del_object(v___x_2720_);
v___x_2726_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2727_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2718_, v_decls_2708_, v___x_2726_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v_a_2718_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
lean_dec(v_a_2718_);
lean_dec_ref(v_decls_2708_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
v___x_2728_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2728_);
v___x_2730_ = v___x_2720_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v___x_2715_);
lean_dec_ref(v_decls_2708_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
v_a_2733_ = lean_ctor_get(v___y_2717_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___y_2717_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___y_2717_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___y_2717_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2710_);
lean_dec_ref(v_decls_2708_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___f_2701_);
lean_dec_ref(v___f_2700_);
v_a_2757_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2711_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2711_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v_decls_2708_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___f_2701_);
lean_dec_ref(v___f_2700_);
lean_dec(v_mvarId_2699_);
v_a_2765_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2709_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2709_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2773_, lean_object* v_mvarId_2774_, lean_object* v___f_2775_, lean_object* v___f_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2773_, v_mvarId_2774_, v___f_2775_, v___f_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___f_2791_; lean_object* v___f_2792_; lean_object* v_candidates_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
v___f_2791_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2792_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2793_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2785_);
v___f_2794_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2794_, 0, v_candidates_2793_);
lean_closure_set(v___f_2794_, 1, v_mvarId_2785_);
lean_closure_set(v___f_2794_, 2, v___f_2792_);
lean_closure_set(v___f_2794_, 3, v___f_2791_);
v___x_2795_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2785_, v___f_2794_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2803_, lean_object* v_m_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2804_, v_a_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_m_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2807_, v_m_2808_, v_a_2809_);
lean_dec(v_a_2809_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2811_, lean_object* v_m_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2812_, v_a_2813_, v_b_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2816_, lean_object* v_m_2817_, lean_object* v_a_2818_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2817_, v_a_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2820_, lean_object* v_m_2821_, lean_object* v_a_2822_){
_start:
{
uint8_t v_res_2823_; lean_object* v_r_2824_; 
v_res_2823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2820_, v_m_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_m_2821_);
v_r_2824_ = lean_box(v_res_2823_);
return v_r_2824_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2825_, lean_object* v_a_2826_, lean_object* v_x_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2826_, v_x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2829_, lean_object* v_a_2830_, lean_object* v_x_2831_){
_start:
{
uint8_t v_res_2832_; lean_object* v_r_2833_; 
v_res_2832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2829_, v_a_2830_, v_x_2831_);
lean_dec(v_x_2831_);
lean_dec(v_a_2830_);
v_r_2833_ = lean_box(v_res_2832_);
return v_r_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2834_, lean_object* v_a_2835_, lean_object* v_x_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2835_, v_x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2838_, lean_object* v_a_2839_, lean_object* v_x_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2838_, v_a_2839_, v_x_2840_);
lean_dec(v_a_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2842_, lean_object* v_a_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2842_, v_a_2843_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2851_, lean_object* v_a_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2851_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec(v_a_2852_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2860_, lean_object* v_data_2861_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2863_, lean_object* v_a_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2863_, v_a_2864_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2872_, lean_object* v_a_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2872_, v_a_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v_a_2873_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2881_, lean_object* v_i_2882_, lean_object* v_source_2883_, lean_object* v_target_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2882_, v_source_2883_, v_target_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2886_, lean_object* v_as_2887_, size_t v_sz_2888_, size_t v_i_2889_, lean_object* v_b_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2886_, v_as_2887_, v_sz_2888_, v_i_2889_, v_b_2890_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2897_, lean_object* v_as_2898_, lean_object* v_sz_2899_, lean_object* v_i_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
size_t v_sz_boxed_2907_; size_t v_i_boxed_2908_; lean_object* v_res_2909_; 
v_sz_boxed_2907_ = lean_unbox_usize(v_sz_2899_);
lean_dec(v_sz_2899_);
v_i_boxed_2908_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_res_2909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2897_, v_as_2898_, v_sz_boxed_2907_, v_i_boxed_2908_, v_b_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v_as_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2909_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2910_, lean_object* v_m_2911_, lean_object* v_a_2912_){
_start:
{
uint8_t v___x_2913_; 
v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2911_, v_a_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2914_, lean_object* v_m_2915_, lean_object* v_a_2916_){
_start:
{
uint8_t v_res_2917_; lean_object* v_r_2918_; 
v_res_2917_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2914_, v_m_2915_, v_a_2916_);
lean_dec_ref(v_a_2916_);
lean_dec_ref(v_m_2915_);
v_r_2918_ = lean_box(v_res_2917_);
return v_r_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2919_, lean_object* v_m_2920_, lean_object* v_a_2921_, lean_object* v_b_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2920_, v_a_2921_, v_b_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2924_, lean_object* v_x_2925_, lean_object* v_x_2926_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2925_, v_x_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2928_, lean_object* v_as_2929_, size_t v_sz_2930_, size_t v_i_2931_, lean_object* v_b_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2928_, v_as_2929_, v_sz_2930_, v_i_2931_, v_b_2932_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2939_, lean_object* v_as_2940_, lean_object* v_sz_2941_, lean_object* v_i_2942_, lean_object* v_b_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
size_t v_sz_boxed_2949_; size_t v_i_boxed_2950_; lean_object* v_res_2951_; 
v_sz_boxed_2949_ = lean_unbox_usize(v_sz_2941_);
lean_dec(v_sz_2941_);
v_i_boxed_2950_ = lean_unbox_usize(v_i_2942_);
lean_dec(v_i_2942_);
v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2939_, v_as_2940_, v_sz_boxed_2949_, v_i_boxed_2950_, v_b_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_as_2940_);
lean_dec_ref(v_a_2939_);
return v_res_2951_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2952_, lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
uint8_t v___x_2955_; 
v___x_2955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2953_, v_x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2956_, lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
uint8_t v_res_2959_; lean_object* v_r_2960_; 
v_res_2959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2956_, v_a_2957_, v_x_2958_);
lean_dec(v_x_2958_);
lean_dec_ref(v_a_2957_);
v_r_2960_ = lean_box(v_res_2959_);
return v_r_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2961_, lean_object* v_data_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2964_, lean_object* v_i_2965_, lean_object* v_source_2966_, lean_object* v_target_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2965_, v_source_2966_, v_target_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2969_, lean_object* v_x_2970_, lean_object* v_x_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2970_, v_x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = l_Lean_maxRecDepthErrorMessage;
v___x_2979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2981_ = l_Lean_MessageData_ofFormat(v___x_2980_);
return v___x_2981_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2983_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2984_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
lean_ctor_set(v___x_2984_, 1, v___x_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_ref_2985_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2993_, lean_object* v_ref_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2994_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_ref_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_3002_, v_ref_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3011_, lean_object* v_mvarId_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_fileName_3019_; lean_object* v_fileMap_3020_; lean_object* v_options_3021_; lean_object* v_currRecDepth_3022_; lean_object* v_maxRecDepth_3023_; lean_object* v_ref_3024_; lean_object* v_currNamespace_3025_; lean_object* v_openDecls_3026_; lean_object* v_initHeartbeats_3027_; lean_object* v_maxHeartbeats_3028_; lean_object* v_quotContext_3029_; lean_object* v_currMacroScope_3030_; uint8_t v_diag_3031_; lean_object* v_cancelTk_x3f_3032_; uint8_t v_suppressElabErrors_3033_; lean_object* v_inheritedTraceOptions_3034_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_fileName_3019_ = lean_ctor_get(v_a_3016_, 0);
v_fileMap_3020_ = lean_ctor_get(v_a_3016_, 1);
v_options_3021_ = lean_ctor_get(v_a_3016_, 2);
v_currRecDepth_3022_ = lean_ctor_get(v_a_3016_, 3);
v_maxRecDepth_3023_ = lean_ctor_get(v_a_3016_, 4);
v_ref_3024_ = lean_ctor_get(v_a_3016_, 5);
v_currNamespace_3025_ = lean_ctor_get(v_a_3016_, 6);
v_openDecls_3026_ = lean_ctor_get(v_a_3016_, 7);
v_initHeartbeats_3027_ = lean_ctor_get(v_a_3016_, 8);
v_maxHeartbeats_3028_ = lean_ctor_get(v_a_3016_, 9);
v_quotContext_3029_ = lean_ctor_get(v_a_3016_, 10);
v_currMacroScope_3030_ = lean_ctor_get(v_a_3016_, 11);
v_diag_3031_ = lean_ctor_get_uint8(v_a_3016_, sizeof(void*)*14);
v_cancelTk_x3f_3032_ = lean_ctor_get(v_a_3016_, 12);
v_suppressElabErrors_3033_ = lean_ctor_get_uint8(v_a_3016_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3034_ = lean_ctor_get(v_a_3016_, 13);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_nat_dec_eq(v_maxRecDepth_3023_, v___x_3062_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_nat_dec_eq(v_currRecDepth_3022_, v_maxRecDepth_3023_);
if (v___x_3064_ == 0)
{
goto v___jp_3035_;
}
else
{
lean_object* v___x_3065_; 
lean_dec(v_mvarId_3012_);
lean_dec_ref(v_x_3011_);
lean_inc(v_ref_3024_);
v___x_3065_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3024_);
return v___x_3065_;
}
}
else
{
goto v___jp_3035_;
}
v___jp_3035_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_add(v_currRecDepth_3022_, v___x_3036_);
lean_inc_ref(v_inheritedTraceOptions_3034_);
lean_inc(v_cancelTk_x3f_3032_);
lean_inc(v_currMacroScope_3030_);
lean_inc(v_quotContext_3029_);
lean_inc(v_maxHeartbeats_3028_);
lean_inc(v_initHeartbeats_3027_);
lean_inc(v_openDecls_3026_);
lean_inc(v_currNamespace_3025_);
lean_inc(v_ref_3024_);
lean_inc(v_maxRecDepth_3023_);
lean_inc_ref(v_options_3021_);
lean_inc_ref(v_fileMap_3020_);
lean_inc_ref(v_fileName_3019_);
v___x_3038_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3038_, 0, v_fileName_3019_);
lean_ctor_set(v___x_3038_, 1, v_fileMap_3020_);
lean_ctor_set(v___x_3038_, 2, v_options_3021_);
lean_ctor_set(v___x_3038_, 3, v___x_3037_);
lean_ctor_set(v___x_3038_, 4, v_maxRecDepth_3023_);
lean_ctor_set(v___x_3038_, 5, v_ref_3024_);
lean_ctor_set(v___x_3038_, 6, v_currNamespace_3025_);
lean_ctor_set(v___x_3038_, 7, v_openDecls_3026_);
lean_ctor_set(v___x_3038_, 8, v_initHeartbeats_3027_);
lean_ctor_set(v___x_3038_, 9, v_maxHeartbeats_3028_);
lean_ctor_set(v___x_3038_, 10, v_quotContext_3029_);
lean_ctor_set(v___x_3038_, 11, v_currMacroScope_3030_);
lean_ctor_set(v___x_3038_, 12, v_cancelTk_x3f_3032_);
lean_ctor_set(v___x_3038_, 13, v_inheritedTraceOptions_3034_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*14, v_diag_3031_);
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*14 + 1, v_suppressElabErrors_3033_);
lean_inc_ref(v_x_3011_);
lean_inc(v_a_3017_);
lean_inc_ref(v___x_3038_);
lean_inc(v_a_3015_);
lean_inc_ref(v_a_3014_);
lean_inc(v_mvarId_3012_);
v___x_3039_ = lean_apply_6(v_x_3011_, v_mvarId_3012_, v_a_3014_, v_a_3015_, v___x_3038_, v_a_3017_, lean_box(0));
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3053_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3053_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
if (lean_obj_tag(v_a_3040_) == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_dec_ref(v___x_3038_);
lean_dec_ref(v_x_3011_);
v___x_3044_ = lean_st_ref_take(v_a_3013_);
v___x_3045_ = lean_array_push(v___x_3044_, v_mvarId_3012_);
v___x_3046_ = lean_st_ref_set(v_a_3013_, v___x_3045_);
v___x_3047_ = lean_box(0);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3047_);
v___x_3049_ = v___x_3042_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v_val_3051_; lean_object* v___x_3052_; 
lean_del_object(v___x_3042_);
lean_dec(v_mvarId_3012_);
v_val_3051_ = lean_ctor_get(v_a_3040_, 0);
lean_inc(v_val_3051_);
lean_dec_ref(v_a_3040_);
v___x_3052_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3011_, v_val_3051_, v_a_3013_, v_a_3014_, v_a_3015_, v___x_3038_, v_a_3017_);
lean_dec_ref(v___x_3038_);
return v___x_3052_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___x_3038_);
lean_dec(v_mvarId_3012_);
lean_dec_ref(v_x_3011_);
v_a_3054_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3039_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3039_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3066_, lean_object* v_as_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
if (lean_obj_tag(v_as_3067_) == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v_x_3066_);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
else
{
lean_object* v_head_3076_; lean_object* v_tail_3077_; lean_object* v___x_3078_; 
v_head_3076_ = lean_ctor_get(v_as_3067_, 0);
lean_inc(v_head_3076_);
v_tail_3077_ = lean_ctor_get(v_as_3067_, 1);
lean_inc(v_tail_3077_);
lean_dec_ref(v_as_3067_);
lean_inc_ref(v_x_3066_);
v___x_3078_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3066_, v_head_3076_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_dec_ref(v___x_3078_);
v_as_3067_ = v_tail_3077_;
goto _start;
}
else
{
lean_dec(v_tail_3077_);
lean_dec_ref(v_x_3066_);
return v___x_3078_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3080_, lean_object* v_as_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3080_, v_as_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3089_, lean_object* v_mvarId_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3089_, v_mvarId_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3098_, lean_object* v_x_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3106_ = lean_st_mk_ref(v___x_3105_);
v___x_3107_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3099_, v_mvarId_3098_, v___x_3106_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3107_, 0);
lean_dec(v_unused_3117_);
v___x_3109_ = v___x_3107_;
v_isShared_3110_ = v_isSharedCheck_3116_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v___x_3107_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3116_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3111_ = lean_st_ref_get(v___x_3106_);
lean_dec(v___x_3106_);
v___x_3112_ = lean_array_to_list(v___x_3111_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3112_);
v___x_3114_ = v___x_3109_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v___x_3106_);
v_a_3118_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3107_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3107_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3126_, lean_object* v_x_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Meta_saturate(v_mvarId_3126_, v_x_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3134_, lean_object* v_msg_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
if (lean_obj_tag(v_mvarIds_3134_) == 1)
{
lean_object* v_tail_3141_; 
v_tail_3141_ = lean_ctor_get(v_mvarIds_3134_, 1);
if (lean_obj_tag(v_tail_3141_) == 0)
{
lean_object* v_head_3142_; lean_object* v___x_3143_; 
lean_dec_ref(v_msg_3135_);
v_head_3142_ = lean_ctor_get(v_mvarIds_3134_, 0);
lean_inc(v_head_3142_);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v_head_3142_);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
return v___x_3144_;
}
}
else
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_);
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3146_, lean_object* v_msg_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Meta_exactlyOne(v_mvarIds_3146_, v_msg_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_mvarIds_3146_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3154_, lean_object* v_msg_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_){
_start:
{
if (lean_obj_tag(v_mvarIds_3154_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec_ref(v_msg_3155_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
else
{
lean_object* v_tail_3163_; 
v_tail_3163_ = lean_ctor_get(v_mvarIds_3154_, 1);
if (lean_obj_tag(v_tail_3163_) == 0)
{
lean_object* v_head_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec_ref(v_msg_3155_);
v_head_3164_ = lean_ctor_get(v_mvarIds_3154_, 0);
lean_inc(v_head_3164_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_head_3164_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
return v___x_3167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3168_, lean_object* v_msg_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3168_, v_msg_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_mvarIds_3168_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3176_, size_t v_sz_3177_, size_t v_i_3178_, lean_object* v_b_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_usize_dec_lt(v_i_3178_, v_sz_3177_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3186_, 0, v_b_3179_);
return v___x_3186_;
}
else
{
lean_object* v_snd_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3217_; 
v_snd_3187_ = lean_ctor_get(v_b_3179_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_b_3179_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v_b_3179_, 0);
lean_dec(v_unused_3218_);
v___x_3189_ = v_b_3179_;
v_isShared_3190_ = v_isSharedCheck_3217_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_snd_3187_);
lean_dec(v_b_3179_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3217_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v_a_3193_; lean_object* v_a_3200_; 
v___x_3191_ = lean_box(0);
v_a_3200_ = lean_array_uget_borrowed(v_as_3176_, v_i_3178_);
if (lean_obj_tag(v_a_3200_) == 0)
{
v_a_3193_ = v_snd_3187_;
goto v___jp_3192_;
}
else
{
lean_object* v_val_3201_; uint8_t v___x_3202_; 
v_val_3201_ = lean_ctor_get(v_a_3200_, 0);
v___x_3202_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = l_Lean_LocalDecl_type(v_val_3201_);
v___x_3204_ = l_Lean_Meta_isProp(v___x_3203_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; uint8_t v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_unbox(v_a_3205_);
lean_dec(v_a_3205_);
if (v___x_3206_ == 0)
{
v_a_3193_ = v_snd_3187_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = l_Lean_LocalDecl_fvarId(v_val_3201_);
v___x_3208_ = lean_array_push(v_snd_3187_, v___x_3207_);
v_a_3193_ = v___x_3208_;
goto v___jp_3192_;
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3189_);
lean_dec(v_snd_3187_);
v_a_3209_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3204_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3204_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
v_a_3193_ = v_snd_3187_;
goto v___jp_3192_;
}
}
v___jp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v_a_3193_);
lean_ctor_set(v___x_3189_, 0, v___x_3191_);
v___x_3195_ = v___x_3189_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_a_3193_);
v___x_3195_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
size_t v___x_3196_; size_t v___x_3197_; 
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = lean_usize_add(v_i_3178_, v___x_3196_);
v_i_3178_ = v___x_3197_;
v_b_3179_ = v___x_3195_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3219_, lean_object* v_sz_3220_, lean_object* v_i_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
size_t v_sz_boxed_3228_; size_t v_i_boxed_3229_; lean_object* v_res_3230_; 
v_sz_boxed_3228_ = lean_unbox_usize(v_sz_3220_);
lean_dec(v_sz_3220_);
v_i_boxed_3229_ = lean_unbox_usize(v_i_3221_);
lean_dec(v_i_3221_);
v_res_3230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3219_, v_sz_boxed_3228_, v_i_boxed_3229_, v_b_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec_ref(v_as_3219_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3231_, size_t v_sz_3232_, size_t v_i_3233_, lean_object* v_b_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_usize_dec_lt(v_i_3233_, v_sz_3232_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v_b_3234_);
return v___x_3241_;
}
else
{
lean_object* v_snd_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3272_; 
v_snd_3242_ = lean_ctor_get(v_b_3234_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_b_3234_);
if (v_isSharedCheck_3272_ == 0)
{
lean_object* v_unused_3273_; 
v_unused_3273_ = lean_ctor_get(v_b_3234_, 0);
lean_dec(v_unused_3273_);
v___x_3244_ = v_b_3234_;
v_isShared_3245_ = v_isSharedCheck_3272_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_snd_3242_);
lean_dec(v_b_3234_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3272_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v_a_3248_; lean_object* v_a_3255_; 
v___x_3246_ = lean_box(0);
v_a_3255_ = lean_array_uget_borrowed(v_as_3231_, v_i_3233_);
if (lean_obj_tag(v_a_3255_) == 0)
{
v_a_3248_ = v_snd_3242_;
goto v___jp_3247_;
}
else
{
lean_object* v_val_3256_; uint8_t v___x_3257_; 
v_val_3256_ = lean_ctor_get(v_a_3255_, 0);
v___x_3257_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3256_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = l_Lean_LocalDecl_type(v_val_3256_);
v___x_3259_ = l_Lean_Meta_isProp(v___x_3258_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
if (v___x_3261_ == 0)
{
v_a_3248_ = v_snd_3242_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = l_Lean_LocalDecl_fvarId(v_val_3256_);
v___x_3263_ = lean_array_push(v_snd_3242_, v___x_3262_);
v_a_3248_ = v___x_3263_;
goto v___jp_3247_;
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_del_object(v___x_3244_);
lean_dec(v_snd_3242_);
v_a_3264_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3259_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3259_);
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
v_a_3248_ = v_snd_3242_;
goto v___jp_3247_;
}
}
v___jp_3247_:
{
lean_object* v___x_3250_; 
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 1, v_a_3248_);
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3250_ = v___x_3244_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_a_3248_);
v___x_3250_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
size_t v___x_3251_; size_t v___x_3252_; lean_object* v___x_3253_; 
v___x_3251_ = ((size_t)1ULL);
v___x_3252_ = lean_usize_add(v_i_3233_, v___x_3251_);
v___x_3253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3231_, v_sz_3232_, v___x_3252_, v___x_3250_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3274_, lean_object* v_sz_3275_, lean_object* v_i_3276_, lean_object* v_b_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
size_t v_sz_boxed_3283_; size_t v_i_boxed_3284_; lean_object* v_res_3285_; 
v_sz_boxed_3283_ = lean_unbox_usize(v_sz_3275_);
lean_dec(v_sz_3275_);
v_i_boxed_3284_ = lean_unbox_usize(v_i_3276_);
lean_dec(v_i_3276_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3274_, v_sz_boxed_3283_, v_i_boxed_3284_, v_b_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_as_3274_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3286_, lean_object* v_n_3287_, lean_object* v_b_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
if (lean_obj_tag(v_n_3287_) == 0)
{
lean_object* v_cs_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3328_; 
v_cs_3294_ = lean_ctor_get(v_n_3287_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_n_3287_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3296_ = v_n_3287_;
v_isShared_3297_ = v_isSharedCheck_3328_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_cs_3294_);
lean_dec(v_n_3287_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3328_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; size_t v_sz_3300_; size_t v___x_3301_; lean_object* v___x_3302_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_ctor_set(v___x_3299_, 1, v_b_3288_);
v_sz_3300_ = lean_array_size(v_cs_3294_);
v___x_3301_ = ((size_t)0ULL);
v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3286_, v_cs_3294_, v_sz_3300_, v___x_3301_, v___x_3299_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec_ref(v_cs_3294_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3319_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3319_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3319_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_fst_3307_; 
v_fst_3307_ = lean_ctor_get(v_a_3303_, 0);
if (lean_obj_tag(v_fst_3307_) == 0)
{
lean_object* v_snd_3308_; lean_object* v___x_3310_; 
v_snd_3308_ = lean_ctor_get(v_a_3303_, 1);
lean_inc(v_snd_3308_);
lean_dec(v_a_3303_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 1);
lean_ctor_set(v___x_3296_, 0, v_snd_3308_);
v___x_3310_ = v___x_3296_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_snd_3308_);
v___x_3310_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3312_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3310_);
v___x_3312_ = v___x_3305_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
lean_object* v_val_3315_; lean_object* v___x_3317_; 
lean_inc_ref(v_fst_3307_);
lean_dec(v_a_3303_);
lean_del_object(v___x_3296_);
v_val_3315_ = lean_ctor_get(v_fst_3307_, 0);
lean_inc(v_val_3315_);
lean_dec_ref(v_fst_3307_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v_val_3315_);
v___x_3317_ = v___x_3305_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_val_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_del_object(v___x_3296_);
v_a_3320_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3302_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3302_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
else
{
lean_object* v_vs_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3363_; 
v_vs_3329_ = lean_ctor_get(v_n_3287_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_n_3287_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3331_ = v_n_3287_;
v_isShared_3332_ = v_isSharedCheck_3363_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_vs_3329_);
lean_dec(v_n_3287_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3363_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; size_t v_sz_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v_b_3288_);
v_sz_3335_ = lean_array_size(v_vs_3329_);
v___x_3336_ = ((size_t)0ULL);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3329_, v_sz_3335_, v___x_3336_, v___x_3334_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec_ref(v_vs_3329_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3354_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3354_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3354_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_fst_3342_; 
v_fst_3342_ = lean_ctor_get(v_a_3338_, 0);
if (lean_obj_tag(v_fst_3342_) == 0)
{
lean_object* v_snd_3343_; lean_object* v___x_3345_; 
v_snd_3343_ = lean_ctor_get(v_a_3338_, 1);
lean_inc(v_snd_3343_);
lean_dec(v_a_3338_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v_snd_3343_);
v___x_3345_ = v___x_3331_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_snd_3343_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v___x_3345_);
v___x_3347_ = v___x_3340_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3352_; 
lean_inc_ref(v_fst_3342_);
lean_dec(v_a_3338_);
lean_del_object(v___x_3331_);
v_val_3350_ = lean_ctor_get(v_fst_3342_, 0);
lean_inc(v_val_3350_);
lean_dec_ref(v_fst_3342_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 0, v_val_3350_);
v___x_3352_ = v___x_3340_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_val_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_del_object(v___x_3331_);
v_a_3355_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3337_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3337_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3364_, lean_object* v_as_3365_, size_t v_sz_3366_, size_t v_i_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_usize_dec_lt(v_i_3367_, v_sz_3366_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_b_3368_);
return v___x_3375_;
}
else
{
lean_object* v_snd_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3410_; 
v_snd_3376_ = lean_ctor_get(v_b_3368_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_b_3368_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v_b_3368_, 0);
lean_dec(v_unused_3411_);
v___x_3378_ = v_b_3368_;
v_isShared_3379_ = v_isSharedCheck_3410_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_snd_3376_);
lean_dec(v_b_3368_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3410_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_a_3380_; lean_object* v___x_3381_; 
v_a_3380_ = lean_array_uget_borrowed(v_as_3365_, v_i_3367_);
lean_inc(v_snd_3376_);
lean_inc(v_a_3380_);
v___x_3381_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3364_, v_a_3380_, v_snd_3376_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3401_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
if (lean_obj_tag(v_a_3382_) == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3382_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3386_);
v___x_3388_ = v___x_3378_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_snd_3376_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3388_);
v___x_3390_ = v___x_3384_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
lean_del_object(v___x_3384_);
lean_dec(v_snd_3376_);
v_a_3393_ = lean_ctor_get(v_a_3382_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v_a_3382_);
v___x_3394_ = lean_box(0);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 1, v_a_3393_);
lean_ctor_set(v___x_3378_, 0, v___x_3394_);
v___x_3396_ = v___x_3378_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_a_3393_);
v___x_3396_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
size_t v___x_3397_; size_t v___x_3398_; 
v___x_3397_ = ((size_t)1ULL);
v___x_3398_ = lean_usize_add(v_i_3367_, v___x_3397_);
v_i_3367_ = v___x_3398_;
v_b_3368_ = v___x_3396_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_del_object(v___x_3378_);
lean_dec(v_snd_3376_);
v_a_3402_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3381_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3381_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3412_, lean_object* v_as_3413_, lean_object* v_sz_3414_, lean_object* v_i_3415_, lean_object* v_b_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
size_t v_sz_boxed_3422_; size_t v_i_boxed_3423_; lean_object* v_res_3424_; 
v_sz_boxed_3422_ = lean_unbox_usize(v_sz_3414_);
lean_dec(v_sz_3414_);
v_i_boxed_3423_ = lean_unbox_usize(v_i_3415_);
lean_dec(v_i_3415_);
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3412_, v_as_3413_, v_sz_boxed_3422_, v_i_boxed_3423_, v_b_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v_as_3413_);
lean_dec_ref(v_init_3412_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3425_, lean_object* v_n_3426_, lean_object* v_b_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3425_, v_n_3426_, v_b_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_init_3425_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3434_, size_t v_sz_3435_, size_t v_i_3436_, lean_object* v_b_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_lt(v_i_3436_, v_sz_3435_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_b_3437_);
return v___x_3444_;
}
else
{
lean_object* v_snd_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3475_; 
v_snd_3445_ = lean_ctor_get(v_b_3437_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_b_3437_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v_b_3437_, 0);
lean_dec(v_unused_3476_);
v___x_3447_ = v_b_3437_;
v_isShared_3448_ = v_isSharedCheck_3475_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_snd_3445_);
lean_dec(v_b_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3475_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_a_3451_; lean_object* v_a_3458_; 
v___x_3449_ = lean_box(0);
v_a_3458_ = lean_array_uget_borrowed(v_as_3434_, v_i_3436_);
if (lean_obj_tag(v_a_3458_) == 0)
{
v_a_3451_ = v_snd_3445_;
goto v___jp_3450_;
}
else
{
lean_object* v_val_3459_; uint8_t v___x_3460_; 
v_val_3459_ = lean_ctor_get(v_a_3458_, 0);
v___x_3460_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3459_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = l_Lean_LocalDecl_type(v_val_3459_);
v___x_3462_ = l_Lean_Meta_isProp(v___x_3461_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; uint8_t v___x_3464_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___x_3462_);
v___x_3464_ = lean_unbox(v_a_3463_);
lean_dec(v_a_3463_);
if (v___x_3464_ == 0)
{
v_a_3451_ = v_snd_3445_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = l_Lean_LocalDecl_fvarId(v_val_3459_);
v___x_3466_ = lean_array_push(v_snd_3445_, v___x_3465_);
v_a_3451_ = v___x_3466_;
goto v___jp_3450_;
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_del_object(v___x_3447_);
lean_dec(v_snd_3445_);
v_a_3467_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3462_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3462_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
v_a_3451_ = v_snd_3445_;
goto v___jp_3450_;
}
}
v___jp_3450_:
{
lean_object* v___x_3453_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v_a_3451_);
lean_ctor_set(v___x_3447_, 0, v___x_3449_);
v___x_3453_ = v___x_3447_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_a_3451_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
size_t v___x_3454_; size_t v___x_3455_; 
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3436_, v___x_3454_);
v_i_3436_ = v___x_3455_;
v_b_3437_ = v___x_3453_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3477_, lean_object* v_sz_3478_, lean_object* v_i_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
size_t v_sz_boxed_3486_; size_t v_i_boxed_3487_; lean_object* v_res_3488_; 
v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3478_);
lean_dec(v_sz_3478_);
v_i_boxed_3487_ = lean_unbox_usize(v_i_3479_);
lean_dec(v_i_3479_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3477_, v_sz_boxed_3486_, v_i_boxed_3487_, v_b_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v_as_3477_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3489_, size_t v_sz_3490_, size_t v_i_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
uint8_t v___x_3498_; 
v___x_3498_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v_b_3492_);
return v___x_3499_;
}
else
{
lean_object* v_snd_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3530_; 
v_snd_3500_ = lean_ctor_get(v_b_3492_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_b_3492_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; 
v_unused_3531_ = lean_ctor_get(v_b_3492_, 0);
lean_dec(v_unused_3531_);
v___x_3502_ = v_b_3492_;
v_isShared_3503_ = v_isSharedCheck_3530_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snd_3500_);
lean_dec(v_b_3492_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3530_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3504_; lean_object* v_a_3506_; lean_object* v_a_3513_; 
v___x_3504_ = lean_box(0);
v_a_3513_ = lean_array_uget_borrowed(v_as_3489_, v_i_3491_);
if (lean_obj_tag(v_a_3513_) == 0)
{
v_a_3506_ = v_snd_3500_;
goto v___jp_3505_;
}
else
{
lean_object* v_val_3514_; uint8_t v___x_3515_; 
v_val_3514_ = lean_ctor_get(v_a_3513_, 0);
v___x_3515_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3514_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = l_Lean_LocalDecl_type(v_val_3514_);
v___x_3517_ = l_Lean_Meta_isProp(v___x_3516_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; uint8_t v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref(v___x_3517_);
v___x_3519_ = lean_unbox(v_a_3518_);
lean_dec(v_a_3518_);
if (v___x_3519_ == 0)
{
v_a_3506_ = v_snd_3500_;
goto v___jp_3505_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = l_Lean_LocalDecl_fvarId(v_val_3514_);
v___x_3521_ = lean_array_push(v_snd_3500_, v___x_3520_);
v_a_3506_ = v___x_3521_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_del_object(v___x_3502_);
lean_dec(v_snd_3500_);
v_a_3522_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3517_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
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
else
{
v_a_3506_ = v_snd_3500_;
goto v___jp_3505_;
}
}
v___jp_3505_:
{
lean_object* v___x_3508_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_a_3506_);
lean_ctor_set(v___x_3502_, 0, v___x_3504_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_a_3506_);
v___x_3508_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
size_t v___x_3509_; size_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = ((size_t)1ULL);
v___x_3510_ = lean_usize_add(v_i_3491_, v___x_3509_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3489_, v_sz_3490_, v___x_3510_, v___x_3508_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3532_, lean_object* v_sz_3533_, lean_object* v_i_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
size_t v_sz_boxed_3541_; size_t v_i_boxed_3542_; lean_object* v_res_3543_; 
v_sz_boxed_3541_ = lean_unbox_usize(v_sz_3533_);
lean_dec(v_sz_3533_);
v_i_boxed_3542_ = lean_unbox_usize(v_i_3534_);
lean_dec(v_i_3534_);
v_res_3543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3532_, v_sz_boxed_3541_, v_i_boxed_3542_, v_b_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v_as_3532_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3544_, lean_object* v_init_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_root_3551_; lean_object* v_tail_3552_; lean_object* v___x_3553_; 
v_root_3551_ = lean_ctor_get(v_t_3544_, 0);
lean_inc_ref(v_root_3551_);
v_tail_3552_ = lean_ctor_get(v_t_3544_, 1);
lean_inc_ref(v_tail_3552_);
lean_dec_ref(v_t_3544_);
lean_inc_ref(v_init_3545_);
v___x_3553_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3545_, v_root_3551_, v_init_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec_ref(v_init_3545_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3590_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3590_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3590_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
if (lean_obj_tag(v_a_3554_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; 
lean_dec_ref(v_tail_3552_);
v_a_3558_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v_a_3554_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 0, v_a_3558_);
v___x_3560_ = v___x_3556_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; size_t v_sz_3565_; size_t v___x_3566_; lean_object* v___x_3567_; 
lean_del_object(v___x_3556_);
v_a_3562_ = lean_ctor_get(v_a_3554_, 0);
lean_inc(v_a_3562_);
lean_dec_ref(v_a_3554_);
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v_a_3562_);
v_sz_3565_ = lean_array_size(v_tail_3552_);
v___x_3566_ = ((size_t)0ULL);
v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3552_, v_sz_3565_, v___x_3566_, v___x_3564_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec_ref(v_tail_3552_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3581_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3581_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3581_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v_fst_3572_; 
v_fst_3572_ = lean_ctor_get(v_a_3568_, 0);
if (lean_obj_tag(v_fst_3572_) == 0)
{
lean_object* v_snd_3573_; lean_object* v___x_3575_; 
v_snd_3573_ = lean_ctor_get(v_a_3568_, 1);
lean_inc(v_snd_3573_);
lean_dec(v_a_3568_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_snd_3573_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_snd_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
else
{
lean_object* v_val_3577_; lean_object* v___x_3579_; 
lean_inc_ref(v_fst_3572_);
lean_dec(v_a_3568_);
v_val_3577_ = lean_ctor_get(v_fst_3572_, 0);
lean_inc(v_val_3577_);
lean_dec_ref(v_fst_3572_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_val_3577_);
v___x_3579_ = v___x_3570_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_val_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
v_a_3582_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3567_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3567_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v_tail_3552_);
v_a_3591_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3553_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3553_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3599_, lean_object* v_init_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3599_, v_init_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_lctx_3612_; lean_object* v_decls_3613_; lean_object* v_result_3614_; lean_object* v___x_3615_; 
v_lctx_3612_ = lean_ctor_get(v_a_3607_, 2);
v_decls_3613_ = lean_ctor_get(v_lctx_3612_, 1);
v_result_3614_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
lean_inc_ref(v_decls_3613_);
v___x_3615_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3613_, v_result_3614_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_Meta_getPropHyps(v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
return v_res_3621_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3626_ = l_Lean_MessageData_ofFormat(v___x_3625_);
return v___x_3626_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3629_, lean_object* v___x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; 
lean_inc(v___x_3630_);
lean_inc(v_mvarId_3629_);
v___x_3636_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3629_, v___x_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v___x_3637_; 
lean_dec_ref(v___x_3636_);
lean_inc(v_mvarId_3629_);
v___x_3637_ = l_Lean_MVarId_getType(v_mvarId_3629_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3637_);
v___x_3639_ = lean_box(0);
v___x_3640_ = l_Lean_Meta_synthInstance(v_a_3638_, v___x_3639_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___x_3640_);
lean_inc(v_mvarId_3629_);
v___x_3642_ = l_Lean_mkMVar(v_mvarId_3629_);
v___x_3643_ = l_Lean_Meta_isExprDefEq(v___x_3642_, v_a_3641_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3655_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3655_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_unbox(v_a_3644_);
lean_dec(v_a_3644_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_del_object(v___x_3646_);
v___x_3649_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3650_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3630_, v_mvarId_3629_, v___x_3649_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
return v___x_3650_;
}
else
{
lean_object* v___x_3651_; lean_object* v___x_3653_; 
lean_dec(v___x_3630_);
lean_dec(v_mvarId_3629_);
v___x_3651_ = lean_box(0);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3651_);
v___x_3653_ = v___x_3646_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v___x_3630_);
lean_dec(v_mvarId_3629_);
v_a_3656_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3643_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3643_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v___x_3630_);
lean_dec(v_mvarId_3629_);
v_a_3664_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3640_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3640_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec(v___x_3630_);
lean_dec(v_mvarId_3629_);
v_a_3672_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3637_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3637_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_dec(v___x_3630_);
lean_dec(v_mvarId_3629_);
return v___x_3636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3680_, lean_object* v___x_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3680_, v___x_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; 
v___x_3697_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3691_);
v___f_3698_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3698_, 0, v_mvarId_3691_);
lean_closure_set(v___f_3698_, 1, v___x_3697_);
v___x_3699_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3691_, v___f_3698_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_MVarId_inferInstance(v_mvarId_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3707_){
_start:
{
switch(lean_obj_tag(v_x_3707_))
{
case 0:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_unsigned_to_nat(0u);
return v___x_3708_;
}
case 1:
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(1u);
return v___x_3709_;
}
default: 
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_unsigned_to_nat(2u);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3711_);
lean_dec(v_x_3711_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3713_, lean_object* v_k_3714_){
_start:
{
if (lean_obj_tag(v_t_3713_) == 2)
{
lean_object* v_mvarId_3715_; lean_object* v___x_3716_; 
v_mvarId_3715_ = lean_ctor_get(v_t_3713_, 0);
lean_inc(v_mvarId_3715_);
lean_dec_ref(v_t_3713_);
v___x_3716_ = lean_apply_1(v_k_3714_, v_mvarId_3715_);
return v___x_3716_;
}
else
{
lean_dec(v_t_3713_);
return v_k_3714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3717_, lean_object* v_ctorIdx_3718_, lean_object* v_t_3719_, lean_object* v_h_3720_, lean_object* v_k_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3719_, v_k_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3723_, lean_object* v_ctorIdx_3724_, lean_object* v_t_3725_, lean_object* v_h_3726_, lean_object* v_k_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3723_, v_ctorIdx_3724_, v_t_3725_, v_h_3726_, v_k_3727_);
lean_dec(v_ctorIdx_3724_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3729_, lean_object* v_closed_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3729_, v_closed_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3732_, lean_object* v_t_3733_, lean_object* v_h_3734_, lean_object* v_closed_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3733_, v_closed_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3737_, lean_object* v_noChange_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3737_, v_noChange_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3740_, lean_object* v_t_3741_, lean_object* v_h_3742_, lean_object* v_noChange_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3741_, v_noChange_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3745_, lean_object* v_modified_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3745_, v_modified_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3748_, lean_object* v_t_3749_, lean_object* v_h_3750_, lean_object* v_modified_3751_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3749_, v_modified_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_){
_start:
{
lean_object* v___y_3763_; uint8_t v___y_3764_; lean_object* v_a_3769_; lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_MVarId_getType(v_g_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_mk_empty_array_with_capacity(v___x_3775_);
v___x_3777_ = lean_array_push(v___x_3776_, v_a_3773_);
v___x_3778_ = l_Lean_Meta_mkAppM(v___x_3774_, v___x_3777_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
v___x_3780_ = lean_box(0);
v___x_3781_ = l_Lean_Meta_synthInstance(v_a_3779_, v___x_3780_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3790_; 
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v___x_3781_, 0);
lean_dec(v_unused_3791_);
v___x_3783_ = v___x_3781_;
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
else
{
lean_dec(v___x_3781_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3790_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
uint8_t v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3785_ = 1;
v___x_3786_ = lean_box(v___x_3785_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3786_);
v___x_3788_ = v___x_3783_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3792_; 
v_a_3792_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3781_);
v_a_3769_ = v_a_3792_;
goto v___jp_3768_;
}
}
else
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3778_);
v_a_3769_ = v_a_3793_;
goto v___jp_3768_;
}
}
else
{
lean_object* v_a_3794_; 
v_a_3794_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3772_);
v_a_3769_ = v_a_3794_;
goto v___jp_3768_;
}
v___jp_3762_:
{
if (v___y_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec_ref(v___y_3763_);
v___x_3765_ = lean_box(v___y_3764_);
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___y_3763_);
return v___x_3767_;
}
}
v___jp_3768_:
{
uint8_t v___x_3770_; 
v___x_3770_ = l_Lean_Exception_isInterrupt(v_a_3769_);
if (v___x_3770_ == 0)
{
uint8_t v___x_3771_; 
lean_inc_ref(v_a_3769_);
v___x_3771_ = l_Lean_Exception_isRuntime(v_a_3769_);
v___y_3763_ = v_a_3769_;
v___y_3764_ = v___x_3771_;
goto v___jp_3762_;
}
else
{
v___y_3763_ = v_a_3769_;
v___y_3764_ = v___x_3770_;
goto v___jp_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_MVarId_isSubsingleton(v_g_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3822_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3819_, v___x_3820_, v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3824_;
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
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
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
