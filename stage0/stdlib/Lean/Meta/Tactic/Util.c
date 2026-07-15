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
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object*, lean_object*);
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
v___x_134_ = l_Lean_Name_eraseMacroScopes(v_suffix_132_);
v___x_135_ = l_Lean_Name_append(v_x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___lam__0___boxed(lean_object* v_suffix_136_, lean_object* v_x_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_appendTag___lam__0(v_suffix_136_, v_x_137_);
lean_dec(v_suffix_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag(lean_object* v_tag_139_, lean_object* v_suffix_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = l_Lean_Name_hasMacroScopes(v_tag_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_tag_139_);
return v___x_142_;
}
else
{
lean_object* v_view_143_; lean_object* v_name_144_; lean_object* v_imported_145_; lean_object* v_ctx_146_; lean_object* v_scopes_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_156_; 
v_view_143_ = l_Lean_extractMacroScopes(v_tag_139_);
v_name_144_ = lean_ctor_get(v_view_143_, 0);
v_imported_145_ = lean_ctor_get(v_view_143_, 1);
v_ctx_146_ = lean_ctor_get(v_view_143_, 2);
v_scopes_147_ = lean_ctor_get(v_view_143_, 3);
v_isSharedCheck_156_ = !lean_is_exclusive(v_view_143_);
if (v_isSharedCheck_156_ == 0)
{
v___x_149_ = v_view_143_;
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_scopes_147_);
lean_inc(v_ctx_146_);
lean_inc(v_imported_145_);
lean_inc(v_name_144_);
lean_dec(v_view_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_156_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = l_Lean_Meta_appendTag___lam__0(v_suffix_140_, v_name_144_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_imported_145_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_ctx_146_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v_scopes_147_);
v___x_153_ = v_reuseFailAlloc_155_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_MacroScopesView_review(v___x_153_);
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTag___boxed(lean_object* v_tag_157_, lean_object* v_suffix_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_appendTag(v_tag_157_, v_suffix_158_);
lean_dec(v_suffix_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix(lean_object* v_mvarId_160_, lean_object* v_suffix_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
lean_inc(v_mvarId_160_);
v___x_167_ = l_Lean_MVarId_getTag(v_mvarId_160_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l_Lean_Meta_appendTag(v_a_168_, v_suffix_161_);
v___x_170_ = l_Lean_MVarId_setTag___redArg(v_mvarId_160_, v___x_169_, v_a_163_);
return v___x_170_;
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v_mvarId_160_);
v_a_171_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_167_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_appendTagSuffix___boxed(lean_object* v_mvarId_179_, lean_object* v_suffix_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_appendTagSuffix(v_mvarId_179_, v_suffix_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_suffix_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object* v_type_187_, lean_object* v_tag_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_type_187_);
v___x_195_ = 2;
v___x_196_ = l_Lean_Meta_mkFreshExprMVar(v___x_194_, v___x_195_, v_tag_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(lean_object* v_type_197_, lean_object* v_tag_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_197_, v_tag_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__0));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__2));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Meta_mkTacticExMsg___closed__5(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_mkTacticExMsg___closed__4));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkTacticExMsg(lean_object* v_tacticName_214_, lean_object* v_mvarId_215_, lean_object* v_msg_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_217_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_218_ = l_Lean_MessageData_ofName(v_tacticName_214_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__3, &l_Lean_Meta_mkTacticExMsg___closed__3_once, _init_l_Lean_Meta_mkTacticExMsg___closed__3);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_msg_216_);
v___x_223_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__5, &l_Lean_Meta_mkTacticExMsg___closed__5_once, _init_l_Lean_Meta_mkTacticExMsg___closed__5);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_mvarId_215_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_env_234_; lean_object* v___x_235_; lean_object* v_mctx_236_; lean_object* v_lctx_237_; lean_object* v_options_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v___x_235_ = lean_st_ref_get(v___y_229_);
v_mctx_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref(v_mctx_236_);
lean_dec(v___x_235_);
v_lctx_237_ = lean_ctor_get(v___y_228_, 2);
v_options_238_ = lean_ctor_get(v___y_230_, 2);
lean_inc_ref(v_options_238_);
lean_inc_ref(v_lctx_237_);
v___x_239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_239_, 0, v_env_234_);
lean_ctor_set(v___x_239_, 1, v_mctx_236_);
lean_ctor_set(v___x_239_, 2, v_lctx_237_);
lean_ctor_set(v___x_239_, 3, v_options_238_);
v___x_240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_msgData_227_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_ref_255_; lean_object* v___x_256_; lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_ref_255_ = lean_ctor_get(v___y_252_, 5);
v___x_256_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
lean_inc(v_ref_255_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_ref_255_);
lean_ctor_set(v___x_261_, 1, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_276_, lean_object* v_mvarId_277_, lean_object* v_msg_x3f_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
if (lean_obj_tag(v_msg_x3f_278_) == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_284_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_285_ = l_Lean_MessageData_ofName(v_tacticName_276_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_mvarId_277_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_290_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_291_;
}
else
{
lean_object* v_val_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_val_292_ = lean_ctor_get(v_msg_x3f_278_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v_msg_x3f_278_, 1);
v___x_293_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_276_, v_mvarId_277_, v_val_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_293_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_295_, lean_object* v_mvarId_296_, lean_object* v_msg_x3f_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_295_, v_mvarId_296_, v_msg_x3f_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_304_, lean_object* v_tacticName_305_, lean_object* v_mvarId_306_, lean_object* v_msg_x3f_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_305_, v_mvarId_306_, v_msg_x3f_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_314_, lean_object* v_tacticName_315_, lean_object* v_mvarId_316_, lean_object* v_msg_x3f_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_314_, v_tacticName_315_, v_mvarId_316_, v_msg_x3f_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_324_, lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_332_, lean_object* v_msg_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_332_, v_msg_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_346_, lean_object* v_ex_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_nestedMsg_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_msg_359_; lean_object* v_kind_360_; uint8_t v___x_361_; 
v_nestedMsg_353_ = l_Lean_Exception_toMessageData(v_ex_347_);
v___x_354_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_355_ = l_Lean_MessageData_ofName(v_tacticName_346_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc_ref(v_nestedMsg_353_);
v_msg_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_359_, 0, v___x_358_);
lean_ctor_set(v_msg_359_, 1, v_nestedMsg_353_);
v_kind_360_ = l_Lean_MessageData_kind(v_nestedMsg_353_);
lean_dec_ref(v_nestedMsg_353_);
v___x_361_ = l_Lean_Name_isAnonymous(v_kind_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_363_ = l_Lean_Name_append(v___x_362_, v_kind_360_);
v___x_364_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_msg_359_);
v___x_365_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_364_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_365_;
}
else
{
lean_object* v___x_366_; 
lean_dec(v_kind_360_);
v___x_366_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_359_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_367_, lean_object* v_ex_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_367_, v_ex_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_375_, lean_object* v_tacticName_376_, lean_object* v_ex_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_376_, v_ex_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_384_, lean_object* v_tacticName_385_, lean_object* v_ex_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_384_, v_tacticName_385_, v_ex_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_393_, lean_object* v_i_394_, lean_object* v_k_395_){
_start:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_array_get_size(v_keys_393_);
v___x_397_ = lean_nat_dec_lt(v_i_394_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_i_394_);
return v___x_397_;
}
else
{
lean_object* v_k_x27_398_; uint8_t v___x_399_; 
v_k_x27_398_ = lean_array_fget_borrowed(v_keys_393_, v_i_394_);
v___x_399_ = l_Lean_instBEqMVarId_beq(v_k_395_, v_k_x27_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_i_394_, v___x_400_);
lean_dec(v_i_394_);
v_i_394_ = v___x_401_;
goto _start;
}
else
{
lean_dec(v_i_394_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_403_, lean_object* v_i_404_, lean_object* v_k_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_403_, v_i_404_, v_k_405_);
lean_dec(v_k_405_);
lean_dec_ref(v_keys_403_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_408_, size_t v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v_es_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_j_415_; lean_object* v___x_416_; 
v_es_411_ = lean_ctor_get(v_x_408_, 0);
v___x_412_ = lean_box(2);
v___x_413_ = ((size_t)31ULL);
v___x_414_ = lean_usize_land(v_x_409_, v___x_413_);
v_j_415_ = lean_usize_to_nat(v___x_414_);
v___x_416_ = lean_array_get_borrowed(v___x_412_, v_es_411_, v_j_415_);
lean_dec(v_j_415_);
switch(lean_obj_tag(v___x_416_))
{
case 0:
{
lean_object* v_key_417_; uint8_t v___x_418_; 
v_key_417_ = lean_ctor_get(v___x_416_, 0);
v___x_418_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_key_417_);
return v___x_418_;
}
case 1:
{
lean_object* v_node_419_; size_t v___x_420_; size_t v___x_421_; 
v_node_419_ = lean_ctor_get(v___x_416_, 0);
v___x_420_ = ((size_t)5ULL);
v___x_421_ = lean_usize_shift_right(v_x_409_, v___x_420_);
v_x_408_ = v_node_419_;
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
size_t v_x_580__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_580__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_427_, v_x_580__boxed_430_, v_x_429_);
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
size_t v_x_747__boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_x_747__boxed_530_ = lean_unbox_usize(v_x_528_);
lean_dec(v_x_528_);
v_res_531_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_526_, v_x_527_, v_x_747__boxed_530_, v_x_529_);
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
lean_dec_ref_known(v___x_628_, 1);
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
lean_dec_ref_known(v___x_630_, 1);
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
lean_object* v_es_802_; size_t v___x_803_; size_t v___x_804_; lean_object* v_j_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_es_802_ = lean_ctor_get(v_x_797_, 0);
v___x_803_ = ((size_t)31ULL);
v___x_804_ = lean_usize_land(v_x_798_, v___x_803_);
v_j_805_ = lean_usize_to_nat(v___x_804_);
v___x_806_ = lean_array_get_size(v_es_802_);
v___x_807_ = lean_nat_dec_lt(v_j_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_dec(v_j_805_);
lean_dec(v_x_801_);
lean_dec(v_x_800_);
return v_x_797_;
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_846_; 
lean_inc_ref(v_es_802_);
v_isSharedCheck_846_ = !lean_is_exclusive(v_x_797_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_x_797_, 0);
lean_dec(v_unused_847_);
v___x_809_ = v_x_797_;
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_846_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_v_811_; lean_object* v___x_812_; lean_object* v_xs_x27_813_; lean_object* v___y_815_; 
v_v_811_ = lean_array_fget(v_es_802_, v_j_805_);
v___x_812_ = lean_box(0);
v_xs_x27_813_ = lean_array_fset(v_es_802_, v_j_805_, v___x_812_);
switch(lean_obj_tag(v_v_811_))
{
case 0:
{
lean_object* v_key_820_; lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_831_; 
v_key_820_ = lean_ctor_get(v_v_811_, 0);
v_val_821_ = lean_ctor_get(v_v_811_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_831_ == 0)
{
v___x_823_ = v_v_811_;
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_inc(v_key_820_);
lean_dec(v_v_811_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_831_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
uint8_t v___x_825_; 
v___x_825_ = l_Lean_instBEqMVarId_beq(v_x_800_, v_key_820_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_823_);
v___x_826_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_820_, v_val_821_, v_x_800_, v_x_801_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___y_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
lean_object* v___x_829_; 
lean_dec(v_val_821_);
lean_dec(v_key_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_x_801_);
lean_ctor_set(v___x_823_, 0, v_x_800_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_x_800_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_x_801_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
v___y_815_ = v___x_829_;
goto v___jp_814_;
}
}
}
}
case 1:
{
lean_object* v_node_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_node_832_ = lean_ctor_get(v_v_811_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_v_811_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_v_811_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_node_832_);
lean_dec(v_v_811_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_836_ = ((size_t)5ULL);
v___x_837_ = lean_usize_shift_right(v_x_798_, v___x_836_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_add(v_x_799_, v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_832_, v___x_837_, v___x_839_, v_x_800_, v_x_801_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_840_);
v___x_842_ = v___x_834_;
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
v___y_815_ = v___x_842_;
goto v___jp_814_;
}
}
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_x_800_);
lean_ctor_set(v___x_845_, 1, v_x_801_);
v___y_815_ = v___x_845_;
goto v___jp_814_;
}
}
v___jp_814_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_array_fset(v_xs_x27_813_, v_j_805_, v___y_815_);
lean_dec(v_j_805_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_816_);
v___x_818_ = v___x_809_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
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
size_t v_x_1007__boxed_902_; size_t v_x_1008__boxed_903_; lean_object* v_res_904_; 
v_x_1007__boxed_902_ = lean_unbox_usize(v_x_898_);
lean_dec(v_x_898_);
v_x_1008__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_res_904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_897_, v_x_1007__boxed_902_, v_x_1008__boxed_903_, v_x_900_, v_x_901_);
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
lean_dec_ref_known(v___x_963_, 1);
lean_inc(v_mvarId_955_);
v___x_964_ = l_Lean_MVarId_getType(v_mvarId_955_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v___x_964_, 1);
v___x_966_ = 1;
v___x_967_ = l_Lean_Meta_mkLabeledSorry(v_a_965_, v_synthetic_957_, v___x_966_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
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
size_t v_x_1332__boxed_1053_; size_t v_x_1333__boxed_1054_; lean_object* v_res_1055_; 
v_x_1332__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_x_1333__boxed_1054_ = lean_unbox_usize(v_x_1050_);
lean_dec(v_x_1050_);
v_res_1055_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1047_, v_x_1048_, v_x_1332__boxed_1053_, v_x_1333__boxed_1054_, v_x_1051_, v_x_1052_);
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
lean_dec_ref_known(v___x_1090_, 1);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v_visited_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; size_t v___x_1221_; uint8_t v___x_1222_; 
v___x_1215_ = lean_st_ref_get(v_a_1213_);
v_visited_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_ref(v_visited_1216_);
lean_dec(v___x_1215_);
v___x_1217_ = lean_ptr_addr(v_e_1212_);
v___x_1218_ = ((size_t)8191ULL);
v___x_1219_ = lean_usize_mod(v___x_1217_, v___x_1218_);
v___x_1220_ = lean_array_uget(v_visited_1216_, v___x_1219_);
lean_dec_ref(v_visited_1216_);
v___x_1221_ = lean_ptr_addr(v___x_1220_);
lean_dec(v___x_1220_);
v___x_1222_ = lean_usize_dec_eq(v___x_1221_, v___x_1217_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v_visited_1224_; lean_object* v_checked_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v___x_1223_ = lean_st_ref_take(v_a_1213_);
v_visited_1224_ = lean_ctor_get(v___x_1223_, 0);
v_checked_1225_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v___x_1223_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_checked_1225_);
lean_inc(v_visited_1224_);
lean_dec(v___x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_array_uset(v_visited_1224_, v___x_1219_, v_e_1212_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_checked_1225_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_st_ref_set(v_a_1213_, v___x_1231_);
v___x_1233_ = lean_box(v___x_1222_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v_e_1212_);
v___x_1237_ = lean_box(v___x_1222_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1239_, v_a_1240_);
lean_dec(v_a_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1243_, lean_object* v_x_1244_){
_start:
{
if (lean_obj_tag(v_x_1244_) == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
lean_object* v_key_1246_; lean_object* v_tail_1247_; uint8_t v___x_1248_; 
v_key_1246_ = lean_ctor_get(v_x_1244_, 0);
v_tail_1247_ = lean_ctor_get(v_x_1244_, 2);
v___x_1248_ = lean_expr_eqv(v_key_1246_, v_a_1243_);
if (v___x_1248_ == 0)
{
v_x_1244_ = v_tail_1247_;
goto _start;
}
else
{
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1250_, lean_object* v_x_1251_){
_start:
{
uint8_t v_res_1252_; lean_object* v_r_1253_; 
v_res_1252_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1250_, v_x_1251_);
lean_dec(v_x_1251_);
lean_dec_ref(v_a_1250_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
if (lean_obj_tag(v_x_1255_) == 0)
{
return v_x_1254_;
}
else
{
lean_object* v_key_1256_; lean_object* v_value_1257_; lean_object* v_tail_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1281_; 
v_key_1256_ = lean_ctor_get(v_x_1255_, 0);
v_value_1257_ = lean_ctor_get(v_x_1255_, 1);
v_tail_1258_ = lean_ctor_get(v_x_1255_, 2);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1260_ = v_x_1255_;
v_isShared_1261_ = v_isSharedCheck_1281_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_tail_1258_);
lean_inc(v_value_1257_);
lean_inc(v_key_1256_);
lean_dec(v_x_1255_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1281_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; uint64_t v_fold_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1262_ = lean_array_get_size(v_x_1254_);
v___x_1263_ = l_Lean_Expr_hash(v_key_1256_);
v___x_1264_ = 32ULL;
v___x_1265_ = lean_uint64_shift_right(v___x_1263_, v___x_1264_);
v_fold_1266_ = lean_uint64_xor(v___x_1263_, v___x_1265_);
v___x_1267_ = 16ULL;
v___x_1268_ = lean_uint64_shift_right(v_fold_1266_, v___x_1267_);
v___x_1269_ = lean_uint64_xor(v_fold_1266_, v___x_1268_);
v___x_1270_ = lean_uint64_to_usize(v___x_1269_);
v___x_1271_ = lean_usize_of_nat(v___x_1262_);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_sub(v___x_1271_, v___x_1272_);
v___x_1274_ = lean_usize_land(v___x_1270_, v___x_1273_);
v___x_1275_ = lean_array_uget_borrowed(v_x_1254_, v___x_1274_);
lean_inc(v___x_1275_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 2, v___x_1275_);
v___x_1277_ = v___x_1260_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_key_1256_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_value_1257_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_array_uset(v_x_1254_, v___x_1274_, v___x_1277_);
v_x_1254_ = v___x_1278_;
v_x_1255_ = v_tail_1258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1282_, lean_object* v_source_1283_, lean_object* v_target_1284_){
_start:
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = lean_array_get_size(v_source_1283_);
v___x_1286_ = lean_nat_dec_lt(v_i_1282_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v_source_1283_);
lean_dec(v_i_1282_);
return v_target_1284_;
}
else
{
lean_object* v_es_1287_; lean_object* v___x_1288_; lean_object* v_source_1289_; lean_object* v_target_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_es_1287_ = lean_array_fget(v_source_1283_, v_i_1282_);
v___x_1288_ = lean_box(0);
v_source_1289_ = lean_array_fset(v_source_1283_, v_i_1282_, v___x_1288_);
v_target_1290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1284_, v_es_1287_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_add(v_i_1282_, v___x_1291_);
lean_dec(v_i_1282_);
v_i_1282_ = v___x_1292_;
v_source_1283_ = v_source_1289_;
v_target_1284_ = v_target_1290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_nbuckets_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1295_ = lean_array_get_size(v_data_1294_);
v___x_1296_ = lean_unsigned_to_nat(2u);
v_nbuckets_1297_ = lean_nat_mul(v___x_1295_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_mk_array(v_nbuckets_1297_, v___x_1299_);
v___x_1301_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1298_, v_data_1294_, v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1302_, lean_object* v_a_1303_, lean_object* v_b_1304_){
_start:
{
lean_object* v_size_1305_; lean_object* v_buckets_1306_; lean_object* v___x_1307_; uint64_t v___x_1308_; uint64_t v___x_1309_; uint64_t v___x_1310_; uint64_t v_fold_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; size_t v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; size_t v___x_1318_; size_t v___x_1319_; lean_object* v_bkt_1320_; uint8_t v___x_1321_; 
v_size_1305_ = lean_ctor_get(v_m_1302_, 0);
v_buckets_1306_ = lean_ctor_get(v_m_1302_, 1);
v___x_1307_ = lean_array_get_size(v_buckets_1306_);
v___x_1308_ = l_Lean_Expr_hash(v_a_1303_);
v___x_1309_ = 32ULL;
v___x_1310_ = lean_uint64_shift_right(v___x_1308_, v___x_1309_);
v_fold_1311_ = lean_uint64_xor(v___x_1308_, v___x_1310_);
v___x_1312_ = 16ULL;
v___x_1313_ = lean_uint64_shift_right(v_fold_1311_, v___x_1312_);
v___x_1314_ = lean_uint64_xor(v_fold_1311_, v___x_1313_);
v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = lean_usize_of_nat(v___x_1307_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_sub(v___x_1316_, v___x_1317_);
v___x_1319_ = lean_usize_land(v___x_1315_, v___x_1318_);
v_bkt_1320_ = lean_array_uget_borrowed(v_buckets_1306_, v___x_1319_);
v___x_1321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1303_, v_bkt_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1342_; 
lean_inc_ref(v_buckets_1306_);
lean_inc(v_size_1305_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_m_1302_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1343_ = lean_ctor_get(v_m_1302_, 1);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_m_1302_, 0);
lean_dec(v_unused_1344_);
v___x_1323_ = v_m_1302_;
v_isShared_1324_ = v_isSharedCheck_1342_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_m_1302_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1342_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v_size_x27_1326_; lean_object* v___x_1327_; lean_object* v_buckets_x27_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1325_ = lean_unsigned_to_nat(1u);
v_size_x27_1326_ = lean_nat_add(v_size_1305_, v___x_1325_);
lean_dec(v_size_1305_);
lean_inc(v_bkt_1320_);
v___x_1327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1327_, 0, v_a_1303_);
lean_ctor_set(v___x_1327_, 1, v_b_1304_);
lean_ctor_set(v___x_1327_, 2, v_bkt_1320_);
v_buckets_x27_1328_ = lean_array_uset(v_buckets_1306_, v___x_1319_, v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(4u);
v___x_1330_ = lean_nat_mul(v_size_x27_1326_, v___x_1329_);
v___x_1331_ = lean_unsigned_to_nat(3u);
v___x_1332_ = lean_nat_div(v___x_1330_, v___x_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_array_get_size(v_buckets_x27_1328_);
v___x_1334_ = lean_nat_dec_le(v___x_1332_, v___x_1333_);
lean_dec(v___x_1332_);
if (v___x_1334_ == 0)
{
lean_object* v_val_1335_; lean_object* v___x_1337_; 
v_val_1335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1328_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v_val_1335_);
lean_ctor_set(v___x_1323_, 0, v_size_x27_1326_);
v___x_1337_ = v___x_1323_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_size_x27_1326_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_val_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
else
{
lean_object* v___x_1340_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v_buckets_x27_1328_);
lean_ctor_set(v___x_1323_, 0, v_size_x27_1326_);
v___x_1340_ = v___x_1323_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_size_x27_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_buckets_x27_1328_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_dec(v_b_1304_);
lean_dec_ref(v_a_1303_);
return v_m_1302_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_buckets_1347_; lean_object* v___x_1348_; uint64_t v___x_1349_; uint64_t v___x_1350_; uint64_t v___x_1351_; uint64_t v_fold_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_buckets_1347_ = lean_ctor_get(v_m_1345_, 1);
v___x_1348_ = lean_array_get_size(v_buckets_1347_);
v___x_1349_ = l_Lean_Expr_hash(v_a_1346_);
v___x_1350_ = 32ULL;
v___x_1351_ = lean_uint64_shift_right(v___x_1349_, v___x_1350_);
v_fold_1352_ = lean_uint64_xor(v___x_1349_, v___x_1351_);
v___x_1353_ = 16ULL;
v___x_1354_ = lean_uint64_shift_right(v_fold_1352_, v___x_1353_);
v___x_1355_ = lean_uint64_xor(v_fold_1352_, v___x_1354_);
v___x_1356_ = lean_uint64_to_usize(v___x_1355_);
v___x_1357_ = lean_usize_of_nat(v___x_1348_);
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_sub(v___x_1357_, v___x_1358_);
v___x_1360_ = lean_usize_land(v___x_1356_, v___x_1359_);
v___x_1361_ = lean_array_uget_borrowed(v_buckets_1347_, v___x_1360_);
v___x_1362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1346_, v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1363_, lean_object* v_a_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1363_, v_a_1364_);
lean_dec_ref(v_a_1364_);
lean_dec_ref(v_m_1363_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_checked_1371_; uint8_t v___x_1372_; 
v___x_1370_ = lean_st_ref_get(v_a_1368_);
v_checked_1371_ = lean_ctor_get(v___x_1370_, 1);
lean_inc_ref(v_checked_1371_);
lean_dec(v___x_1370_);
v___x_1372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1371_, v_e_1367_);
lean_dec_ref(v_checked_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v_visited_1374_; lean_object* v_checked_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1387_; 
v___x_1373_ = lean_st_ref_take(v_a_1368_);
v_visited_1374_ = lean_ctor_get(v___x_1373_, 0);
v_checked_1375_ = lean_ctor_get(v___x_1373_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1377_ = v___x_1373_;
v_isShared_1378_ = v_isSharedCheck_1387_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_checked_1375_);
lean_inc(v_visited_1374_);
lean_dec(v___x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1387_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1375_, v_e_1367_, v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_visited_1374_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = lean_st_ref_set(v_a_1368_, v___x_1382_);
v___x_1384_ = lean_box(v___x_1372_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_e_1367_);
v___x_1388_ = lean_box(v___x_1372_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1390_, lean_object* v_a_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1390_, v_a_1391_);
lean_dec(v_a_1391_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1394_, lean_object* v_f_1395_, uint8_t v_stopWhenVisited_1396_, lean_object* v_e_1397_, lean_object* v_a_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v_d_1411_; lean_object* v_b_1412_; lean_object* v___y_1413_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___x_1443_; 
lean_inc_ref(v_e_1397_);
v___x_1443_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1397_, v_a_1398_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1476_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1476_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1476_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_unbox(v_a_1444_);
lean_dec(v_a_1444_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; uint8_t v___x_1450_; 
lean_del_object(v___x_1446_);
lean_inc_ref(v_p_1394_);
lean_inc_ref(v_e_1397_);
v___x_1449_ = lean_apply_1(v_p_1394_, v_e_1397_);
v___x_1450_ = lean_unbox(v___x_1449_);
if (v___x_1450_ == 0)
{
v___y_1417_ = v_a_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1451_; 
lean_inc_ref(v_e_1397_);
v___x_1451_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1397_, v_a_1398_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; uint8_t v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = lean_unbox(v_a_1452_);
lean_dec(v_a_1452_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_inc_ref(v_f_1395_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc_ref(v_e_1397_);
v___x_1454_ = lean_apply_7(v_f_1395_, v_e_1397_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, lean_box(0));
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1454_, 0);
lean_dec(v_unused_1463_);
v___x_1456_ = v___x_1454_;
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v___x_1454_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1462_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
if (v_stopWhenVisited_1396_ == 0)
{
lean_del_object(v___x_1456_);
v___y_1417_ = v_a_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
v___x_1458_ = lean_box(0);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
return v___x_1454_;
}
}
else
{
v___y_1417_ = v_a_1398_;
v___y_1418_ = v___y_1399_;
v___y_1419_ = v___y_1400_;
v___y_1420_ = v___y_1401_;
v___y_1421_ = v___y_1402_;
v___y_1422_ = v___y_1403_;
goto v___jp_1416_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
v_a_1464_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1451_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1451_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
v___x_1472_ = lean_box(0);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1472_);
v___x_1474_ = v___x_1446_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
v_a_1477_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1443_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1443_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
v___jp_1405_:
{
lean_object* v___x_1414_; 
lean_inc_ref(v_f_1395_);
lean_inc_ref(v_p_1394_);
v___x_1414_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1394_, v_f_1395_, v_stopWhenVisited_1396_, v_d_1411_, v___y_1413_, v___y_1407_, v___y_1409_, v___y_1410_, v___y_1408_, v___y_1406_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_dec_ref_known(v___x_1414_, 1);
v_e_1397_ = v_b_1412_;
v_a_1398_ = v___y_1413_;
v___y_1399_ = v___y_1407_;
v___y_1400_ = v___y_1409_;
v___y_1401_ = v___y_1410_;
v___y_1402_ = v___y_1408_;
v___y_1403_ = v___y_1406_;
goto _start;
}
else
{
lean_dec_ref(v_b_1412_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
return v___x_1414_;
}
}
v___jp_1416_:
{
switch(lean_obj_tag(v_e_1397_))
{
case 7:
{
lean_object* v_binderType_1423_; lean_object* v_body_1424_; 
v_binderType_1423_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_binderType_1423_);
v_body_1424_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_body_1424_);
lean_dec_ref_known(v_e_1397_, 3);
v___y_1406_ = v___y_1422_;
v___y_1407_ = v___y_1418_;
v___y_1408_ = v___y_1421_;
v___y_1409_ = v___y_1419_;
v___y_1410_ = v___y_1420_;
v_d_1411_ = v_binderType_1423_;
v_b_1412_ = v_body_1424_;
v___y_1413_ = v___y_1417_;
goto v___jp_1405_;
}
case 6:
{
lean_object* v_binderType_1425_; lean_object* v_body_1426_; 
v_binderType_1425_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_binderType_1425_);
v_body_1426_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_body_1426_);
lean_dec_ref_known(v_e_1397_, 3);
v___y_1406_ = v___y_1422_;
v___y_1407_ = v___y_1418_;
v___y_1408_ = v___y_1421_;
v___y_1409_ = v___y_1419_;
v___y_1410_ = v___y_1420_;
v_d_1411_ = v_binderType_1425_;
v_b_1412_ = v_body_1426_;
v___y_1413_ = v___y_1417_;
goto v___jp_1405_;
}
case 8:
{
lean_object* v_type_1427_; lean_object* v_value_1428_; lean_object* v_body_1429_; lean_object* v___x_1430_; 
v_type_1427_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_type_1427_);
v_value_1428_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_value_1428_);
v_body_1429_ = lean_ctor_get(v_e_1397_, 3);
lean_inc_ref(v_body_1429_);
lean_dec_ref_known(v_e_1397_, 4);
lean_inc_ref(v_f_1395_);
lean_inc_ref(v_p_1394_);
v___x_1430_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1394_, v_f_1395_, v_stopWhenVisited_1396_, v_type_1427_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref_known(v___x_1430_, 1);
lean_inc_ref(v_f_1395_);
lean_inc_ref(v_p_1394_);
v___x_1431_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1394_, v_f_1395_, v_stopWhenVisited_1396_, v_value_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_dec_ref_known(v___x_1431_, 1);
v_e_1397_ = v_body_1429_;
v_a_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
goto _start;
}
else
{
lean_dec_ref(v_body_1429_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
return v___x_1431_;
}
}
else
{
lean_dec_ref(v_body_1429_);
lean_dec_ref(v_value_1428_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
return v___x_1430_;
}
}
case 5:
{
lean_object* v_fn_1433_; lean_object* v_arg_1434_; lean_object* v___x_1435_; 
v_fn_1433_ = lean_ctor_get(v_e_1397_, 0);
lean_inc_ref(v_fn_1433_);
v_arg_1434_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_arg_1434_);
lean_dec_ref_known(v_e_1397_, 2);
lean_inc_ref(v_f_1395_);
lean_inc_ref(v_p_1394_);
v___x_1435_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1394_, v_f_1395_, v_stopWhenVisited_1396_, v_fn_1433_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v_e_1397_ = v_arg_1434_;
v_a_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1434_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
return v___x_1435_;
}
}
case 10:
{
lean_object* v_expr_1437_; 
v_expr_1437_ = lean_ctor_get(v_e_1397_, 1);
lean_inc_ref(v_expr_1437_);
lean_dec_ref_known(v_e_1397_, 2);
v_e_1397_ = v_expr_1437_;
v_a_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
goto _start;
}
case 11:
{
lean_object* v_struct_1439_; 
v_struct_1439_ = lean_ctor_get(v_e_1397_, 2);
lean_inc_ref(v_struct_1439_);
lean_dec_ref_known(v_e_1397_, 3);
v_e_1397_ = v_struct_1439_;
v_a_1398_ = v___y_1417_;
v___y_1399_ = v___y_1418_;
v___y_1400_ = v___y_1419_;
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
goto _start;
}
default: 
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v_e_1397_);
lean_dec_ref(v_f_1395_);
lean_dec_ref(v_p_1394_);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1485_, lean_object* v_f_1486_, lean_object* v_stopWhenVisited_1487_, lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1496_; lean_object* v_res_1497_; 
v_stopWhenVisited_boxed_1496_ = lean_unbox(v_stopWhenVisited_1487_);
v_res_1497_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1485_, v_f_1486_, v_stopWhenVisited_boxed_1496_, v_e_1488_, v_a_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v_a_1489_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1498_, lean_object* v_f_1499_, lean_object* v_e_1500_, uint8_t v_stopWhenVisited_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = l_Lean_ForEachExprWhere_initCache;
v___x_1509_ = lean_st_mk_ref(v___x_1508_);
v___x_1510_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1498_, v_f_1499_, v_stopWhenVisited_1501_, v_e_1500_, v___x_1509_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1519_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1519_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1515_ = lean_st_ref_get(v___x_1509_);
lean_dec(v___x_1509_);
lean_dec(v___x_1515_);
if (v_isShared_1514_ == 0)
{
v___x_1517_ = v___x_1513_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1511_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_dec(v___x_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1520_, lean_object* v_f_1521_, lean_object* v_e_1522_, lean_object* v_stopWhenVisited_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1530_; lean_object* v_res_1531_; 
v_stopWhenVisited_boxed_1530_ = lean_unbox(v_stopWhenVisited_1523_);
v_res_1531_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1520_, v_f_1521_, v_e_1522_, v_stopWhenVisited_boxed_1530_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1533_, lean_object* v___f_1534_, uint8_t v___x_1535_, lean_object* v_e_1536_, lean_object* v_candidates_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1536_, v___y_1539_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___y_1547_; uint8_t v___x_1557_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = lean_st_mk_ref(v_candidates_1537_);
v___x_1557_ = l_Lean_Expr_hasFVar(v_a_1544_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec(v_a_1544_);
lean_dec_ref(v___f_1534_);
v___x_1558_ = lean_box(0);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___x_1545_);
v___x_1559_ = lean_apply_7(v___f_1533_, v___x_1558_, v___x_1545_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
v___y_1547_ = v___x_1559_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1561_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1560_, v___f_1534_, v_a_1544_, v___x_1535_, v___x_1545_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
lean_inc(v___x_1545_);
v___x_1563_ = lean_apply_7(v___f_1533_, v_a_1562_, v___x_1545_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, lean_box(0));
v___y_1547_ = v___x_1563_;
goto v___jp_1546_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v___x_1545_);
lean_dec_ref(v___f_1533_);
v_a_1564_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1561_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1561_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
v___jp_1546_:
{
if (lean_obj_tag(v___y_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
v_a_1548_ = lean_ctor_get(v___y_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___y_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1550_ = v___y_1547_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___y_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_st_ref_get(v___x_1545_);
lean_dec(v___x_1545_);
lean_dec(v___x_1552_);
if (v_isShared_1551_ == 0)
{
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1548_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_dec(v___x_1545_);
return v___y_1547_;
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v_candidates_1537_);
lean_dec_ref(v___f_1534_);
lean_dec_ref(v___f_1533_);
v_a_1572_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1543_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1543_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1580_, lean_object* v___f_1581_, lean_object* v___x_1582_, lean_object* v_e_1583_, lean_object* v_candidates_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___x_17576__boxed_1590_; lean_object* v_res_1591_; 
v___x_17576__boxed_1590_ = lean_unbox(v___x_1582_);
v_res_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1580_, v___f_1581_, v___x_17576__boxed_1590_, v_e_1583_, v_candidates_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_e_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = lean_st_ref_take(v___y_1593_);
v___x_1600_ = l_Lean_Expr_fvarId_x21(v_e_1592_);
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1599_, v___x_1600_);
lean_dec(v___x_1600_);
v___x_1602_ = lean_st_ref_set(v___y_1593_, v___x_1601_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_e_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v_e_1605_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_____r_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_st_ref_get(v___y_1614_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_____r_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
if (lean_obj_tag(v_x_1631_) == 0)
{
return v_x_1630_;
}
else
{
lean_object* v_key_1632_; lean_object* v_value_1633_; lean_object* v_tail_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1657_; 
v_key_1632_ = lean_ctor_get(v_x_1631_, 0);
v_value_1633_ = lean_ctor_get(v_x_1631_, 1);
v_tail_1634_ = lean_ctor_get(v_x_1631_, 2);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1631_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1636_ = v_x_1631_;
v_isShared_1637_ = v_isSharedCheck_1657_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_tail_1634_);
lean_inc(v_value_1633_);
lean_inc(v_key_1632_);
lean_dec(v_x_1631_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1657_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v_fold_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1638_ = lean_array_get_size(v_x_1630_);
v___x_1639_ = l_Lean_instHashableFVarId_hash(v_key_1632_);
v___x_1640_ = 32ULL;
v___x_1641_ = lean_uint64_shift_right(v___x_1639_, v___x_1640_);
v_fold_1642_ = lean_uint64_xor(v___x_1639_, v___x_1641_);
v___x_1643_ = 16ULL;
v___x_1644_ = lean_uint64_shift_right(v_fold_1642_, v___x_1643_);
v___x_1645_ = lean_uint64_xor(v_fold_1642_, v___x_1644_);
v___x_1646_ = lean_uint64_to_usize(v___x_1645_);
v___x_1647_ = lean_usize_of_nat(v___x_1638_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_sub(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_usize_land(v___x_1646_, v___x_1649_);
v___x_1651_ = lean_array_uget_borrowed(v_x_1630_, v___x_1650_);
lean_inc(v___x_1651_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 2, v___x_1651_);
v___x_1653_ = v___x_1636_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_key_1632_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_value_1633_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_uset(v_x_1630_, v___x_1650_, v___x_1653_);
v_x_1630_ = v___x_1654_;
v_x_1631_ = v_tail_1634_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1658_, lean_object* v_source_1659_, lean_object* v_target_1660_){
_start:
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = lean_array_get_size(v_source_1659_);
v___x_1662_ = lean_nat_dec_lt(v_i_1658_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_source_1659_);
lean_dec(v_i_1658_);
return v_target_1660_;
}
else
{
lean_object* v_es_1663_; lean_object* v___x_1664_; lean_object* v_source_1665_; lean_object* v_target_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_es_1663_ = lean_array_fget(v_source_1659_, v_i_1658_);
v___x_1664_ = lean_box(0);
v_source_1665_ = lean_array_fset(v_source_1659_, v_i_1658_, v___x_1664_);
v_target_1666_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1660_, v_es_1663_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v_i_1658_, v___x_1667_);
lean_dec(v_i_1658_);
v_i_1658_ = v___x_1668_;
v_source_1659_ = v_source_1665_;
v_target_1660_ = v_target_1666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_nbuckets_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1671_ = lean_array_get_size(v_data_1670_);
v___x_1672_ = lean_unsigned_to_nat(2u);
v_nbuckets_1673_ = lean_nat_mul(v___x_1671_, v___x_1672_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_mk_array(v_nbuckets_1673_, v___x_1675_);
v___x_1677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1674_, v_data_1670_, v___x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1678_, lean_object* v_a_1679_, lean_object* v_b_1680_){
_start:
{
lean_object* v_size_1681_; lean_object* v_buckets_1682_; lean_object* v___x_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint64_t v_fold_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; size_t v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; lean_object* v_bkt_1696_; uint8_t v___x_1697_; 
v_size_1681_ = lean_ctor_get(v_m_1678_, 0);
v_buckets_1682_ = lean_ctor_get(v_m_1678_, 1);
v___x_1683_ = lean_array_get_size(v_buckets_1682_);
v___x_1684_ = l_Lean_instHashableFVarId_hash(v_a_1679_);
v___x_1685_ = 32ULL;
v___x_1686_ = lean_uint64_shift_right(v___x_1684_, v___x_1685_);
v_fold_1687_ = lean_uint64_xor(v___x_1684_, v___x_1686_);
v___x_1688_ = 16ULL;
v___x_1689_ = lean_uint64_shift_right(v_fold_1687_, v___x_1688_);
v___x_1690_ = lean_uint64_xor(v_fold_1687_, v___x_1689_);
v___x_1691_ = lean_uint64_to_usize(v___x_1690_);
v___x_1692_ = lean_usize_of_nat(v___x_1683_);
v___x_1693_ = ((size_t)1ULL);
v___x_1694_ = lean_usize_sub(v___x_1692_, v___x_1693_);
v___x_1695_ = lean_usize_land(v___x_1691_, v___x_1694_);
v_bkt_1696_ = lean_array_uget_borrowed(v_buckets_1682_, v___x_1695_);
v___x_1697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1679_, v_bkt_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1718_; 
lean_inc_ref(v_buckets_1682_);
lean_inc(v_size_1681_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_m_1678_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; 
v_unused_1719_ = lean_ctor_get(v_m_1678_, 1);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_m_1678_, 0);
lean_dec(v_unused_1720_);
v___x_1699_ = v_m_1678_;
v_isShared_1700_ = v_isSharedCheck_1718_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_m_1678_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1718_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v_size_x27_1702_; lean_object* v___x_1703_; lean_object* v_buckets_x27_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v_size_x27_1702_ = lean_nat_add(v_size_1681_, v___x_1701_);
lean_dec(v_size_1681_);
lean_inc(v_bkt_1696_);
v___x_1703_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1679_);
lean_ctor_set(v___x_1703_, 1, v_b_1680_);
lean_ctor_set(v___x_1703_, 2, v_bkt_1696_);
v_buckets_x27_1704_ = lean_array_uset(v_buckets_1682_, v___x_1695_, v___x_1703_);
v___x_1705_ = lean_unsigned_to_nat(4u);
v___x_1706_ = lean_nat_mul(v_size_x27_1702_, v___x_1705_);
v___x_1707_ = lean_unsigned_to_nat(3u);
v___x_1708_ = lean_nat_div(v___x_1706_, v___x_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_array_get_size(v_buckets_x27_1704_);
v___x_1710_ = lean_nat_dec_le(v___x_1708_, v___x_1709_);
lean_dec(v___x_1708_);
if (v___x_1710_ == 0)
{
lean_object* v_val_1711_; lean_object* v___x_1713_; 
v_val_1711_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1704_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v_val_1711_);
lean_ctor_set(v___x_1699_, 0, v_size_x27_1702_);
v___x_1713_ = v___x_1699_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_size_x27_1702_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_val_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v___x_1716_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v_buckets_x27_1704_);
lean_ctor_set(v___x_1699_, 0, v_size_x27_1702_);
v___x_1716_ = v___x_1699_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_size_x27_1702_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_buckets_x27_1704_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_dec(v_b_1680_);
lean_dec(v_a_1679_);
return v_m_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1723_, size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_b_1726_);
return v___x_1733_;
}
else
{
lean_object* v_snd_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1798_; 
v_snd_1734_ = lean_ctor_get(v_b_1726_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_b_1726_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_b_1726_, 0);
lean_dec(v_unused_1799_);
v___x_1736_ = v_b_1726_;
v_isShared_1737_ = v_isSharedCheck_1798_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snd_1734_);
lean_dec(v_b_1726_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1798_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v_a_1740_; lean_object* v_a_1747_; 
v___x_1738_ = lean_box(0);
v_a_1747_ = lean_array_uget_borrowed(v_as_1723_, v_i_1725_);
if (lean_obj_tag(v_a_1747_) == 0)
{
v_a_1740_ = v_snd_1734_;
goto v___jp_1739_;
}
else
{
lean_object* v_val_1748_; lean_object* v___y_1750_; uint8_t v___x_1754_; 
v_val_1748_ = lean_ctor_get(v_a_1747_, 0);
v___x_1754_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1748_);
if (v___x_1754_ == 0)
{
lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v_candidates_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___x_1776_; 
v___f_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1757_ = l_Lean_LocalDecl_type(v_val_1748_);
lean_inc_ref(v___x_1757_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1756_, v___f_1755_, v___x_1754_, v___x_1757_, v_snd_1734_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Lean_LocalDecl_value_x3f(v_val_1748_, v___x_1754_);
if (lean_obj_tag(v___x_1778_) == 0)
{
v_candidates_1759_ = v_a_1777_;
v___y_1760_ = v___y_1727_;
v___y_1761_ = v___y_1728_;
v___y_1762_ = v___y_1729_;
v___y_1763_ = v___y_1730_;
goto v___jp_1758_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1780_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1756_, v___f_1755_, v___x_1754_, v_val_1779_, v_a_1777_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v_candidates_1759_ = v_a_1781_;
v___y_1760_ = v___y_1727_;
v___y_1761_ = v___y_1728_;
v___y_1762_ = v___y_1729_;
v___y_1763_ = v___y_1730_;
goto v___jp_1758_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___x_1757_);
lean_del_object(v___x_1736_);
v_a_1782_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___x_1757_);
lean_del_object(v___x_1736_);
v_a_1790_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1776_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1776_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Meta_isProp(v___x_1757_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; uint8_t v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_unbox(v_a_1765_);
lean_dec(v_a_1765_);
if (v___x_1766_ == 0)
{
v_a_1740_ = v_candidates_1759_;
goto v___jp_1739_;
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Lean_LocalDecl_hasValue(v_val_1748_, v___x_1754_);
if (v___x_1767_ == 0)
{
v___y_1750_ = v_candidates_1759_;
goto v___jp_1749_;
}
else
{
if (v___x_1754_ == 0)
{
v_a_1740_ = v_candidates_1759_;
goto v___jp_1739_;
}
else
{
v___y_1750_ = v_candidates_1759_;
goto v___jp_1749_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_candidates_1759_);
lean_del_object(v___x_1736_);
v_a_1768_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1764_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1764_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
v_a_1740_ = v_snd_1734_;
goto v___jp_1739_;
}
v___jp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = l_Lean_LocalDecl_fvarId(v_val_1748_);
v___x_1752_ = lean_box(0);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1750_, v___x_1751_, v___x_1752_);
v_a_1740_ = v___x_1753_;
goto v___jp_1739_;
}
}
v___jp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v_a_1740_);
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1742_ = v___x_1736_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_a_1740_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
size_t v___x_1743_; size_t v___x_1744_; 
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1725_, v___x_1743_);
v_i_1725_ = v___x_1744_;
v_b_1726_ = v___x_1742_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1800_, lean_object* v_sz_1801_, lean_object* v_i_1802_, lean_object* v_b_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1801_);
lean_dec(v_sz_1801_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1802_);
lean_dec(v_i_1802_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1800_, v_sz_boxed_1809_, v_i_boxed_1810_, v_b_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec_ref(v_as_1800_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1812_, size_t v_sz_1813_, size_t v_i_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_usize_dec_lt(v_i_1814_, v_sz_1813_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_b_1815_);
return v___x_1822_;
}
else
{
lean_object* v_snd_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1887_; 
v_snd_1823_ = lean_ctor_get(v_b_1815_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_b_1815_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_b_1815_, 0);
lean_dec(v_unused_1888_);
v___x_1825_ = v_b_1815_;
v_isShared_1826_ = v_isSharedCheck_1887_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_snd_1823_);
lean_dec(v_b_1815_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1887_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v_a_1829_; lean_object* v_a_1836_; 
v___x_1827_ = lean_box(0);
v_a_1836_ = lean_array_uget_borrowed(v_as_1812_, v_i_1814_);
if (lean_obj_tag(v_a_1836_) == 0)
{
v_a_1829_ = v_snd_1823_;
goto v___jp_1828_;
}
else
{
lean_object* v_val_1837_; lean_object* v___y_1839_; uint8_t v___x_1843_; 
v_val_1837_ = lean_ctor_get(v_a_1836_, 0);
v___x_1843_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1837_);
if (v___x_1843_ == 0)
{
lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; lean_object* v_candidates_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___x_1865_; 
v___f_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1846_ = l_Lean_LocalDecl_type(v_val_1837_);
lean_inc_ref(v___x_1846_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1845_, v___f_1844_, v___x_1843_, v___x_1846_, v_snd_1823_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = l_Lean_LocalDecl_value_x3f(v_val_1837_, v___x_1843_);
if (lean_obj_tag(v___x_1867_) == 0)
{
v_candidates_1848_ = v_a_1866_;
v___y_1849_ = v___y_1816_;
v___y_1850_ = v___y_1817_;
v___y_1851_ = v___y_1818_;
v___y_1852_ = v___y_1819_;
goto v___jp_1847_;
}
else
{
lean_object* v_val_1868_; lean_object* v___x_1869_; 
v_val_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1845_, v___f_1844_, v___x_1843_, v_val_1868_, v_a_1866_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_candidates_1848_ = v_a_1870_;
v___y_1849_ = v___y_1816_;
v___y_1850_ = v___y_1817_;
v___y_1851_ = v___y_1818_;
v___y_1852_ = v___y_1819_;
goto v___jp_1847_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1846_);
lean_del_object(v___x_1825_);
v_a_1871_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1869_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v___x_1846_);
lean_del_object(v___x_1825_);
v_a_1879_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1865_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
v___jp_1847_:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Meta_isProp(v___x_1846_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; uint8_t v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = lean_unbox(v_a_1854_);
lean_dec(v_a_1854_);
if (v___x_1855_ == 0)
{
v_a_1829_ = v_candidates_1848_;
goto v___jp_1828_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_LocalDecl_hasValue(v_val_1837_, v___x_1843_);
if (v___x_1856_ == 0)
{
v___y_1839_ = v_candidates_1848_;
goto v___jp_1838_;
}
else
{
if (v___x_1843_ == 0)
{
v_a_1829_ = v_candidates_1848_;
goto v___jp_1828_;
}
else
{
v___y_1839_ = v_candidates_1848_;
goto v___jp_1838_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_candidates_1848_);
lean_del_object(v___x_1825_);
v_a_1857_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1853_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1853_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
v_a_1829_ = v_snd_1823_;
goto v___jp_1828_;
}
v___jp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = l_Lean_LocalDecl_fvarId(v_val_1837_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1839_, v___x_1840_, v___x_1841_);
v_a_1829_ = v___x_1842_;
goto v___jp_1828_;
}
}
v___jp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v_a_1829_);
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1831_ = v___x_1825_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_a_1829_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
size_t v___x_1832_; size_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_add(v_i_1814_, v___x_1832_);
v___x_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1812_, v_sz_1813_, v___x_1833_, v___x_1831_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1889_, lean_object* v_sz_1890_, lean_object* v_i_1891_, lean_object* v_b_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
size_t v_sz_boxed_1898_; size_t v_i_boxed_1899_; lean_object* v_res_1900_; 
v_sz_boxed_1898_ = lean_unbox_usize(v_sz_1890_);
lean_dec(v_sz_1890_);
v_i_boxed_1899_ = lean_unbox_usize(v_i_1891_);
lean_dec(v_i_1891_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1889_, v_sz_boxed_1898_, v_i_boxed_1899_, v_b_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec_ref(v_as_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1901_, size_t v_sz_1902_, size_t v_i_1903_, lean_object* v_b_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_lt(v_i_1903_, v_sz_1902_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_b_1904_);
return v___x_1911_;
}
else
{
lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1976_; 
v_snd_1912_ = lean_ctor_get(v_b_1904_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_b_1904_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_b_1904_, 0);
lean_dec(v_unused_1977_);
v___x_1914_ = v_b_1904_;
v_isShared_1915_ = v_isSharedCheck_1976_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_dec(v_b_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1976_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v_a_1918_; lean_object* v_a_1925_; 
v___x_1916_ = lean_box(0);
v_a_1925_ = lean_array_uget_borrowed(v_as_1901_, v_i_1903_);
if (lean_obj_tag(v_a_1925_) == 0)
{
v_a_1918_ = v_snd_1912_;
goto v___jp_1917_;
}
else
{
lean_object* v_val_1926_; lean_object* v___y_1928_; uint8_t v___x_1932_; 
v_val_1926_ = lean_ctor_get(v_a_1925_, 0);
v___x_1932_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1926_);
if (v___x_1932_ == 0)
{
lean_object* v___f_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; lean_object* v_candidates_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___x_1954_; 
v___f_1933_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1935_ = l_Lean_LocalDecl_type(v_val_1926_);
lean_inc_ref(v___x_1935_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1934_, v___f_1933_, v___x_1932_, v___x_1935_, v_snd_1912_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l_Lean_LocalDecl_value_x3f(v_val_1926_, v___x_1932_);
if (lean_obj_tag(v___x_1956_) == 0)
{
v_candidates_1937_ = v_a_1955_;
v___y_1938_ = v___y_1905_;
v___y_1939_ = v___y_1906_;
v___y_1940_ = v___y_1907_;
v___y_1941_ = v___y_1908_;
goto v___jp_1936_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1958_; 
v_val_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1934_, v___f_1933_, v___x_1932_, v_val_1957_, v_a_1955_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v_candidates_1937_ = v_a_1959_;
v___y_1938_ = v___y_1905_;
v___y_1939_ = v___y_1906_;
v___y_1940_ = v___y_1907_;
v___y_1941_ = v___y_1908_;
goto v___jp_1936_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v___x_1935_);
lean_del_object(v___x_1914_);
v_a_1960_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec_ref(v___x_1935_);
lean_del_object(v___x_1914_);
v_a_1968_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1954_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1954_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
v___jp_1936_:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Lean_Meta_isProp(v___x_1935_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; uint8_t v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1944_ == 0)
{
v_a_1918_ = v_candidates_1937_;
goto v___jp_1917_;
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_LocalDecl_hasValue(v_val_1926_, v___x_1932_);
if (v___x_1945_ == 0)
{
v___y_1928_ = v_candidates_1937_;
goto v___jp_1927_;
}
else
{
if (v___x_1932_ == 0)
{
v_a_1918_ = v_candidates_1937_;
goto v___jp_1917_;
}
else
{
v___y_1928_ = v_candidates_1937_;
goto v___jp_1927_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_candidates_1937_);
lean_del_object(v___x_1914_);
v_a_1946_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1942_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1942_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
v_a_1918_ = v_snd_1912_;
goto v___jp_1917_;
}
v___jp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_LocalDecl_fvarId(v_val_1926_);
v___x_1930_ = lean_box(0);
v___x_1931_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1928_, v___x_1929_, v___x_1930_);
v_a_1918_ = v___x_1931_;
goto v___jp_1917_;
}
}
v___jp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v_a_1918_);
lean_ctor_set(v___x_1914_, 0, v___x_1916_);
v___x_1920_ = v___x_1914_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_a_1918_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
size_t v___x_1921_; size_t v___x_1922_; 
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1903_, v___x_1921_);
v_i_1903_ = v___x_1922_;
v_b_1904_ = v___x_1920_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1978_, lean_object* v_sz_1979_, lean_object* v_i_1980_, lean_object* v_b_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1979_);
lean_dec(v_sz_1979_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1980_);
lean_dec(v_i_1980_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1978_, v_sz_boxed_1987_, v_i_boxed_1988_, v_b_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec_ref(v_as_1978_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1990_, size_t v_sz_1991_, size_t v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_lt(v_i_1992_, v_sz_1991_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_b_1993_);
return v___x_2000_;
}
else
{
lean_object* v_snd_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2065_; 
v_snd_2001_ = lean_ctor_get(v_b_1993_, 1);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_b_1993_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_b_1993_, 0);
lean_dec(v_unused_2066_);
v___x_2003_ = v_b_1993_;
v_isShared_2004_ = v_isSharedCheck_2065_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snd_2001_);
lean_dec(v_b_1993_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2065_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v_a_2007_; lean_object* v_a_2014_; 
v___x_2005_ = lean_box(0);
v_a_2014_ = lean_array_uget_borrowed(v_as_1990_, v_i_1992_);
if (lean_obj_tag(v_a_2014_) == 0)
{
v_a_2007_ = v_snd_2001_;
goto v___jp_2006_;
}
else
{
lean_object* v_val_2015_; lean_object* v___y_2017_; uint8_t v___x_2021_; 
v_val_2015_ = lean_ctor_get(v_a_2014_, 0);
v___x_2021_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2015_);
if (v___x_2021_ == 0)
{
lean_object* v___f_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v_candidates_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___x_2043_; 
v___f_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2024_ = l_Lean_LocalDecl_type(v_val_2015_);
lean_inc_ref(v___x_2024_);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2023_, v___f_2022_, v___x_2021_, v___x_2024_, v_snd_2001_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_LocalDecl_value_x3f(v_val_2015_, v___x_2021_);
if (lean_obj_tag(v___x_2045_) == 0)
{
v_candidates_2026_ = v_a_2044_;
v___y_2027_ = v___y_1994_;
v___y_2028_ = v___y_1995_;
v___y_2029_ = v___y_1996_;
v___y_2030_ = v___y_1997_;
goto v___jp_2025_;
}
else
{
lean_object* v_val_2046_; lean_object* v___x_2047_; 
v_val_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2023_, v___f_2022_, v___x_2021_, v_val_2046_, v_a_2044_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v_candidates_2026_ = v_a_2048_;
v___y_2027_ = v___y_1994_;
v___y_2028_ = v___y_1995_;
v___y_2029_ = v___y_1996_;
v___y_2030_ = v___y_1997_;
goto v___jp_2025_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v___x_2024_);
lean_del_object(v___x_2003_);
v_a_2049_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2047_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2047_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___x_2024_);
lean_del_object(v___x_2003_);
v_a_2057_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2043_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2043_);
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
v___jp_2025_:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_isProp(v___x_2024_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; uint8_t v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
if (v___x_2033_ == 0)
{
v_a_2007_ = v_candidates_2026_;
goto v___jp_2006_;
}
else
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_LocalDecl_hasValue(v_val_2015_, v___x_2021_);
if (v___x_2034_ == 0)
{
v___y_2017_ = v_candidates_2026_;
goto v___jp_2016_;
}
else
{
if (v___x_2021_ == 0)
{
v_a_2007_ = v_candidates_2026_;
goto v___jp_2006_;
}
else
{
v___y_2017_ = v_candidates_2026_;
goto v___jp_2016_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_candidates_2026_);
lean_del_object(v___x_2003_);
v_a_2035_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2031_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2031_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
v_a_2007_ = v_snd_2001_;
goto v___jp_2006_;
}
v___jp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = l_Lean_LocalDecl_fvarId(v_val_2015_);
v___x_2019_ = lean_box(0);
v___x_2020_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2017_, v___x_2018_, v___x_2019_);
v_a_2007_ = v___x_2020_;
goto v___jp_2006_;
}
}
v___jp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v_a_2007_);
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2009_ = v___x_2003_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_a_2007_);
v___x_2009_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = ((size_t)1ULL);
v___x_2011_ = lean_usize_add(v_i_1992_, v___x_2010_);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1990_, v_sz_1991_, v___x_2011_, v___x_2009_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
return v___x_2012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2067_, lean_object* v_sz_2068_, lean_object* v_i_2069_, lean_object* v_b_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2068_);
lean_dec(v_sz_2068_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2067_, v_sz_boxed_2076_, v_i_boxed_2077_, v_b_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_as_2067_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2079_, lean_object* v_n_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
if (lean_obj_tag(v_n_2080_) == 0)
{
lean_object* v_cs_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; size_t v_sz_2090_; size_t v___x_2091_; lean_object* v___x_2092_; 
v_cs_2087_ = lean_ctor_get(v_n_2080_, 0);
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v_b_2081_);
v_sz_2090_ = lean_array_size(v_cs_2087_);
v___x_2091_ = ((size_t)0ULL);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2079_, v_cs_2087_, v_sz_2090_, v___x_2091_, v___x_2089_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2107_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2107_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_fst_2097_; 
v_fst_2097_ = lean_ctor_get(v_a_2093_, 0);
if (lean_obj_tag(v_fst_2097_) == 0)
{
lean_object* v_snd_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_snd_2098_ = lean_ctor_get(v_a_2093_, 1);
lean_inc(v_snd_2098_);
lean_dec(v_a_2093_);
v___x_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2099_, 0, v_snd_2098_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2099_);
v___x_2101_ = v___x_2095_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
else
{
lean_object* v_val_2103_; lean_object* v___x_2105_; 
lean_inc_ref(v_fst_2097_);
lean_dec(v_a_2093_);
v_val_2103_ = lean_ctor_get(v_fst_2097_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v_fst_2097_, 1);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v_val_2103_);
v___x_2105_ = v___x_2095_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_val_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_a_2108_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2092_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2092_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
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
lean_object* v_vs_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; size_t v_sz_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v_vs_2116_ = lean_ctor_get(v_n_2080_, 0);
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_b_2081_);
v_sz_2119_ = lean_array_size(v_vs_2116_);
v___x_2120_ = ((size_t)0ULL);
v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2116_, v_sz_2119_, v___x_2120_, v___x_2118_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2136_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2136_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2136_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_fst_2126_; 
v_fst_2126_ = lean_ctor_get(v_a_2122_, 0);
if (lean_obj_tag(v_fst_2126_) == 0)
{
lean_object* v_snd_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_snd_2127_ = lean_ctor_get(v_a_2122_, 1);
lean_inc(v_snd_2127_);
lean_dec(v_a_2122_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v_snd_2127_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2128_);
v___x_2130_ = v___x_2124_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2134_; 
lean_inc_ref(v_fst_2126_);
lean_dec(v_a_2122_);
v_val_2132_ = lean_ctor_get(v_fst_2126_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v_fst_2126_, 1);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_val_2132_);
v___x_2134_ = v___x_2124_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_val_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2121_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2121_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2145_, lean_object* v_as_2146_, size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_b_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_b_2149_);
return v___x_2156_;
}
else
{
lean_object* v_snd_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2191_; 
v_snd_2157_ = lean_ctor_get(v_b_2149_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_b_2149_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_b_2149_, 0);
lean_dec(v_unused_2192_);
v___x_2159_ = v_b_2149_;
v_isShared_2160_ = v_isSharedCheck_2191_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snd_2157_);
lean_dec(v_b_2149_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2191_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_array_uget_borrowed(v_as_2146_, v_i_2148_);
lean_inc(v_snd_2157_);
v___x_2162_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2145_, v_a_2161_, v_snd_2157_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2182_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2182_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2182_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
if (lean_obj_tag(v_a_2163_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_a_2163_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2167_);
v___x_2169_ = v___x_2159_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_snd_2157_);
v___x_2169_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2171_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2169_);
v___x_2171_ = v___x_2165_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_del_object(v___x_2165_);
lean_dec(v_snd_2157_);
v_a_2174_ = lean_ctor_get(v_a_2163_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v_a_2163_, 1);
v___x_2175_ = lean_box(0);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_a_2174_);
lean_ctor_set(v___x_2159_, 0, v___x_2175_);
v___x_2177_ = v___x_2159_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_a_2174_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
size_t v___x_2178_; size_t v___x_2179_; 
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2148_, v___x_2178_);
v_i_2148_ = v___x_2179_;
v_b_2149_ = v___x_2177_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2159_);
lean_dec(v_snd_2157_);
v_a_2183_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2162_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2162_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2193_, lean_object* v_as_2194_, lean_object* v_sz_2195_, lean_object* v_i_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
size_t v_sz_boxed_2203_; size_t v_i_boxed_2204_; lean_object* v_res_2205_; 
v_sz_boxed_2203_ = lean_unbox_usize(v_sz_2195_);
lean_dec(v_sz_2195_);
v_i_boxed_2204_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2193_, v_as_2194_, v_sz_boxed_2203_, v_i_boxed_2204_, v_b_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_as_2194_);
lean_dec_ref(v_init_2193_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2206_, lean_object* v_n_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2206_, v_n_2207_, v_b_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_n_2207_);
lean_dec_ref(v_init_2206_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2215_, lean_object* v_init_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_root_2222_; lean_object* v_tail_2223_; lean_object* v___x_2224_; 
v_root_2222_ = lean_ctor_get(v_t_2215_, 0);
v_tail_2223_ = lean_ctor_get(v_t_2215_, 1);
lean_inc_ref(v_init_2216_);
v___x_2224_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2216_, v_root_2222_, v_init_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec_ref(v_init_2216_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2261_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2261_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2261_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
if (lean_obj_tag(v_a_2225_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; 
v_a_2229_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v_a_2225_, 1);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_a_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; size_t v_sz_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
lean_del_object(v___x_2227_);
v_a_2233_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v_a_2225_, 1);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v_a_2233_);
v_sz_2236_ = lean_array_size(v_tail_2223_);
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2223_, v_sz_2236_, v___x_2237_, v___x_2235_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2252_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2252_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2252_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v_fst_2243_; 
v_fst_2243_ = lean_ctor_get(v_a_2239_, 0);
if (lean_obj_tag(v_fst_2243_) == 0)
{
lean_object* v_snd_2244_; lean_object* v___x_2246_; 
v_snd_2244_ = lean_ctor_get(v_a_2239_, 1);
lean_inc(v_snd_2244_);
lean_dec(v_a_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_snd_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_snd_2244_);
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
lean_object* v_val_2248_; lean_object* v___x_2250_; 
lean_inc_ref(v_fst_2243_);
lean_dec(v_a_2239_);
v_val_2248_ = lean_ctor_get(v_fst_2243_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v_fst_2243_, 1);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_val_2248_);
v___x_2250_ = v___x_2241_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_val_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_a_2253_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2238_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2238_);
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
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
v_a_2262_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2224_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2224_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2270_, lean_object* v_init_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2270_, v_init_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_t_2270_);
return v_res_2277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_buckets_2280_; lean_object* v___x_2281_; uint64_t v___x_2282_; uint64_t v___x_2283_; uint64_t v___x_2284_; uint64_t v_fold_2285_; uint64_t v___x_2286_; uint64_t v___x_2287_; uint64_t v___x_2288_; size_t v___x_2289_; size_t v___x_2290_; size_t v___x_2291_; size_t v___x_2292_; size_t v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_buckets_2280_ = lean_ctor_get(v_m_2278_, 1);
v___x_2281_ = lean_array_get_size(v_buckets_2280_);
v___x_2282_ = l_Lean_instHashableFVarId_hash(v_a_2279_);
v___x_2283_ = 32ULL;
v___x_2284_ = lean_uint64_shift_right(v___x_2282_, v___x_2283_);
v_fold_2285_ = lean_uint64_xor(v___x_2282_, v___x_2284_);
v___x_2286_ = 16ULL;
v___x_2287_ = lean_uint64_shift_right(v_fold_2285_, v___x_2286_);
v___x_2288_ = lean_uint64_xor(v_fold_2285_, v___x_2287_);
v___x_2289_ = lean_uint64_to_usize(v___x_2288_);
v___x_2290_ = lean_usize_of_nat(v___x_2281_);
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_sub(v___x_2290_, v___x_2291_);
v___x_2293_ = lean_usize_land(v___x_2289_, v___x_2292_);
v___x_2294_ = lean_array_uget_borrowed(v_buckets_2280_, v___x_2293_);
v___x_2295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2279_, v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2296_, lean_object* v_a_2297_){
_start:
{
uint8_t v_res_2298_; lean_object* v_r_2299_; 
v_res_2298_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2296_, v_a_2297_);
lean_dec(v_a_2297_);
lean_dec_ref(v_m_2296_);
v_r_2299_ = lean_box(v_res_2298_);
return v_r_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2300_, lean_object* v_as_2301_, size_t v_sz_2302_, size_t v_i_2303_, lean_object* v_b_2304_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_lt(v_i_2303_, v_sz_2302_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_b_2304_);
return v___x_2307_;
}
else
{
lean_object* v_snd_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2326_; 
v_snd_2308_ = lean_ctor_get(v_b_2304_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_b_2304_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_b_2304_, 0);
lean_dec(v_unused_2327_);
v___x_2310_ = v_b_2304_;
v_isShared_2311_ = v_isSharedCheck_2326_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_snd_2308_);
lean_dec(v_b_2304_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2326_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v_a_2314_; lean_object* v_a_2321_; 
v___x_2312_ = lean_box(0);
v_a_2321_ = lean_array_uget_borrowed(v_as_2301_, v_i_2303_);
if (lean_obj_tag(v_a_2321_) == 0)
{
v_a_2314_ = v_snd_2308_;
goto v___jp_2313_;
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_val_2322_ = lean_ctor_get(v_a_2321_, 0);
v___x_2323_ = l_Lean_LocalDecl_fvarId(v_val_2322_);
v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2300_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec(v___x_2323_);
v_a_2314_ = v_snd_2308_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_array_push(v_snd_2308_, v___x_2323_);
v_a_2314_ = v___x_2325_;
goto v___jp_2313_;
}
}
v___jp_2313_:
{
lean_object* v___x_2316_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v_a_2314_);
lean_ctor_set(v___x_2310_, 0, v___x_2312_);
v___x_2316_ = v___x_2310_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2316_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
size_t v___x_2317_; size_t v___x_2318_; 
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_add(v_i_2303_, v___x_2317_);
v_i_2303_ = v___x_2318_;
v_b_2304_ = v___x_2316_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2328_, lean_object* v_as_2329_, lean_object* v_sz_2330_, lean_object* v_i_2331_, lean_object* v_b_2332_, lean_object* v___y_2333_){
_start:
{
size_t v_sz_boxed_2334_; size_t v_i_boxed_2335_; lean_object* v_res_2336_; 
v_sz_boxed_2334_ = lean_unbox_usize(v_sz_2330_);
lean_dec(v_sz_2330_);
v_i_boxed_2335_ = lean_unbox_usize(v_i_2331_);
lean_dec(v_i_2331_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2328_, v_as_2329_, v_sz_boxed_2334_, v_i_boxed_2335_, v_b_2332_);
lean_dec_ref(v_as_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2337_, lean_object* v_as_2338_, size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_usize_dec_lt(v_i_2340_, v_sz_2339_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_b_2341_);
return v___x_2348_;
}
else
{
lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2367_; 
v_snd_2349_ = lean_ctor_get(v_b_2341_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_b_2341_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; 
v_unused_2368_ = lean_ctor_get(v_b_2341_, 0);
lean_dec(v_unused_2368_);
v___x_2351_ = v_b_2341_;
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v_b_2341_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v_a_2355_; lean_object* v_a_2362_; 
v___x_2353_ = lean_box(0);
v_a_2362_ = lean_array_uget_borrowed(v_as_2338_, v_i_2340_);
if (lean_obj_tag(v_a_2362_) == 0)
{
v_a_2355_ = v_snd_2349_;
goto v___jp_2354_;
}
else
{
lean_object* v_val_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_val_2363_ = lean_ctor_get(v_a_2362_, 0);
v___x_2364_ = l_Lean_LocalDecl_fvarId(v_val_2363_);
v___x_2365_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2337_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec(v___x_2364_);
v_a_2355_ = v_snd_2349_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_array_push(v_snd_2349_, v___x_2364_);
v_a_2355_ = v___x_2366_;
goto v___jp_2354_;
}
}
v___jp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 1, v_a_2355_);
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2357_ = v___x_2351_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_a_2355_);
v___x_2357_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
size_t v___x_2358_; size_t v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = ((size_t)1ULL);
v___x_2359_ = lean_usize_add(v_i_2340_, v___x_2358_);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2337_, v_as_2338_, v_sz_2339_, v___x_2359_, v___x_2357_);
return v___x_2360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2369_, lean_object* v_as_2370_, lean_object* v_sz_2371_, lean_object* v_i_2372_, lean_object* v_b_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
size_t v_sz_boxed_2379_; size_t v_i_boxed_2380_; lean_object* v_res_2381_; 
v_sz_boxed_2379_ = lean_unbox_usize(v_sz_2371_);
lean_dec(v_sz_2371_);
v_i_boxed_2380_ = lean_unbox_usize(v_i_2372_);
lean_dec(v_i_2372_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2369_, v_as_2370_, v_sz_boxed_2379_, v_i_boxed_2380_, v_b_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v_as_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2382_, lean_object* v_a_2383_, lean_object* v_n_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
if (lean_obj_tag(v_n_2384_) == 0)
{
lean_object* v_cs_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v_cs_2391_ = lean_ctor_get(v_n_2384_, 0);
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v_b_2385_);
v_sz_2394_ = lean_array_size(v_cs_2391_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2382_, v_a_2383_, v_cs_2391_, v_sz_2394_, v___x_2395_, v___x_2393_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2411_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_fst_2401_; 
v_fst_2401_ = lean_ctor_get(v_a_2397_, 0);
if (lean_obj_tag(v_fst_2401_) == 0)
{
lean_object* v_snd_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v_snd_2402_ = lean_ctor_get(v_a_2397_, 1);
lean_inc(v_snd_2402_);
lean_dec(v_a_2397_);
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v_snd_2402_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2403_);
v___x_2405_ = v___x_2399_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
else
{
lean_object* v_val_2407_; lean_object* v___x_2409_; 
lean_inc_ref(v_fst_2401_);
lean_dec(v_a_2397_);
v_val_2407_ = lean_ctor_get(v_fst_2401_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v_fst_2401_, 1);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_val_2407_);
v___x_2409_ = v___x_2399_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_val_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_a_2412_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2396_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2396_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_vs_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; size_t v_sz_2423_; size_t v___x_2424_; lean_object* v___x_2425_; 
v_vs_2420_ = lean_ctor_get(v_n_2384_, 0);
v___x_2421_ = lean_box(0);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v_b_2385_);
v_sz_2423_ = lean_array_size(v_vs_2420_);
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2383_, v_vs_2420_, v_sz_2423_, v___x_2424_, v___x_2422_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2440_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2440_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2440_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_fst_2430_; 
v_fst_2430_ = lean_ctor_get(v_a_2426_, 0);
if (lean_obj_tag(v_fst_2430_) == 0)
{
lean_object* v_snd_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v_snd_2431_ = lean_ctor_get(v_a_2426_, 1);
lean_inc(v_snd_2431_);
lean_dec(v_a_2426_);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_snd_2431_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2432_);
v___x_2434_ = v___x_2428_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
else
{
lean_object* v_val_2436_; lean_object* v___x_2438_; 
lean_inc_ref(v_fst_2430_);
lean_dec(v_a_2426_);
v_val_2436_ = lean_ctor_get(v_fst_2430_, 0);
lean_inc(v_val_2436_);
lean_dec_ref_known(v_fst_2430_, 1);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v_val_2436_);
v___x_2438_ = v___x_2428_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_val_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2425_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2425_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2449_, lean_object* v_a_2450_, lean_object* v_as_2451_, size_t v_sz_2452_, size_t v_i_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_lt(v_i_2453_, v_sz_2452_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_b_2454_);
return v___x_2461_;
}
else
{
lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2496_; 
v_snd_2462_ = lean_ctor_get(v_b_2454_, 1);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_b_2454_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v_b_2454_, 0);
lean_dec(v_unused_2497_);
v___x_2464_ = v_b_2454_;
v_isShared_2465_ = v_isSharedCheck_2496_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_dec(v_b_2454_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2496_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_array_uget_borrowed(v_as_2451_, v_i_2453_);
lean_inc(v_snd_2462_);
v___x_2467_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2449_, v_a_2450_, v_a_2466_, v_snd_2462_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2487_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2487_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2487_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
if (lean_obj_tag(v_a_2468_) == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2468_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2472_);
v___x_2474_ = v___x_2464_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_snd_2462_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2474_);
v___x_2476_ = v___x_2470_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_del_object(v___x_2470_);
lean_dec(v_snd_2462_);
v_a_2479_ = lean_ctor_get(v_a_2468_, 0);
lean_inc(v_a_2479_);
lean_dec_ref_known(v_a_2468_, 1);
v___x_2480_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v_a_2479_);
lean_ctor_set(v___x_2464_, 0, v___x_2480_);
v___x_2482_ = v___x_2464_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_a_2479_);
v___x_2482_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
size_t v___x_2483_; size_t v___x_2484_; 
v___x_2483_ = ((size_t)1ULL);
v___x_2484_ = lean_usize_add(v_i_2453_, v___x_2483_);
v_i_2453_ = v___x_2484_;
v_b_2454_ = v___x_2482_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_del_object(v___x_2464_);
lean_dec(v_snd_2462_);
v_a_2488_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2467_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2467_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2498_, lean_object* v_a_2499_, lean_object* v_as_2500_, lean_object* v_sz_2501_, lean_object* v_i_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
size_t v_sz_boxed_2509_; size_t v_i_boxed_2510_; lean_object* v_res_2511_; 
v_sz_boxed_2509_ = lean_unbox_usize(v_sz_2501_);
lean_dec(v_sz_2501_);
v_i_boxed_2510_ = lean_unbox_usize(v_i_2502_);
lean_dec(v_i_2502_);
v_res_2511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2498_, v_a_2499_, v_as_2500_, v_sz_boxed_2509_, v_i_boxed_2510_, v_b_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v_as_2500_);
lean_dec_ref(v_a_2499_);
lean_dec_ref(v_init_2498_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2512_, lean_object* v_a_2513_, lean_object* v_n_2514_, lean_object* v_b_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2512_, v_a_2513_, v_n_2514_, v_b_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_n_2514_);
lean_dec_ref(v_a_2513_);
lean_dec_ref(v_init_2512_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2522_, lean_object* v_as_2523_, size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_b_2526_){
_start:
{
uint8_t v___x_2528_; 
v___x_2528_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2526_);
return v___x_2529_;
}
else
{
lean_object* v_snd_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2548_; 
v_snd_2530_ = lean_ctor_get(v_b_2526_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_b_2526_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v_b_2526_, 0);
lean_dec(v_unused_2549_);
v___x_2532_ = v_b_2526_;
v_isShared_2533_ = v_isSharedCheck_2548_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_snd_2530_);
lean_dec(v_b_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2548_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v_a_2536_; lean_object* v_a_2543_; 
v___x_2534_ = lean_box(0);
v_a_2543_ = lean_array_uget_borrowed(v_as_2523_, v_i_2525_);
if (lean_obj_tag(v_a_2543_) == 0)
{
v_a_2536_ = v_snd_2530_;
goto v___jp_2535_;
}
else
{
lean_object* v_val_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_val_2544_ = lean_ctor_get(v_a_2543_, 0);
v___x_2545_ = l_Lean_LocalDecl_fvarId(v_val_2544_);
v___x_2546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2522_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec(v___x_2545_);
v_a_2536_ = v_snd_2530_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_array_push(v_snd_2530_, v___x_2545_);
v_a_2536_ = v___x_2547_;
goto v___jp_2535_;
}
}
v___jp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 1, v_a_2536_);
lean_ctor_set(v___x_2532_, 0, v___x_2534_);
v___x_2538_ = v___x_2532_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_a_2536_);
v___x_2538_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
size_t v___x_2539_; size_t v___x_2540_; 
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2525_, v___x_2539_);
v_i_2525_ = v___x_2540_;
v_b_2526_ = v___x_2538_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2550_, lean_object* v_as_2551_, lean_object* v_sz_2552_, lean_object* v_i_2553_, lean_object* v_b_2554_, lean_object* v___y_2555_){
_start:
{
size_t v_sz_boxed_2556_; size_t v_i_boxed_2557_; lean_object* v_res_2558_; 
v_sz_boxed_2556_ = lean_unbox_usize(v_sz_2552_);
lean_dec(v_sz_2552_);
v_i_boxed_2557_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_res_2558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2550_, v_as_2551_, v_sz_boxed_2556_, v_i_boxed_2557_, v_b_2554_);
lean_dec_ref(v_as_2551_);
lean_dec_ref(v_a_2550_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2559_, lean_object* v_as_2560_, size_t v_sz_2561_, size_t v_i_2562_, lean_object* v_b_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_usize_dec_lt(v_i_2562_, v_sz_2561_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_b_2563_);
return v___x_2570_;
}
else
{
lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2589_; 
v_snd_2571_ = lean_ctor_get(v_b_2563_, 1);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_b_2563_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; 
v_unused_2590_ = lean_ctor_get(v_b_2563_, 0);
lean_dec(v_unused_2590_);
v___x_2573_ = v_b_2563_;
v_isShared_2574_ = v_isSharedCheck_2589_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_dec(v_b_2563_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2589_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v_a_2577_; lean_object* v_a_2584_; 
v___x_2575_ = lean_box(0);
v_a_2584_ = lean_array_uget_borrowed(v_as_2560_, v_i_2562_);
if (lean_obj_tag(v_a_2584_) == 0)
{
v_a_2577_ = v_snd_2571_;
goto v___jp_2576_;
}
else
{
lean_object* v_val_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_val_2585_ = lean_ctor_get(v_a_2584_, 0);
v___x_2586_ = l_Lean_LocalDecl_fvarId(v_val_2585_);
v___x_2587_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2559_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_dec(v___x_2586_);
v_a_2577_ = v_snd_2571_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_array_push(v_snd_2571_, v___x_2586_);
v_a_2577_ = v___x_2588_;
goto v___jp_2576_;
}
}
v___jp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v_a_2577_);
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2579_ = v___x_2573_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_a_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_add(v_i_2562_, v___x_2580_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2559_, v_as_2560_, v_sz_2561_, v___x_2581_, v___x_2579_);
return v___x_2582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2591_, lean_object* v_as_2592_, lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_b_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
size_t v_sz_boxed_2601_; size_t v_i_boxed_2602_; lean_object* v_res_2603_; 
v_sz_boxed_2601_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2602_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2591_, v_as_2592_, v_sz_boxed_2601_, v_i_boxed_2602_, v_b_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v_as_2592_);
lean_dec_ref(v_a_2591_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2604_, lean_object* v_t_2605_, lean_object* v_init_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_root_2612_; lean_object* v_tail_2613_; lean_object* v___x_2614_; 
v_root_2612_ = lean_ctor_get(v_t_2605_, 0);
v_tail_2613_ = lean_ctor_get(v_t_2605_, 1);
lean_inc_ref(v_init_2606_);
v___x_2614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2606_, v_a_2604_, v_root_2612_, v_init_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec_ref(v_init_2606_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2651_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2651_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2651_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
if (lean_obj_tag(v_a_2615_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; 
v_a_2619_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_a_2615_, 1);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_a_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; size_t v_sz_2626_; size_t v___x_2627_; lean_object* v___x_2628_; 
lean_del_object(v___x_2617_);
v_a_2623_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_a_2615_, 1);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
lean_ctor_set(v___x_2625_, 1, v_a_2623_);
v_sz_2626_ = lean_array_size(v_tail_2613_);
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2604_, v_tail_2613_, v_sz_2626_, v___x_2627_, v___x_2625_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2642_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2642_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2642_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_fst_2633_; 
v_fst_2633_ = lean_ctor_get(v_a_2629_, 0);
if (lean_obj_tag(v_fst_2633_) == 0)
{
lean_object* v_snd_2634_; lean_object* v___x_2636_; 
v_snd_2634_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_snd_2634_);
lean_dec(v_a_2629_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_snd_2634_);
v___x_2636_ = v___x_2631_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_snd_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v_val_2638_; lean_object* v___x_2640_; 
lean_inc_ref(v_fst_2633_);
lean_dec(v_a_2629_);
v_val_2638_ = lean_ctor_get(v_fst_2633_, 0);
lean_inc(v_val_2638_);
lean_dec_ref_known(v_fst_2633_, 1);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_val_2638_);
v___x_2640_ = v___x_2631_;
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
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
v_a_2643_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2628_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2628_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2614_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2614_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2660_, lean_object* v_t_2661_, lean_object* v_init_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2660_, v_t_2661_, v_init_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_t_2661_);
lean_dec_ref(v_a_2660_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2671_, lean_object* v_mvarId_2672_, lean_object* v___f_2673_, lean_object* v___f_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_lctx_2680_; lean_object* v_decls_2681_; lean_object* v___x_2682_; 
v_lctx_2680_ = lean_ctor_get(v___y_2675_, 2);
v_decls_2681_ = lean_ctor_get(v_lctx_2680_, 1);
lean_inc_ref(v_decls_2681_);
v___x_2682_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2681_, v_candidates_2671_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_MVarId_getType(v_mvarId_2672_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___y_2690_; uint8_t v___x_2714_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2685_, v___y_2676_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
v___x_2688_ = lean_st_mk_ref(v_a_2683_);
v___x_2714_ = l_Lean_Expr_hasFVar(v_a_2687_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v_a_2687_);
lean_dec_ref(v___f_2674_);
v___x_2715_ = lean_box(0);
lean_inc(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___x_2688_);
v___x_2716_ = lean_apply_7(v___f_2673_, v___x_2715_, v___x_2688_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, lean_box(0));
v___y_2690_ = v___x_2716_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2718_ = 0;
v___x_2719_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2717_, v___f_2674_, v_a_2687_, v___x_2718_, v___x_2688_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
lean_inc(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
lean_inc(v___x_2688_);
v___x_2721_ = lean_apply_7(v___f_2673_, v_a_2720_, v___x_2688_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, lean_box(0));
v___y_2690_ = v___x_2721_;
goto v___jp_2689_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___x_2688_);
lean_dec_ref(v_decls_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___f_2673_);
v_a_2722_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2719_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2719_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
v___jp_2689_:
{
if (lean_obj_tag(v___y_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2705_; 
v_a_2691_ = lean_ctor_get(v___y_2690_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___y_2690_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2693_ = v___y_2690_;
v_isShared_2694_ = v_isSharedCheck_2705_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___y_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2705_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v_size_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2695_ = lean_st_ref_get(v___x_2688_);
lean_dec(v___x_2688_);
lean_dec(v___x_2695_);
v_size_2696_ = lean_ctor_get(v_a_2691_, 0);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_nat_dec_eq(v_size_2696_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_del_object(v___x_2693_);
v___x_2699_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2700_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2691_, v_decls_2681_, v___x_2699_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_decls_2681_);
lean_dec(v_a_2691_);
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec(v_a_2691_);
lean_dec_ref(v_decls_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
v___x_2701_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2701_);
v___x_2703_ = v___x_2693_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec(v___x_2688_);
lean_dec_ref(v_decls_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
v_a_2706_ = lean_ctor_get(v___y_2690_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___y_2690_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___y_2690_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___y_2690_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_a_2683_);
lean_dec_ref(v_decls_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___f_2674_);
lean_dec_ref(v___f_2673_);
v_a_2730_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2684_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2684_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_decls_2681_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v___f_2674_);
lean_dec_ref(v___f_2673_);
lean_dec(v_mvarId_2672_);
v_a_2738_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2682_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2682_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2746_, lean_object* v_mvarId_2747_, lean_object* v___f_2748_, lean_object* v___f_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2746_, v_mvarId_2747_, v___f_2748_, v___f_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___f_2764_; lean_object* v___f_2765_; lean_object* v_candidates_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; 
v___f_2764_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2765_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2766_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2758_);
v___f_2767_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2767_, 0, v_candidates_2766_);
lean_closure_set(v___f_2767_, 1, v_mvarId_2758_);
lean_closure_set(v___f_2767_, 2, v___f_2765_);
lean_closure_set(v___f_2767_, 3, v___f_2764_);
v___x_2768_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2758_, v___f_2767_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2776_, lean_object* v_m_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2777_, v_a_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2780_, lean_object* v_m_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2780_, v_m_2781_, v_a_2782_);
lean_dec(v_a_2782_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2784_, lean_object* v_m_2785_, lean_object* v_a_2786_, lean_object* v_b_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2785_, v_a_2786_, v_b_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2789_, lean_object* v_m_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2790_, v_a_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2793_, lean_object* v_m_2794_, lean_object* v_a_2795_){
_start:
{
uint8_t v_res_2796_; lean_object* v_r_2797_; 
v_res_2796_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2793_, v_m_2794_, v_a_2795_);
lean_dec(v_a_2795_);
lean_dec_ref(v_m_2794_);
v_r_2797_ = lean_box(v_res_2796_);
return v_r_2797_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_x_2800_){
_start:
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2799_, v_x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2802_, lean_object* v_a_2803_, lean_object* v_x_2804_){
_start:
{
uint8_t v_res_2805_; lean_object* v_r_2806_; 
v_res_2805_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2802_, v_a_2803_, v_x_2804_);
lean_dec(v_x_2804_);
lean_dec(v_a_2803_);
v_r_2806_ = lean_box(v_res_2805_);
return v_r_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2807_, lean_object* v_a_2808_, lean_object* v_x_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2808_, v_x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2811_, lean_object* v_a_2812_, lean_object* v_x_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2811_, v_a_2812_, v_x_2813_);
lean_dec(v_a_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2815_, lean_object* v_a_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2815_, v_a_2816_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2824_, lean_object* v_a_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2824_, v_a_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v_a_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2833_, lean_object* v_data_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2836_, lean_object* v_a_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2836_, v_a_2837_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2845_, v_a_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v_a_2846_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2854_, lean_object* v_i_2855_, lean_object* v_source_2856_, lean_object* v_target_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2855_, v_source_2856_, v_target_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2859_, lean_object* v_as_2860_, size_t v_sz_2861_, size_t v_i_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2859_, v_as_2860_, v_sz_2861_, v_i_2862_, v_b_2863_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2870_, lean_object* v_as_2871_, lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_b_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
size_t v_sz_boxed_2880_; size_t v_i_boxed_2881_; lean_object* v_res_2882_; 
v_sz_boxed_2880_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2881_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2870_, v_as_2871_, v_sz_boxed_2880_, v_i_boxed_2881_, v_b_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec_ref(v_as_2871_);
lean_dec_ref(v_a_2870_);
return v_res_2882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2883_, lean_object* v_m_2884_, lean_object* v_a_2885_){
_start:
{
uint8_t v___x_2886_; 
v___x_2886_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2884_, v_a_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2887_, lean_object* v_m_2888_, lean_object* v_a_2889_){
_start:
{
uint8_t v_res_2890_; lean_object* v_r_2891_; 
v_res_2890_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2887_, v_m_2888_, v_a_2889_);
lean_dec_ref(v_a_2889_);
lean_dec_ref(v_m_2888_);
v_r_2891_ = lean_box(v_res_2890_);
return v_r_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2892_, lean_object* v_m_2893_, lean_object* v_a_2894_, lean_object* v_b_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2893_, v_a_2894_, v_b_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2898_, v_x_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2901_, lean_object* v_as_2902_, size_t v_sz_2903_, size_t v_i_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2901_, v_as_2902_, v_sz_2903_, v_i_2904_, v_b_2905_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2912_, lean_object* v_as_2913_, lean_object* v_sz_2914_, lean_object* v_i_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
size_t v_sz_boxed_2922_; size_t v_i_boxed_2923_; lean_object* v_res_2924_; 
v_sz_boxed_2922_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2923_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2912_, v_as_2913_, v_sz_boxed_2922_, v_i_boxed_2923_, v_b_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_as_2913_);
lean_dec_ref(v_a_2912_);
return v_res_2924_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2925_, lean_object* v_a_2926_, lean_object* v_x_2927_){
_start:
{
uint8_t v___x_2928_; 
v___x_2928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2926_, v_x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2929_, lean_object* v_a_2930_, lean_object* v_x_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2929_, v_a_2930_, v_x_2931_);
lean_dec(v_x_2931_);
lean_dec_ref(v_a_2930_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2934_, lean_object* v_data_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2937_, lean_object* v_i_2938_, lean_object* v_source_2939_, lean_object* v_target_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2938_, v_source_2939_, v_target_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2943_, v_x_2944_);
return v___x_2945_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = l_Lean_maxRecDepthErrorMessage;
v___x_2952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2954_ = l_Lean_MessageData_ofFormat(v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2956_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2957_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___x_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2958_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_ref_2958_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2966_, lean_object* v_ref_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2967_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_ref_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2975_, v_ref_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_2984_, lean_object* v_mvarId_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_fileName_2992_; lean_object* v_fileMap_2993_; lean_object* v_options_2994_; lean_object* v_currRecDepth_2995_; lean_object* v_maxRecDepth_2996_; lean_object* v_ref_2997_; lean_object* v_currNamespace_2998_; lean_object* v_openDecls_2999_; lean_object* v_initHeartbeats_3000_; lean_object* v_maxHeartbeats_3001_; lean_object* v_quotContext_3002_; lean_object* v_currMacroScope_3003_; uint8_t v_diag_3004_; lean_object* v_cancelTk_x3f_3005_; uint8_t v_suppressElabErrors_3006_; lean_object* v_inheritedTraceOptions_3007_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_fileName_2992_ = lean_ctor_get(v_a_2989_, 0);
v_fileMap_2993_ = lean_ctor_get(v_a_2989_, 1);
v_options_2994_ = lean_ctor_get(v_a_2989_, 2);
v_currRecDepth_2995_ = lean_ctor_get(v_a_2989_, 3);
v_maxRecDepth_2996_ = lean_ctor_get(v_a_2989_, 4);
v_ref_2997_ = lean_ctor_get(v_a_2989_, 5);
v_currNamespace_2998_ = lean_ctor_get(v_a_2989_, 6);
v_openDecls_2999_ = lean_ctor_get(v_a_2989_, 7);
v_initHeartbeats_3000_ = lean_ctor_get(v_a_2989_, 8);
v_maxHeartbeats_3001_ = lean_ctor_get(v_a_2989_, 9);
v_quotContext_3002_ = lean_ctor_get(v_a_2989_, 10);
v_currMacroScope_3003_ = lean_ctor_get(v_a_2989_, 11);
v_diag_3004_ = lean_ctor_get_uint8(v_a_2989_, sizeof(void*)*14);
v_cancelTk_x3f_3005_ = lean_ctor_get(v_a_2989_, 12);
v_suppressElabErrors_3006_ = lean_ctor_get_uint8(v_a_2989_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3007_ = lean_ctor_get(v_a_2989_, 13);
v___x_3035_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_nat_dec_eq(v_maxRecDepth_2996_, v___x_3035_);
if (v___x_3036_ == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = lean_nat_dec_eq(v_currRecDepth_2995_, v_maxRecDepth_2996_);
if (v___x_3037_ == 0)
{
goto v___jp_3008_;
}
else
{
lean_object* v___x_3038_; 
lean_dec(v_mvarId_2985_);
lean_dec_ref(v_x_2984_);
lean_inc(v_ref_2997_);
v___x_3038_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2997_);
return v___x_3038_;
}
}
else
{
goto v___jp_3008_;
}
v___jp_3008_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_nat_add(v_currRecDepth_2995_, v___x_3009_);
lean_inc_ref(v_inheritedTraceOptions_3007_);
lean_inc(v_cancelTk_x3f_3005_);
lean_inc(v_currMacroScope_3003_);
lean_inc(v_quotContext_3002_);
lean_inc(v_maxHeartbeats_3001_);
lean_inc(v_initHeartbeats_3000_);
lean_inc(v_openDecls_2999_);
lean_inc(v_currNamespace_2998_);
lean_inc(v_ref_2997_);
lean_inc(v_maxRecDepth_2996_);
lean_inc_ref(v_options_2994_);
lean_inc_ref(v_fileMap_2993_);
lean_inc_ref(v_fileName_2992_);
v___x_3011_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3011_, 0, v_fileName_2992_);
lean_ctor_set(v___x_3011_, 1, v_fileMap_2993_);
lean_ctor_set(v___x_3011_, 2, v_options_2994_);
lean_ctor_set(v___x_3011_, 3, v___x_3010_);
lean_ctor_set(v___x_3011_, 4, v_maxRecDepth_2996_);
lean_ctor_set(v___x_3011_, 5, v_ref_2997_);
lean_ctor_set(v___x_3011_, 6, v_currNamespace_2998_);
lean_ctor_set(v___x_3011_, 7, v_openDecls_2999_);
lean_ctor_set(v___x_3011_, 8, v_initHeartbeats_3000_);
lean_ctor_set(v___x_3011_, 9, v_maxHeartbeats_3001_);
lean_ctor_set(v___x_3011_, 10, v_quotContext_3002_);
lean_ctor_set(v___x_3011_, 11, v_currMacroScope_3003_);
lean_ctor_set(v___x_3011_, 12, v_cancelTk_x3f_3005_);
lean_ctor_set(v___x_3011_, 13, v_inheritedTraceOptions_3007_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*14, v_diag_3004_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*14 + 1, v_suppressElabErrors_3006_);
lean_inc_ref(v_x_2984_);
lean_inc(v_a_2990_);
lean_inc_ref(v___x_3011_);
lean_inc(v_a_2988_);
lean_inc_ref(v_a_2987_);
lean_inc(v_mvarId_2985_);
v___x_3012_ = lean_apply_6(v_x_2984_, v_mvarId_2985_, v_a_2987_, v_a_2988_, v___x_3011_, v_a_2990_, lean_box(0));
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3026_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3026_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
if (lean_obj_tag(v_a_3013_) == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
lean_dec_ref_known(v___x_3011_, 14);
lean_dec_ref(v_x_2984_);
v___x_3017_ = lean_st_ref_take(v_a_2986_);
v___x_3018_ = lean_array_push(v___x_3017_, v_mvarId_2985_);
v___x_3019_ = lean_st_ref_set(v_a_2986_, v___x_3018_);
v___x_3020_ = lean_box(0);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3020_);
v___x_3022_ = v___x_3015_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
else
{
lean_object* v_val_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_3015_);
lean_dec(v_mvarId_2985_);
v_val_3024_ = lean_ctor_get(v_a_3013_, 0);
lean_inc(v_val_3024_);
lean_dec_ref_known(v_a_3013_, 1);
v___x_3025_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_2984_, v_val_3024_, v_a_2986_, v_a_2987_, v_a_2988_, v___x_3011_, v_a_2990_);
lean_dec_ref_known(v___x_3011_, 14);
return v___x_3025_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref_known(v___x_3011_, 14);
lean_dec(v_mvarId_2985_);
lean_dec_ref(v_x_2984_);
v_a_3027_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3012_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3012_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3039_, lean_object* v_as_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
if (lean_obj_tag(v_as_3040_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_dec_ref(v_x_3039_);
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
return v___x_3048_;
}
else
{
lean_object* v_head_3049_; lean_object* v_tail_3050_; lean_object* v___x_3051_; 
v_head_3049_ = lean_ctor_get(v_as_3040_, 0);
lean_inc(v_head_3049_);
v_tail_3050_ = lean_ctor_get(v_as_3040_, 1);
lean_inc(v_tail_3050_);
lean_dec_ref_known(v_as_3040_, 2);
lean_inc_ref(v_x_3039_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3039_, v_head_3049_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
v_as_3040_ = v_tail_3050_;
goto _start;
}
else
{
lean_dec(v_tail_3050_);
lean_dec_ref(v_x_3039_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3053_, lean_object* v_as_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3053_, v_as_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3062_, lean_object* v_mvarId_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3062_, v_mvarId_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3071_, lean_object* v_x_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3079_ = lean_st_mk_ref(v___x_3078_);
v___x_3080_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3072_, v_mvarId_3071_, v___x_3079_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3089_; 
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3090_);
v___x_3082_ = v___x_3080_;
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v___x_3080_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3084_ = lean_st_ref_get(v___x_3079_);
lean_dec(v___x_3079_);
v___x_3085_ = lean_array_to_list(v___x_3084_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3085_);
v___x_3087_ = v___x_3082_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v___x_3079_);
v_a_3091_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3080_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3080_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3099_, lean_object* v_x_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_Meta_saturate(v_mvarId_3099_, v_x_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3107_, lean_object* v_msg_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
if (lean_obj_tag(v_mvarIds_3107_) == 1)
{
lean_object* v_tail_3114_; 
v_tail_3114_ = lean_ctor_get(v_mvarIds_3107_, 1);
if (lean_obj_tag(v_tail_3114_) == 0)
{
lean_object* v_head_3115_; lean_object* v___x_3116_; 
lean_dec_ref(v_msg_3108_);
v_head_3115_ = lean_ctor_get(v_mvarIds_3107_, 0);
lean_inc(v_head_3115_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_head_3115_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3117_;
}
}
else
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3119_, lean_object* v_msg_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_exactlyOne(v_mvarIds_3119_, v_msg_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_mvarIds_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3127_, lean_object* v_msg_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
if (lean_obj_tag(v_mvarIds_3127_) == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v_msg_3128_);
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v_tail_3136_; 
v_tail_3136_ = lean_ctor_get(v_mvarIds_3127_, 1);
if (lean_obj_tag(v_tail_3136_) == 0)
{
lean_object* v_head_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
lean_dec_ref(v_msg_3128_);
v_head_3137_ = lean_ctor_get(v_mvarIds_3127_, 0);
lean_inc(v_head_3137_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_head_3137_);
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3141_, lean_object* v_msg_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3141_, v_msg_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_mvarIds_3141_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3149_, size_t v_sz_3150_, size_t v_i_3151_, lean_object* v_b_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_lt(v_i_3151_, v_sz_3150_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_b_3152_);
return v___x_3159_;
}
else
{
lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3190_; 
v_snd_3160_ = lean_ctor_get(v_b_3152_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_b_3152_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_b_3152_, 0);
lean_dec(v_unused_3191_);
v___x_3162_ = v_b_3152_;
v_isShared_3163_ = v_isSharedCheck_3190_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_dec(v_b_3152_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3190_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v_a_3166_; lean_object* v_a_3173_; 
v___x_3164_ = lean_box(0);
v_a_3173_ = lean_array_uget_borrowed(v_as_3149_, v_i_3151_);
if (lean_obj_tag(v_a_3173_) == 0)
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3174_; uint8_t v___x_3175_; 
v_val_3174_ = lean_ctor_get(v_a_3173_, 0);
v___x_3175_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = l_Lean_LocalDecl_type(v_val_3174_);
v___x_3177_ = l_Lean_Meta_isProp(v___x_3176_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; uint8_t v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
v___x_3179_ = lean_unbox(v_a_3178_);
lean_dec(v_a_3178_);
if (v___x_3179_ == 0)
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = l_Lean_LocalDecl_fvarId(v_val_3174_);
v___x_3181_ = lean_array_push(v_snd_3160_, v___x_3180_);
v_a_3166_ = v___x_3181_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3162_);
lean_dec(v_snd_3160_);
v_a_3182_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3177_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3177_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
v_a_3166_ = v_snd_3160_;
goto v___jp_3165_;
}
}
v___jp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v_a_3166_);
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3168_ = v___x_3162_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3166_);
v___x_3168_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
size_t v___x_3169_; size_t v___x_3170_; 
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3151_, v___x_3169_);
v_i_3151_ = v___x_3170_;
v_b_3152_ = v___x_3168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3192_, lean_object* v_sz_3193_, lean_object* v_i_3194_, lean_object* v_b_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
size_t v_sz_boxed_3201_; size_t v_i_boxed_3202_; lean_object* v_res_3203_; 
v_sz_boxed_3201_ = lean_unbox_usize(v_sz_3193_);
lean_dec(v_sz_3193_);
v_i_boxed_3202_ = lean_unbox_usize(v_i_3194_);
lean_dec(v_i_3194_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3192_, v_sz_boxed_3201_, v_i_boxed_3202_, v_b_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v_as_3192_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3204_, size_t v_sz_3205_, size_t v_i_3206_, lean_object* v_b_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_usize_dec_lt(v_i_3206_, v_sz_3205_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_b_3207_);
return v___x_3214_;
}
else
{
lean_object* v_snd_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3245_; 
v_snd_3215_ = lean_ctor_get(v_b_3207_, 1);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_b_3207_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_b_3207_, 0);
lean_dec(v_unused_3246_);
v___x_3217_ = v_b_3207_;
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_snd_3215_);
lean_dec(v_b_3207_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v_a_3221_; lean_object* v_a_3228_; 
v___x_3219_ = lean_box(0);
v_a_3228_ = lean_array_uget_borrowed(v_as_3204_, v_i_3206_);
if (lean_obj_tag(v_a_3228_) == 0)
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
else
{
lean_object* v_val_3229_; uint8_t v___x_3230_; 
v_val_3229_ = lean_ctor_get(v_a_3228_, 0);
v___x_3230_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = l_Lean_LocalDecl_type(v_val_3229_);
v___x_3232_ = l_Lean_Meta_isProp(v___x_3231_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; uint8_t v___x_3234_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = lean_unbox(v_a_3233_);
lean_dec(v_a_3233_);
if (v___x_3234_ == 0)
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = l_Lean_LocalDecl_fvarId(v_val_3229_);
v___x_3236_ = lean_array_push(v_snd_3215_, v___x_3235_);
v_a_3221_ = v___x_3236_;
goto v___jp_3220_;
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_del_object(v___x_3217_);
lean_dec(v_snd_3215_);
v_a_3237_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3232_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3232_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
v_a_3221_ = v_snd_3215_;
goto v___jp_3220_;
}
}
v___jp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v_a_3221_);
lean_ctor_set(v___x_3217_, 0, v___x_3219_);
v___x_3223_ = v___x_3217_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3221_);
v___x_3223_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_add(v_i_3206_, v___x_3224_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3204_, v_sz_3205_, v___x_3225_, v___x_3223_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3247_, lean_object* v_sz_3248_, lean_object* v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3248_);
lean_dec(v_sz_3248_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3247_, v_sz_boxed_3256_, v_i_boxed_3257_, v_b_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_as_3247_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3259_, lean_object* v_n_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
if (lean_obj_tag(v_n_3260_) == 0)
{
lean_object* v_cs_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; size_t v_sz_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v_cs_3267_ = lean_ctor_get(v_n_3260_, 0);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
lean_ctor_set(v___x_3269_, 1, v_b_3261_);
v_sz_3270_ = lean_array_size(v_cs_3267_);
v___x_3271_ = ((size_t)0ULL);
v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3259_, v_cs_3267_, v_sz_3270_, v___x_3271_, v___x_3269_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3287_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3287_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_fst_3277_; 
v_fst_3277_ = lean_ctor_get(v_a_3273_, 0);
if (lean_obj_tag(v_fst_3277_) == 0)
{
lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v_snd_3278_ = lean_ctor_get(v_a_3273_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_a_3273_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v_snd_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3279_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
else
{
lean_object* v_val_3283_; lean_object* v___x_3285_; 
lean_inc_ref(v_fst_3277_);
lean_dec(v_a_3273_);
v_val_3283_ = lean_ctor_get(v_fst_3277_, 0);
lean_inc(v_val_3283_);
lean_dec_ref_known(v_fst_3277_, 1);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v_val_3283_);
v___x_3285_ = v___x_3275_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_val_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3272_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3272_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_vs_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; size_t v_sz_3299_; size_t v___x_3300_; lean_object* v___x_3301_; 
v_vs_3296_ = lean_ctor_get(v_n_3260_, 0);
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v_b_3261_);
v_sz_3299_ = lean_array_size(v_vs_3296_);
v___x_3300_ = ((size_t)0ULL);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3296_, v_sz_3299_, v___x_3300_, v___x_3298_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3316_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3316_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_fst_3306_; 
v_fst_3306_ = lean_ctor_get(v_a_3302_, 0);
if (lean_obj_tag(v_fst_3306_) == 0)
{
lean_object* v_snd_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v_snd_3307_ = lean_ctor_get(v_a_3302_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_a_3302_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_snd_3307_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3308_);
v___x_3310_ = v___x_3304_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
else
{
lean_object* v_val_3312_; lean_object* v___x_3314_; 
lean_inc_ref(v_fst_3306_);
lean_dec(v_a_3302_);
v_val_3312_ = lean_ctor_get(v_fst_3306_, 0);
lean_inc(v_val_3312_);
lean_dec_ref_known(v_fst_3306_, 1);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v_val_3312_);
v___x_3314_ = v___x_3304_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_val_3312_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3301_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3301_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3325_, lean_object* v_as_3326_, size_t v_sz_3327_, size_t v_i_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_lt(v_i_3328_, v_sz_3327_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_b_3329_);
return v___x_3336_;
}
else
{
lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3371_; 
v_snd_3337_ = lean_ctor_get(v_b_3329_, 1);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_b_3329_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v_b_3329_, 0);
lean_dec(v_unused_3372_);
v___x_3339_ = v_b_3329_;
v_isShared_3340_ = v_isSharedCheck_3371_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_dec(v_b_3329_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3371_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_array_uget_borrowed(v_as_3326_, v_i_3328_);
lean_inc(v_snd_3337_);
v___x_3342_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3325_, v_a_3341_, v_snd_3337_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3362_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3362_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3362_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
if (lean_obj_tag(v_a_3343_) == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3343_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3347_);
v___x_3349_ = v___x_3339_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_snd_3337_);
v___x_3349_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3349_);
v___x_3351_ = v___x_3345_;
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
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
lean_del_object(v___x_3345_);
lean_dec(v_snd_3337_);
v_a_3354_ = lean_ctor_get(v_a_3343_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v_a_3343_, 1);
v___x_3355_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v_a_3354_);
lean_ctor_set(v___x_3339_, 0, v___x_3355_);
v___x_3357_ = v___x_3339_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_a_3354_);
v___x_3357_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
size_t v___x_3358_; size_t v___x_3359_; 
v___x_3358_ = ((size_t)1ULL);
v___x_3359_ = lean_usize_add(v_i_3328_, v___x_3358_);
v_i_3328_ = v___x_3359_;
v_b_3329_ = v___x_3357_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_del_object(v___x_3339_);
lean_dec(v_snd_3337_);
v_a_3363_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3342_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3342_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3373_, lean_object* v_as_3374_, lean_object* v_sz_3375_, lean_object* v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
size_t v_sz_boxed_3383_; size_t v_i_boxed_3384_; lean_object* v_res_3385_; 
v_sz_boxed_3383_ = lean_unbox_usize(v_sz_3375_);
lean_dec(v_sz_3375_);
v_i_boxed_3384_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3373_, v_as_3374_, v_sz_boxed_3383_, v_i_boxed_3384_, v_b_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_as_3374_);
lean_dec_ref(v_init_3373_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3386_, lean_object* v_n_3387_, lean_object* v_b_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3386_, v_n_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v_n_3387_);
lean_dec_ref(v_init_3386_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3395_, size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3398_);
return v___x_3405_;
}
else
{
lean_object* v_snd_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3436_; 
v_snd_3406_ = lean_ctor_get(v_b_3398_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_b_3398_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v_b_3398_, 0);
lean_dec(v_unused_3437_);
v___x_3408_ = v_b_3398_;
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_snd_3406_);
lean_dec(v_b_3398_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3436_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v_a_3412_; lean_object* v_a_3419_; 
v___x_3410_ = lean_box(0);
v_a_3419_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
if (lean_obj_tag(v_a_3419_) == 0)
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
else
{
lean_object* v_val_3420_; uint8_t v___x_3421_; 
v_val_3420_ = lean_ctor_get(v_a_3419_, 0);
v___x_3421_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = l_Lean_LocalDecl_type(v_val_3420_);
v___x_3423_ = l_Lean_Meta_isProp(v___x_3422_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; uint8_t v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___x_3425_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
if (v___x_3425_ == 0)
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = l_Lean_LocalDecl_fvarId(v_val_3420_);
v___x_3427_ = lean_array_push(v_snd_3406_, v___x_3426_);
v_a_3412_ = v___x_3427_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_del_object(v___x_3408_);
lean_dec(v_snd_3406_);
v_a_3428_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3423_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3423_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
else
{
v_a_3412_ = v_snd_3406_;
goto v___jp_3411_;
}
}
v___jp_3411_:
{
lean_object* v___x_3414_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 1, v_a_3412_);
lean_ctor_set(v___x_3408_, 0, v___x_3410_);
v___x_3414_ = v___x_3408_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3410_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_a_3412_);
v___x_3414_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
size_t v___x_3415_; size_t v___x_3416_; 
v___x_3415_ = ((size_t)1ULL);
v___x_3416_ = lean_usize_add(v_i_3397_, v___x_3415_);
v_i_3397_ = v___x_3416_;
v_b_3398_ = v___x_3414_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3438_, lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3438_, v_sz_boxed_3447_, v_i_boxed_3448_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_as_3438_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3450_, size_t v_sz_3451_, size_t v_i_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_usize_dec_lt(v_i_3452_, v_sz_3451_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_b_3453_);
return v___x_3460_;
}
else
{
lean_object* v_snd_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3491_; 
v_snd_3461_ = lean_ctor_get(v_b_3453_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_b_3453_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v_b_3453_, 0);
lean_dec(v_unused_3492_);
v___x_3463_ = v_b_3453_;
v_isShared_3464_ = v_isSharedCheck_3491_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_snd_3461_);
lean_dec(v_b_3453_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3491_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v_a_3467_; lean_object* v_a_3474_; 
v___x_3465_ = lean_box(0);
v_a_3474_ = lean_array_uget_borrowed(v_as_3450_, v_i_3452_);
if (lean_obj_tag(v_a_3474_) == 0)
{
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3475_; uint8_t v___x_3476_; 
v_val_3475_ = lean_ctor_get(v_a_3474_, 0);
v___x_3476_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = l_Lean_LocalDecl_type(v_val_3475_);
v___x_3478_ = l_Lean_Meta_isProp(v___x_3477_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; uint8_t v___x_3480_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3478_, 1);
v___x_3480_ = lean_unbox(v_a_3479_);
lean_dec(v_a_3479_);
if (v___x_3480_ == 0)
{
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = l_Lean_LocalDecl_fvarId(v_val_3475_);
v___x_3482_ = lean_array_push(v_snd_3461_, v___x_3481_);
v_a_3467_ = v___x_3482_;
goto v___jp_3466_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_del_object(v___x_3463_);
lean_dec(v_snd_3461_);
v_a_3483_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3478_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3478_);
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
v_a_3467_ = v_snd_3461_;
goto v___jp_3466_;
}
}
v___jp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 1, v_a_3467_);
lean_ctor_set(v___x_3463_, 0, v___x_3465_);
v___x_3469_ = v___x_3463_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_a_3467_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = ((size_t)1ULL);
v___x_3471_ = lean_usize_add(v_i_3452_, v___x_3470_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3450_, v_sz_3451_, v___x_3471_, v___x_3469_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3493_, lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3493_, v_sz_boxed_3502_, v_i_boxed_3503_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_as_3493_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3505_, lean_object* v_init_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_root_3512_; lean_object* v_tail_3513_; lean_object* v___x_3514_; 
v_root_3512_ = lean_ctor_get(v_t_3505_, 0);
v_tail_3513_ = lean_ctor_get(v_t_3505_, 1);
lean_inc_ref(v_init_3506_);
v___x_3514_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3506_, v_root_3512_, v_init_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec_ref(v_init_3506_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3551_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3551_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3551_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
if (lean_obj_tag(v_a_3515_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; 
v_a_3519_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v_a_3515_, 1);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v_a_3519_);
v___x_3521_ = v___x_3517_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; size_t v_sz_3526_; size_t v___x_3527_; lean_object* v___x_3528_; 
lean_del_object(v___x_3517_);
v_a_3523_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v_a_3515_, 1);
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v_a_3523_);
v_sz_3526_ = lean_array_size(v_tail_3513_);
v___x_3527_ = ((size_t)0ULL);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3513_, v_sz_3526_, v___x_3527_, v___x_3525_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3542_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_fst_3533_; 
v_fst_3533_ = lean_ctor_get(v_a_3529_, 0);
if (lean_obj_tag(v_fst_3533_) == 0)
{
lean_object* v_snd_3534_; lean_object* v___x_3536_; 
v_snd_3534_ = lean_ctor_get(v_a_3529_, 1);
lean_inc(v_snd_3534_);
lean_dec(v_a_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_snd_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_snd_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
else
{
lean_object* v_val_3538_; lean_object* v___x_3540_; 
lean_inc_ref(v_fst_3533_);
lean_dec(v_a_3529_);
v_val_3538_ = lean_ctor_get(v_fst_3533_, 0);
lean_inc(v_val_3538_);
lean_dec_ref_known(v_fst_3533_, 1);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_val_3538_);
v___x_3540_ = v___x_3531_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_val_3538_);
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
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3528_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3528_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
v_a_3552_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3514_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3514_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3560_, lean_object* v_init_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3560_, v_init_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v_t_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_lctx_3573_; lean_object* v_decls_3574_; lean_object* v_result_3575_; lean_object* v___x_3576_; 
v_lctx_3573_ = lean_ctor_get(v_a_3568_, 2);
v_decls_3574_ = lean_ctor_get(v_lctx_3573_, 1);
v_result_3575_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3576_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3574_, v_result_3575_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Lean_Meta_getPropHyps(v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3582_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3587_ = l_Lean_MessageData_ofFormat(v___x_3586_);
return v___x_3587_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3590_, lean_object* v___x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
lean_inc(v___x_3591_);
lean_inc(v_mvarId_3590_);
v___x_3597_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3590_, v___x_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3598_; 
lean_dec_ref_known(v___x_3597_, 1);
lean_inc(v_mvarId_3590_);
v___x_3598_ = l_Lean_MVarId_getType(v_mvarId_3590_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_Lean_Meta_synthInstance(v_a_3599_, v___x_3600_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
lean_inc(v_mvarId_3590_);
v___x_3603_ = l_Lean_mkMVar(v_mvarId_3590_);
v___x_3604_ = l_Lean_Meta_isExprDefEq(v___x_3603_, v_a_3602_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3616_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3616_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3616_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
uint8_t v___x_3609_; 
v___x_3609_ = lean_unbox(v_a_3605_);
lean_dec(v_a_3605_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_del_object(v___x_3607_);
v___x_3610_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3611_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3591_, v_mvarId_3590_, v___x_3610_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v___x_3612_ = lean_box(0);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3612_);
v___x_3614_ = v___x_3607_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3617_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3604_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3604_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3625_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3601_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3601_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
v_a_3633_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3598_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3598_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_dec(v___x_3591_);
lean_dec(v_mvarId_3590_);
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3641_, lean_object* v___x_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3641_, v___x_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3652_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3659_, 0, v_mvarId_3652_);
lean_closure_set(v___f_3659_, 1, v___x_3658_);
v___x_3660_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3652_, v___f_3659_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_MVarId_inferInstance(v_mvarId_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx(lean_object* v_x_3668_){
_start:
{
switch(lean_obj_tag(v_x_3668_))
{
case 0:
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_unsigned_to_nat(0u);
return v___x_3669_;
}
case 1:
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(1u);
return v___x_3670_;
}
default: 
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_unsigned_to_nat(2u);
return v___x_3671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(lean_object* v_x_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_3672_);
lean_dec(v_x_3672_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3674_, lean_object* v_k_3675_){
_start:
{
if (lean_obj_tag(v_t_3674_) == 2)
{
lean_object* v_mvarId_3676_; lean_object* v___x_3677_; 
v_mvarId_3676_ = lean_ctor_get(v_t_3674_, 0);
lean_inc(v_mvarId_3676_);
lean_dec_ref_known(v_t_3674_, 1);
v___x_3677_ = lean_apply_1(v_k_3675_, v_mvarId_3676_);
return v___x_3677_;
}
else
{
lean_dec(v_t_3674_);
return v_k_3675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3678_, lean_object* v_ctorIdx_3679_, lean_object* v_t_3680_, lean_object* v_h_3681_, lean_object* v_k_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3680_, v_k_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3684_, lean_object* v_ctorIdx_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_, lean_object* v_k_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3684_, v_ctorIdx_3685_, v_t_3686_, v_h_3687_, v_k_3688_);
lean_dec(v_ctorIdx_3685_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3690_, lean_object* v_closed_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3690_, v_closed_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3693_, lean_object* v_t_3694_, lean_object* v_h_3695_, lean_object* v_closed_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3694_, v_closed_3696_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3698_, lean_object* v_noChange_3699_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3698_, v_noChange_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3701_, lean_object* v_t_3702_, lean_object* v_h_3703_, lean_object* v_noChange_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3702_, v_noChange_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3706_, lean_object* v_modified_3707_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3706_, v_modified_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3709_, lean_object* v_t_3710_, lean_object* v_h_3711_, lean_object* v_modified_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3710_, v_modified_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v_a_3730_; lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_MVarId_getType(v_g_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = lean_mk_empty_array_with_capacity(v___x_3736_);
v___x_3738_ = lean_array_push(v___x_3737_, v_a_3734_);
v___x_3739_ = l_Lean_Meta_mkAppM(v___x_3735_, v___x_3738_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = lean_box(0);
v___x_3742_ = l_Lean_Meta_synthInstance(v_a_3740_, v___x_3741_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3751_; 
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; 
v_unused_3752_ = lean_ctor_get(v___x_3742_, 0);
lean_dec(v_unused_3752_);
v___x_3744_ = v___x_3742_;
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v___x_3742_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3751_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
uint8_t v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3746_ = 1;
v___x_3747_ = lean_box(v___x_3746_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3747_);
v___x_3749_ = v___x_3744_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
else
{
lean_object* v_a_3753_; 
v_a_3753_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3742_, 1);
v_a_3730_ = v_a_3753_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3754_; 
v_a_3754_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3739_, 1);
v_a_3730_ = v_a_3754_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3755_; 
v_a_3755_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3733_, 1);
v_a_3730_ = v_a_3755_;
goto v___jp_3729_;
}
v___jp_3723_:
{
if (v___y_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
lean_dec_ref(v___y_3724_);
v___x_3726_ = lean_box(v___y_3725_);
v___x_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
return v___x_3727_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___y_3724_);
return v___x_3728_;
}
}
v___jp_3729_:
{
uint8_t v___x_3731_; 
v___x_3731_ = l_Lean_Exception_isInterrupt(v_a_3730_);
if (v___x_3731_ == 0)
{
uint8_t v___x_3732_; 
lean_inc_ref(v_a_3730_);
v___x_3732_ = l_Lean_Exception_isRuntime(v_a_3730_);
v___y_3724_ = v_a_3730_;
v___y_3725_ = v___x_3732_;
goto v___jp_3723_;
}
else
{
v___y_3724_ = v_a_3730_;
v___y_3725_ = v___x_3731_;
goto v___jp_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_MVarId_isSubsingleton(v_g_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3783_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3780_, v___x_3781_, v___x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3785_;
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
