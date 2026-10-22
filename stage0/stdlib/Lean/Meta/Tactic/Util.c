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
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object*);
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
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_box(0);
v___x_104_ = l_Lean_MetavarContext_setMVarUserName(v_mctx_95_, v_mvarId_90_, v_tag_91_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v_cache_96_);
lean_ctor_set(v_reuseFailAlloc_109_, 2, v_zetaDeltaFVarIds_97_);
lean_ctor_set(v_reuseFailAlloc_109_, 3, v_postponed_98_);
lean_ctor_set(v_reuseFailAlloc_109_, 4, v_diag_99_);
v___x_106_ = v_reuseFailAlloc_109_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_st_ref_put(v_a_92_, v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_103_);
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
lean_object* v___x_233_; lean_object* v_env_234_; uint8_t v___x_235_; lean_object* v_env_236_; lean_object* v___x_237_; lean_object* v_toCold_238_; lean_object* v_mctx_239_; lean_object* v_lctx_240_; lean_object* v_options_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_234_);
lean_dec(v___x_233_);
v___x_235_ = 0;
v_env_236_ = l_Lean_Environment_setRecordingDeps(v_env_234_, v___x_235_);
v___x_237_ = lean_st_ref_get(v___y_229_);
v_toCold_238_ = lean_ctor_get(v___y_230_, 0);
v_mctx_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc_ref(v_mctx_239_);
lean_dec(v___x_237_);
v_lctx_240_ = lean_ctor_get(v___y_228_, 2);
v_options_241_ = lean_ctor_get(v_toCold_238_, 2);
lean_inc_ref(v_options_241_);
lean_inc_ref(v_lctx_240_);
v___x_242_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_242_, 0, v_env_236_);
lean_ctor_set(v___x_242_, 1, v_mctx_239_);
lean_ctor_set(v___x_242_, 2, v_lctx_240_);
lean_ctor_set(v___x_242_, 3, v_options_241_);
v___x_243_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_msgData_227_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(lean_object* v_msgData_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_ref_258_; lean_object* v___x_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_ref_258_ = lean_ctor_get(v___y_255_, 2);
v___x_259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_inc(v_ref_258_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_ref_258_);
lean_ctor_set(v___x_264_, 1, v_a_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 1);
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_Meta_throwTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_throwTacticEx___redArg___closed__0));
v___x_278_ = l_Lean_stringToMessageData(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object* v_tacticName_279_, lean_object* v_mvarId_280_, lean_object* v_msg_x3f_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
if (lean_obj_tag(v_msg_x3f_281_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_287_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_288_ = l_Lean_MessageData_ofName(v_tacticName_279_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Meta_throwTacticEx___redArg___closed__1, &l_Lean_Meta_throwTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwTacticEx___redArg___closed__1);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_mvarId_280_);
v___x_293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_293_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_294_;
}
else
{
lean_object* v_val_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_val_295_ = lean_ctor_get(v_msg_x3f_281_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v_msg_x3f_281_, 1);
v___x_296_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_279_, v_mvarId_280_, v_val_295_);
v___x_297_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_296_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___redArg___boxed(lean_object* v_tacticName_298_, lean_object* v_mvarId_299_, lean_object* v_msg_x3f_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_298_, v_mvarId_299_, v_msg_x3f_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx(lean_object* v_00_u03b1_307_, lean_object* v_tacticName_308_, lean_object* v_mvarId_309_, lean_object* v_msg_x3f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_308_, v_mvarId_309_, v_msg_x3f_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTacticEx___boxed(lean_object* v_00_u03b1_317_, lean_object* v_tacticName_318_, lean_object* v_mvarId_319_, lean_object* v_msg_x3f_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_throwTacticEx(v_00_u03b1_317_, v_tacticName_318_, v_mvarId_319_, v_msg_x3f_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(lean_object* v_00_u03b1_327_, lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(lean_object* v_00_u03b1_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(v_00_u03b1_335_, v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0));
v___x_345_ = l_Lean_stringToMessageData(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg(lean_object* v_tacticName_349_, lean_object* v_ex_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_nestedMsg_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_msg_362_; lean_object* v_kind_363_; uint8_t v___x_364_; 
v_nestedMsg_356_ = l_Lean_Exception_toMessageData(v_ex_350_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_mkTacticExMsg___closed__1, &l_Lean_Meta_mkTacticExMsg___closed__1_once, _init_l_Lean_Meta_mkTacticExMsg___closed__1);
v___x_358_ = l_Lean_MessageData_ofName(v_tacticName_349_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_Meta_throwNestedTacticEx___redArg___closed__1, &l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once, _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_inc_ref(v_nestedMsg_356_);
v_msg_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_362_, 0, v___x_361_);
lean_ctor_set(v_msg_362_, 1, v_nestedMsg_356_);
v_kind_363_ = l_Lean_MessageData_kind(v_nestedMsg_356_);
lean_dec_ref(v_nestedMsg_356_);
v___x_364_ = l_Lean_Name_isAnonymous(v_kind_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = ((lean_object*)(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3));
v___x_366_ = l_Lean_Name_append(v___x_365_, v_kind_363_);
v___x_367_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_msg_362_);
v___x_368_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v___x_367_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_368_;
}
else
{
lean_object* v___x_369_; 
lean_dec(v_kind_363_);
v___x_369_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_362_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___redArg___boxed(lean_object* v_tacticName_370_, lean_object* v_ex_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_370_, v_ex_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx(lean_object* v_00_u03b1_378_, lean_object* v_tacticName_379_, lean_object* v_ex_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_throwNestedTacticEx___redArg(v_tacticName_379_, v_ex_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwNestedTacticEx___boxed(lean_object* v_00_u03b1_387_, lean_object* v_tacticName_388_, lean_object* v_ex_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_throwNestedTacticEx(v_00_u03b1_387_, v_tacticName_388_, v_ex_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
return v_res_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_396_, lean_object* v_i_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_array_get_size(v_keys_396_);
v___x_400_ = lean_nat_dec_lt(v_i_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v_i_397_);
return v___x_400_;
}
else
{
lean_object* v_k_x27_401_; uint8_t v___x_402_; 
v_k_x27_401_ = lean_array_fget_borrowed(v_keys_396_, v_i_397_);
v___x_402_ = l_Lean_instBEqMVarId_beq(v_k_398_, v_k_x27_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_397_, v___x_403_);
lean_dec(v_i_397_);
v_i_397_ = v___x_404_;
goto _start;
}
else
{
lean_dec(v_i_397_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_406_, v_i_407_, v_k_408_);
lean_dec(v_k_408_);
lean_dec_ref(v_keys_406_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(lean_object* v_x_411_, size_t v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v_es_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_j_418_; lean_object* v___x_419_; 
v_es_414_ = lean_ctor_get(v_x_411_, 0);
v___x_415_ = lean_box(2);
v___x_416_ = ((size_t)31ULL);
v___x_417_ = lean_usize_land(v_x_412_, v___x_416_);
v_j_418_ = lean_usize_to_nat(v___x_417_);
v___x_419_ = lean_array_get_borrowed(v___x_415_, v_es_414_, v_j_418_);
lean_dec(v_j_418_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_key_420_; uint8_t v___x_421_; 
v_key_420_ = lean_ctor_get(v___x_419_, 0);
v___x_421_ = l_Lean_instBEqMVarId_beq(v_x_413_, v_key_420_);
return v___x_421_;
}
case 1:
{
lean_object* v_node_422_; size_t v___x_423_; size_t v___x_424_; 
v_node_422_ = lean_ctor_get(v___x_419_, 0);
v___x_423_ = ((size_t)5ULL);
v___x_424_ = lean_usize_shift_right(v_x_412_, v___x_423_);
v_x_411_ = v_node_422_;
v_x_412_ = v___x_424_;
goto _start;
}
default: 
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_ks_427_ = lean_ctor_get(v_x_411_, 0);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_427_, v___x_428_, v_x_413_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_546__boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_x_546__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_430_, v_x_546__boxed_433_, v_x_432_);
lean_dec(v_x_432_);
lean_dec_ref(v_x_430_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = l_Lean_instHashableMVarId_hash(v_x_437_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_436_, v___x_439_, v_x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_441_, v_x_442_);
lean_dec(v_x_442_);
lean_dec_ref(v_x_441_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(lean_object* v_mvarId_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_mctx_449_; lean_object* v_eAssignment_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = lean_st_ref_get(v___y_446_);
v_mctx_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_mctx_449_);
lean_dec(v___x_448_);
v_eAssignment_450_ = lean_ctor_get(v_mctx_449_, 8);
lean_inc_ref(v_eAssignment_450_);
lean_dec_ref(v_mctx_449_);
v___x_451_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_450_, v_mvarId_445_);
lean_dec_ref(v_eAssignment_450_);
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(lean_object* v_mvarId_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec(v_mvarId_454_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__4(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_MVarId_checkNotAssigned___closed__3));
v___x_465_ = l_Lean_MessageData_ofFormat(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__5(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__4, &l_Lean_MVarId_checkNotAssigned___closed__4_once, _init_l_Lean_MVarId_checkNotAssigned___closed__4);
v___x_467_ = l_Lean_MessageData_note(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__6(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__5, &l_Lean_MVarId_checkNotAssigned___closed__5_once, _init_l_Lean_MVarId_checkNotAssigned___closed__5);
v___x_469_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__1, &l_Lean_MVarId_checkNotAssigned___closed__1_once, _init_l_Lean_MVarId_checkNotAssigned___closed__1);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_MVarId_checkNotAssigned___closed__7(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__6, &l_Lean_MVarId_checkNotAssigned___closed__6_once, _init_l_Lean_MVarId_checkNotAssigned___closed__6);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned(lean_object* v_mvarId_473_, lean_object* v_tacticName_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_492_; 
v___x_480_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_473_, v_a_476_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_492_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_492_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = lean_unbox(v_a_481_);
lean_dec(v_a_481_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec(v_tacticName_474_);
lean_dec(v_mvarId_473_);
v___x_486_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_del_object(v___x_483_);
v___x_490_ = lean_obj_once(&l_Lean_MVarId_checkNotAssigned___closed__7, &l_Lean_MVarId_checkNotAssigned___closed__7_once, _init_l_Lean_MVarId_checkNotAssigned___closed__7);
v___x_491_ = l_Lean_Meta_throwTacticEx___redArg(v_tacticName_474_, v_mvarId_473_, v___x_490_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkNotAssigned___boxed(lean_object* v_mvarId_493_, lean_object* v_tacticName_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_493_, v_tacticName_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(lean_object* v_mvarId_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(v_mvarId_501_, v___y_503_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(lean_object* v_mvarId_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(v_mvarId_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v_mvarId_508_);
return v_res_514_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(lean_object* v_00_u03b2_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(lean_object* v_00_u03b2_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_519_, v_x_520_, v_x_521_);
lean_dec(v_x_521_);
lean_dec_ref(v_x_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_524_, lean_object* v_x_525_, size_t v_x_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_525_, v_x_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_713__boxed_533_; uint8_t v_res_534_; lean_object* v_r_535_; 
v_x_713__boxed_533_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_534_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_529_, v_x_530_, v_x_713__boxed_533_, v_x_532_);
lean_dec(v_x_532_);
lean_dec_ref(v_x_530_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_536_, lean_object* v_keys_537_, lean_object* v_vals_538_, lean_object* v_heq_539_, lean_object* v_i_540_, lean_object* v_k_541_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_537_, v_i_540_, v_k_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_543_, lean_object* v_keys_544_, lean_object* v_vals_545_, lean_object* v_heq_546_, lean_object* v_i_547_, lean_object* v_k_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_543_, v_keys_544_, v_vals_545_, v_heq_546_, v_i_547_, v_k_548_);
lean_dec(v_k_548_);
lean_dec_ref(v_vals_545_);
lean_dec_ref(v_keys_544_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType(lean_object* v_mvarId_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_MVarId_getDecl(v_mvarId_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_566_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_type_562_; lean_object* v___x_564_; 
v_type_562_ = lean_ctor_get(v_a_558_, 2);
lean_inc_ref(v_type_562_);
lean_dec(v_a_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v_type_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_type_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
v_a_567_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_557_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_557_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType___boxed(lean_object* v_mvarId_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_MVarId_getType(v_mvarId_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(lean_object* v_e_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = l_Lean_Expr_hasMVar(v_e_582_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v_e_582_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v_mctx_588_; lean_object* v___x_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; lean_object* v_cache_593_; lean_object* v_zetaDeltaFVarIds_594_; lean_object* v_postponed_595_; lean_object* v_diag_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_605_; 
v___x_587_ = lean_st_ref_get(v___y_583_);
v_mctx_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_mctx_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_instantiateMVarsCore(v_mctx_588_, v_e_582_);
v_fst_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v___x_589_, 1);
lean_inc(v_snd_591_);
lean_dec_ref(v___x_589_);
v___x_592_ = lean_st_ref_take(v___y_583_);
v_cache_593_ = lean_ctor_get(v___x_592_, 1);
v_zetaDeltaFVarIds_594_ = lean_ctor_get(v___x_592_, 2);
v_postponed_595_ = lean_ctor_get(v___x_592_, 3);
v_diag_596_ = lean_ctor_get(v___x_592_, 4);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_606_);
v___x_598_ = v___x_592_;
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_diag_596_);
lean_inc(v_postponed_595_);
lean_inc(v_zetaDeltaFVarIds_594_);
lean_inc(v_cache_593_);
lean_dec(v___x_592_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_605_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_snd_591_);
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_snd_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_zetaDeltaFVarIds_594_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_postponed_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v_diag_596_);
v___x_601_ = v_reuseFailAlloc_604_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_st_ref_put(v___y_583_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_fst_590_);
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(lean_object* v_e_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_607_, v___y_608_);
lean_dec(v___y_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(lean_object* v_e_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_611_, v___y_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(lean_object* v_e_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(v_e_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27(lean_object* v_mvarId_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_MVarId_getType(v_mvarId_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
lean_inc(v_a_629_);
lean_inc_ref(v_a_628_);
lean_inc(v_a_627_);
lean_inc_ref(v_a_626_);
v___x_633_ = lean_whnf(v_a_632_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_634_, v_a_627_);
return v___x_635_;
}
else
{
return v___x_633_;
}
}
else
{
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getType_x27___boxed(lean_object* v_mvarId_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_MVarId_getType_x27(v_mvarId_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_709_ = 0;
v___x_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_));
v___x_711_ = l_Lean_registerTraceClass(v___x_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(lean_object* v_mvarId_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_721_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_721_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(lean_object* v_mvarId_738_, lean_object* v_x_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_738_, v_x_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(lean_object* v_00_u03b1_746_, lean_object* v_mvarId_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_747_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(lean_object* v_00_u03b1_755_, lean_object* v_mvarId_756_, lean_object* v_x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(v_00_u03b1_755_, v_mvarId_756_, v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_ks_768_; lean_object* v_vs_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_793_; 
v_ks_768_ = lean_ctor_get(v_x_764_, 0);
v_vs_769_ = lean_ctor_get(v_x_764_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_793_ == 0)
{
v___x_771_ = v_x_764_;
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_vs_769_);
lean_inc(v_ks_768_);
lean_dec(v_x_764_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_793_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_array_get_size(v_ks_768_);
v___x_774_ = lean_nat_dec_lt(v_x_765_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec(v_x_765_);
v___x_775_ = lean_array_push(v_ks_768_, v_x_766_);
v___x_776_ = lean_array_push(v_vs_769_, v_x_767_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_776_);
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_778_ = v___x_771_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
else
{
lean_object* v_k_x27_780_; uint8_t v___x_781_; 
v_k_x27_780_ = lean_array_fget_borrowed(v_ks_768_, v_x_765_);
v___x_781_ = l_Lean_instBEqMVarId_beq(v_x_766_, v_k_x27_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_783_; 
if (v_isShared_772_ == 0)
{
v___x_783_ = v___x_771_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_ks_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_vs_769_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_add(v_x_765_, v___x_784_);
lean_dec(v_x_765_);
v_x_764_ = v___x_783_;
v_x_765_ = v___x_785_;
goto _start;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_788_ = lean_array_fset(v_ks_768_, v_x_765_, v_x_766_);
v___x_789_ = lean_array_fset(v_vs_769_, v_x_765_, v_x_767_);
lean_dec(v_x_765_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_789_);
lean_ctor_set(v___x_771_, 0, v___x_788_);
v___x_791_ = v___x_771_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v___x_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_n_794_, lean_object* v_k_795_, lean_object* v_v_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_794_, v___x_797_, v_k_795_, v_v_796_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(lean_object* v_x_800_, size_t v_x_801_, size_t v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_800_) == 0)
{
lean_object* v_es_805_; size_t v___x_806_; size_t v___x_807_; lean_object* v_j_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_es_805_ = lean_ctor_get(v_x_800_, 0);
v___x_806_ = ((size_t)31ULL);
v___x_807_ = lean_usize_land(v_x_801_, v___x_806_);
v_j_808_ = lean_usize_to_nat(v___x_807_);
v___x_809_ = lean_array_get_size(v_es_805_);
v___x_810_ = lean_nat_dec_lt(v_j_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_dec(v_j_808_);
lean_dec(v_x_804_);
lean_dec(v_x_803_);
return v_x_800_;
}
else
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_849_; 
lean_inc_ref(v_es_805_);
v_isSharedCheck_849_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_x_800_, 0);
lean_dec(v_unused_850_);
v___x_812_ = v_x_800_;
v_isShared_813_ = v_isSharedCheck_849_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_x_800_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_849_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v_xs_x27_816_; lean_object* v___y_818_; 
v_v_814_ = lean_array_fget(v_es_805_, v_j_808_);
v___x_815_ = lean_box(0);
v_xs_x27_816_ = lean_array_fset(v_es_805_, v_j_808_, v___x_815_);
switch(lean_obj_tag(v_v_814_))
{
case 0:
{
lean_object* v_key_823_; lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_key_823_ = lean_ctor_get(v_v_814_, 0);
v_val_824_ = lean_ctor_get(v_v_814_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_v_814_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_v_814_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_inc(v_key_823_);
lean_dec(v_v_814_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___x_828_; 
v___x_828_ = l_Lean_instBEqMVarId_beq(v_x_803_, v_key_823_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_826_);
v___x_829_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_823_, v_val_824_, v_x_803_, v_x_804_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
v___y_818_ = v___x_830_;
goto v___jp_817_;
}
else
{
lean_object* v___x_832_; 
lean_dec(v_val_824_);
lean_dec(v_key_823_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_x_804_);
lean_ctor_set(v___x_826_, 0, v_x_803_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_x_803_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_x_804_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v___y_818_ = v___x_832_;
goto v___jp_817_;
}
}
}
}
case 1:
{
lean_object* v_node_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_847_; 
v_node_835_ = lean_ctor_get(v_v_814_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_v_814_);
if (v_isSharedCheck_847_ == 0)
{
v___x_837_ = v_v_814_;
v_isShared_838_ = v_isSharedCheck_847_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_node_835_);
lean_dec(v_v_814_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_847_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_839_ = ((size_t)5ULL);
v___x_840_ = lean_usize_shift_right(v_x_801_, v___x_839_);
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_x_802_, v___x_841_);
v___x_843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_835_, v___x_840_, v___x_842_, v_x_803_, v_x_804_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_843_);
v___x_845_ = v___x_837_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_818_ = v___x_845_;
goto v___jp_817_;
}
}
}
default: 
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_x_803_);
lean_ctor_set(v___x_848_, 1, v_x_804_);
v___y_818_ = v___x_848_;
goto v___jp_817_;
}
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = lean_array_fset(v_xs_x27_816_, v_j_808_, v___y_818_);
lean_dec(v_j_808_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
else
{
lean_object* v_ks_851_; lean_object* v_vs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_870_; 
v_ks_851_ = lean_ctor_get(v_x_800_, 0);
v_vs_852_ = lean_ctor_get(v_x_800_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_800_);
if (v_isSharedCheck_870_ == 0)
{
v___x_854_ = v_x_800_;
v_isShared_855_ = v_isSharedCheck_870_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_vs_852_);
lean_inc(v_ks_851_);
lean_dec(v_x_800_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_870_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_ks_851_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_vs_852_);
v___x_857_ = v_reuseFailAlloc_869_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v_newNode_858_; size_t v___x_859_; uint8_t v___x_860_; 
v_newNode_858_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_857_, v_x_803_, v_x_804_);
v___x_859_ = ((size_t)7ULL);
v___x_860_ = lean_usize_dec_le(v___x_859_, v_x_802_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_858_);
v___x_862_ = lean_unsigned_to_nat(4u);
v___x_863_ = lean_nat_dec_lt(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
if (v___x_863_ == 0)
{
lean_object* v_ks_864_; lean_object* v_vs_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_ks_864_ = lean_ctor_get(v_newNode_858_, 0);
lean_inc_ref(v_ks_864_);
v_vs_865_ = lean_ctor_get(v_newNode_858_, 1);
lean_inc_ref(v_vs_865_);
lean_dec_ref(v_newNode_858_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_802_, v_ks_864_, v_vs_865_, v___x_866_, v___x_867_);
lean_dec_ref(v_vs_865_);
lean_dec_ref(v_ks_864_);
return v___x_868_;
}
else
{
return v_newNode_858_;
}
}
else
{
return v_newNode_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(size_t v_depth_871_, lean_object* v_keys_872_, lean_object* v_vals_873_, lean_object* v_i_874_, lean_object* v_entries_875_){
_start:
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_array_get_size(v_keys_872_);
v___x_877_ = lean_nat_dec_lt(v_i_874_, v___x_876_);
if (v___x_877_ == 0)
{
lean_dec(v_i_874_);
return v_entries_875_;
}
else
{
lean_object* v_k_878_; lean_object* v_v_879_; uint64_t v___x_880_; size_t v_h_881_; size_t v___x_882_; lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; size_t v___x_886_; size_t v_h_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_k_878_ = lean_array_fget_borrowed(v_keys_872_, v_i_874_);
v_v_879_ = lean_array_fget_borrowed(v_vals_873_, v_i_874_);
v___x_880_ = l_Lean_instHashableMVarId_hash(v_k_878_);
v_h_881_ = lean_uint64_to_usize(v___x_880_);
v___x_882_ = ((size_t)5ULL);
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_sub(v_depth_871_, v___x_884_);
v___x_886_ = lean_usize_mul(v___x_882_, v___x_885_);
v_h_887_ = lean_usize_shift_right(v_h_881_, v___x_886_);
v___x_888_ = lean_nat_add(v_i_874_, v___x_883_);
lean_dec(v_i_874_);
lean_inc(v_v_879_);
lean_inc(v_k_878_);
v___x_889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_875_, v_h_887_, v_depth_871_, v_k_878_, v_v_879_);
v_i_874_ = v___x_888_;
v_entries_875_ = v___x_889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_depth_891_, lean_object* v_keys_892_, lean_object* v_vals_893_, lean_object* v_i_894_, lean_object* v_entries_895_){
_start:
{
size_t v_depth_boxed_896_; lean_object* v_res_897_; 
v_depth_boxed_896_ = lean_unbox_usize(v_depth_891_);
lean_dec(v_depth_891_);
v_res_897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_896_, v_keys_892_, v_vals_893_, v_i_894_, v_entries_895_);
lean_dec_ref(v_vals_893_);
lean_dec_ref(v_keys_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_){
_start:
{
size_t v_x_1018__boxed_903_; size_t v_x_1019__boxed_904_; lean_object* v_res_905_; 
v_x_1018__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_x_1019__boxed_904_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_898_, v_x_1018__boxed_903_, v_x_1019__boxed_904_, v_x_901_, v_x_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
uint64_t v___x_909_; size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
v___x_909_ = l_Lean_instHashableMVarId_hash(v_x_907_);
v___x_910_ = lean_uint64_to_usize(v___x_909_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_906_, v___x_910_, v___x_911_, v_x_907_, v_x_908_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(lean_object* v_mvarId_913_, lean_object* v_val_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v_cache_919_; lean_object* v_zetaDeltaFVarIds_920_; lean_object* v_postponed_921_; lean_object* v_diag_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_951_; 
v___x_917_ = lean_st_ref_take(v___y_915_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
v_cache_919_ = lean_ctor_get(v___x_917_, 1);
v_zetaDeltaFVarIds_920_ = lean_ctor_get(v___x_917_, 2);
v_postponed_921_ = lean_ctor_get(v___x_917_, 3);
v_diag_922_ = lean_ctor_get(v___x_917_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_951_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_diag_922_);
lean_inc(v_postponed_921_);
lean_inc(v_zetaDeltaFVarIds_920_);
lean_inc(v_cache_919_);
lean_inc(v_mctx_918_);
lean_dec(v___x_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_depth_926_; lean_object* v_levelAssignDepth_927_; lean_object* v_lmvarCounter_928_; lean_object* v_mvarCounter_929_; lean_object* v_lDecls_930_; lean_object* v_decls_931_; lean_object* v_userNames_932_; lean_object* v_lAssignment_933_; lean_object* v_eAssignment_934_; lean_object* v_dAssignment_935_; lean_object* v_synthNormMemo_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_950_; 
v_depth_926_ = lean_ctor_get(v_mctx_918_, 0);
v_levelAssignDepth_927_ = lean_ctor_get(v_mctx_918_, 1);
v_lmvarCounter_928_ = lean_ctor_get(v_mctx_918_, 2);
v_mvarCounter_929_ = lean_ctor_get(v_mctx_918_, 3);
v_lDecls_930_ = lean_ctor_get(v_mctx_918_, 4);
v_decls_931_ = lean_ctor_get(v_mctx_918_, 5);
v_userNames_932_ = lean_ctor_get(v_mctx_918_, 6);
v_lAssignment_933_ = lean_ctor_get(v_mctx_918_, 7);
v_eAssignment_934_ = lean_ctor_get(v_mctx_918_, 8);
v_dAssignment_935_ = lean_ctor_get(v_mctx_918_, 9);
v_synthNormMemo_936_ = lean_ctor_get(v_mctx_918_, 10);
v_isSharedCheck_950_ = !lean_is_exclusive(v_mctx_918_);
if (v_isSharedCheck_950_ == 0)
{
v___x_938_ = v_mctx_918_;
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_synthNormMemo_936_);
lean_inc(v_dAssignment_935_);
lean_inc(v_eAssignment_934_);
lean_inc(v_lAssignment_933_);
lean_inc(v_userNames_932_);
lean_inc(v_decls_931_);
lean_inc(v_lDecls_930_);
lean_inc(v_mvarCounter_929_);
lean_inc(v_lmvarCounter_928_);
lean_inc(v_levelAssignDepth_927_);
lean_inc(v_depth_926_);
lean_dec(v_mctx_918_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_950_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_box(0);
v___x_941_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_934_, v_mvarId_913_, v_val_914_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 8, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_depth_926_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_levelAssignDepth_927_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_lmvarCounter_928_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_mvarCounter_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_lDecls_930_);
lean_ctor_set(v_reuseFailAlloc_949_, 5, v_decls_931_);
lean_ctor_set(v_reuseFailAlloc_949_, 6, v_userNames_932_);
lean_ctor_set(v_reuseFailAlloc_949_, 7, v_lAssignment_933_);
lean_ctor_set(v_reuseFailAlloc_949_, 8, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_949_, 9, v_dAssignment_935_);
lean_ctor_set(v_reuseFailAlloc_949_, 10, v_synthNormMemo_936_);
v___x_943_ = v_reuseFailAlloc_949_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_943_);
v___x_945_ = v___x_924_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_cache_919_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_zetaDeltaFVarIds_920_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_postponed_921_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_diag_922_);
v___x_945_ = v_reuseFailAlloc_948_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_st_ref_put(v___y_915_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_940_);
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_952_, lean_object* v_val_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_952_, v_val_953_, v___y_954_);
lean_dec(v___y_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_957_, lean_object* v___x_958_, uint8_t v_synthetic_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
lean_inc(v_mvarId_957_);
v___x_965_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_957_, v___x_958_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_966_; 
lean_dec_ref_known(v___x_965_, 1);
lean_inc(v_mvarId_957_);
v___x_966_ = l_Lean_MVarId_getType(v_mvarId_957_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = 1;
v___x_969_ = l_Lean_Meta_mkLabeledSorry(v_a_967_, v_synthetic_959_, v___x_968_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_957_, v_a_970_, v___y_961_);
return v___x_971_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_mvarId_957_);
v_a_972_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_969_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_mvarId_957_);
v_a_980_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_966_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_966_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_dec(v_mvarId_957_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_988_, lean_object* v___x_989_, lean_object* v_synthetic_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v_synthetic_boxed_996_; lean_object* v_res_997_; 
v_synthetic_boxed_996_ = lean_unbox(v_synthetic_990_);
v_res_997_ = l_Lean_MVarId_admit___lam__0(v_mvarId_988_, v___x_989_, v_synthetic_boxed_996_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1001_, uint8_t v_synthetic_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; 
v___x_1008_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1009_ = lean_box(v_synthetic_1002_);
lean_inc(v_mvarId_1001_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1010_, 0, v_mvarId_1001_);
lean_closure_set(v___f_1010_, 1, v___x_1008_);
lean_closure_set(v___f_1010_, 2, v___x_1009_);
v___x_1011_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1001_, v___f_1010_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1012_, lean_object* v_synthetic_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
uint8_t v_synthetic_boxed_1019_; lean_object* v_res_1020_; 
v_synthetic_boxed_1019_ = lean_unbox(v_synthetic_1013_);
v_res_1020_ = l_Lean_MVarId_admit(v_mvarId_1012_, v_synthetic_boxed_1019_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1021_, lean_object* v_val_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1021_, v_val_1022_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1029_, lean_object* v_val_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1029_, v_val_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1038_, v_x_1039_, v_x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, size_t v_x_1044_, size_t v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
size_t v_x_1339__boxed_1055_; size_t v_x_1340__boxed_1056_; lean_object* v_res_1057_; 
v_x_1339__boxed_1055_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_x_1340__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1049_, v_x_1050_, v_x_1339__boxed_1055_, v_x_1340__boxed_1056_, v_x_1053_, v_x_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1058_, lean_object* v_n_1059_, lean_object* v_k_1060_, lean_object* v_v_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1059_, v_k_1060_, v_v_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1063_, size_t v_depth_1064_, lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_heq_1067_, lean_object* v_i_1068_, lean_object* v_entries_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1064_, v_keys_1065_, v_vals_1066_, v_i_1068_, v_entries_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_depth_1072_, lean_object* v_keys_1073_, lean_object* v_vals_1074_, lean_object* v_heq_1075_, lean_object* v_i_1076_, lean_object* v_entries_1077_){
_start:
{
size_t v_depth_boxed_1078_; lean_object* v_res_1079_; 
v_depth_boxed_1078_ = lean_unbox_usize(v_depth_1072_);
lean_dec(v_depth_1072_);
v_res_1079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1071_, v_depth_boxed_1078_, v_keys_1073_, v_vals_1074_, v_heq_1075_, v_i_1076_, v_entries_1077_);
lean_dec_ref(v_vals_1074_);
lean_dec_ref(v_keys_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1092_; 
lean_inc(v_mvarId_1086_);
v___x_1092_ = l_Lean_MVarId_getType(v_mvarId_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = l_Lean_Expr_headBeta(v_a_1093_);
v___x_1095_ = l_Lean_MVarId_setType___redArg(v_mvarId_1086_, v___x_1094_, v_a_1088_);
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_mvarId_1086_);
v_a_1096_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1092_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1092_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_MVarId_headBetaType(v_mvarId_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1110_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
if (lean_obj_tag(v_x_1112_) == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = 0;
return v___x_1113_;
}
else
{
lean_object* v_key_1114_; lean_object* v_tail_1115_; uint8_t v___x_1116_; 
v_key_1114_ = lean_ctor_get(v_x_1112_, 0);
v_tail_1115_ = lean_ctor_get(v_x_1112_, 2);
v___x_1116_ = l_Lean_instBEqFVarId_beq(v_key_1114_, v_a_1111_);
if (v___x_1116_ == 0)
{
v_x_1112_ = v_tail_1115_;
goto _start;
}
else
{
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1118_, lean_object* v_x_1119_){
_start:
{
uint8_t v_res_1120_; lean_object* v_r_1121_; 
v_res_1120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1118_, v_x_1119_);
lean_dec(v_x_1119_);
lean_dec(v_a_1118_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
return v_x_1123_;
}
else
{
lean_object* v_key_1124_; lean_object* v_value_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v_key_1124_ = lean_ctor_get(v_x_1123_, 0);
v_value_1125_ = lean_ctor_get(v_x_1123_, 1);
v_tail_1126_ = lean_ctor_get(v_x_1123_, 2);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1128_ = v_x_1123_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_value_1125_);
lean_inc(v_key_1124_);
lean_dec(v_x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_instBEqFVarId_beq(v_key_1124_, v_a_1122_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1122_, v_tail_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_key_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_value_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_del_object(v___x_1128_);
lean_dec(v_value_1125_);
lean_dec(v_key_1124_);
return v_tail_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1136_, v_x_1137_);
lean_dec(v_a_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_size_1141_; lean_object* v_buckets_1142_; lean_object* v___x_1143_; uint64_t v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v_fold_1147_; uint64_t v___x_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v_bkt_1156_; uint8_t v___x_1157_; 
v_size_1141_ = lean_ctor_get(v_m_1139_, 0);
v_buckets_1142_ = lean_ctor_get(v_m_1139_, 1);
v___x_1143_ = lean_array_get_size(v_buckets_1142_);
v___x_1144_ = l_Lean_instHashableFVarId_hash(v_a_1140_);
v___x_1145_ = 32ULL;
v___x_1146_ = lean_uint64_shift_right(v___x_1144_, v___x_1145_);
v_fold_1147_ = lean_uint64_xor(v___x_1144_, v___x_1146_);
v___x_1148_ = 16ULL;
v___x_1149_ = lean_uint64_shift_right(v_fold_1147_, v___x_1148_);
v___x_1150_ = lean_uint64_xor(v_fold_1147_, v___x_1149_);
v___x_1151_ = lean_uint64_to_usize(v___x_1150_);
v___x_1152_ = lean_usize_of_nat(v___x_1143_);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_sub(v___x_1152_, v___x_1153_);
v___x_1155_ = lean_usize_land(v___x_1151_, v___x_1154_);
v_bkt_1156_ = lean_array_uget_borrowed(v_buckets_1142_, v___x_1155_);
v___x_1157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1140_, v_bkt_1156_);
if (v___x_1157_ == 0)
{
return v_m_1139_;
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1170_; 
lean_inc(v_bkt_1156_);
lean_inc_ref(v_buckets_1142_);
lean_inc(v_size_1141_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_m_1139_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1171_ = lean_ctor_get(v_m_1139_, 1);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_m_1139_, 0);
lean_dec(v_unused_1172_);
v___x_1159_ = v_m_1139_;
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_m_1139_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1170_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_buckets_x27_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1161_ = lean_box(0);
v_buckets_x27_1162_ = lean_array_uset(v_buckets_1142_, v___x_1155_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_sub(v_size_1141_, v___x_1163_);
lean_dec(v_size_1141_);
v___x_1165_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1140_, v_bkt_1156_);
v___x_1166_ = lean_array_uset(v_buckets_x27_1162_, v___x_1155_, v___x_1165_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1166_);
lean_ctor_set(v___x_1159_, 0, v___x_1164_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1173_, v_a_1174_);
lean_dec(v_a_1174_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1183_ = lean_st_ref_take(v___y_1177_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Lean_Expr_fvarId_x21(v_e_1176_);
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1183_, v___x_1185_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_st_ref_put(v___y_1177_, v___x_1186_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1184_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v_e_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_st_ref_get(v___y_1198_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(lean_object* v_e_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_visited_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v___x_1217_ = lean_st_ref_get(v_a_1215_);
v_visited_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_visited_1218_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_ptr_addr(v_e_1214_);
v___x_1220_ = ((size_t)8191ULL);
v___x_1221_ = lean_usize_mod(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_array_uget(v_visited_1218_, v___x_1221_);
lean_dec_ref(v_visited_1218_);
v___x_1223_ = lean_ptr_addr(v___x_1222_);
lean_dec(v___x_1222_);
v___x_1224_ = lean_usize_dec_eq(v___x_1223_, v___x_1219_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_visited_1226_; lean_object* v_checked_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1238_; 
v___x_1225_ = lean_st_ref_take(v_a_1215_);
v_visited_1226_ = lean_ctor_get(v___x_1225_, 0);
v_checked_1227_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1229_ = v___x_1225_;
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_checked_1227_);
lean_inc(v_visited_1226_);
lean_dec(v___x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_array_uset(v_visited_1226_, v___x_1221_, v_e_1214_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_checked_1227_);
v___x_1233_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_st_ref_put(v_a_1215_, v___x_1233_);
v___x_1235_ = lean_box(v___x_1224_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref(v_e_1214_);
v___x_1239_ = lean_box(v___x_1224_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1241_, v_a_1242_);
lean_dec(v_a_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(lean_object* v_a_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
uint8_t v___x_1247_; 
v___x_1247_ = 0;
return v___x_1247_;
}
else
{
lean_object* v_key_1248_; lean_object* v_tail_1249_; uint8_t v___x_1250_; 
v_key_1248_ = lean_ctor_get(v_x_1246_, 0);
v_tail_1249_ = lean_ctor_get(v_x_1246_, 2);
v___x_1250_ = lean_expr_eqv(v_key_1248_, v_a_1245_);
if (v___x_1250_ == 0)
{
v_x_1246_ = v_tail_1249_;
goto _start;
}
else
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(lean_object* v_a_1252_, lean_object* v_x_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1252_, v_x_1253_);
lean_dec(v_x_1253_);
lean_dec_ref(v_a_1252_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 0)
{
return v_x_1256_;
}
else
{
lean_object* v_key_1258_; lean_object* v_value_1259_; lean_object* v_tail_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1283_; 
v_key_1258_ = lean_ctor_get(v_x_1257_, 0);
v_value_1259_ = lean_ctor_get(v_x_1257_, 1);
v_tail_1260_ = lean_ctor_get(v_x_1257_, 2);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_x_1257_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1262_ = v_x_1257_;
v_isShared_1263_ = v_isSharedCheck_1283_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_tail_1260_);
lean_inc(v_value_1259_);
lean_inc(v_key_1258_);
lean_dec(v_x_1257_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1283_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; uint64_t v_fold_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; size_t v___x_1272_; size_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1264_ = lean_array_get_size(v_x_1256_);
v___x_1265_ = l_Lean_Expr_hash(v_key_1258_);
v___x_1266_ = 32ULL;
v___x_1267_ = lean_uint64_shift_right(v___x_1265_, v___x_1266_);
v_fold_1268_ = lean_uint64_xor(v___x_1265_, v___x_1267_);
v___x_1269_ = 16ULL;
v___x_1270_ = lean_uint64_shift_right(v_fold_1268_, v___x_1269_);
v___x_1271_ = lean_uint64_xor(v_fold_1268_, v___x_1270_);
v___x_1272_ = lean_uint64_to_usize(v___x_1271_);
v___x_1273_ = lean_usize_of_nat(v___x_1264_);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_sub(v___x_1273_, v___x_1274_);
v___x_1276_ = lean_usize_land(v___x_1272_, v___x_1275_);
v___x_1277_ = lean_array_uget_borrowed(v_x_1256_, v___x_1276_);
lean_inc(v___x_1277_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 2, v___x_1277_);
v___x_1279_ = v___x_1262_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_key_1258_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_value_1259_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_array_uset(v_x_1256_, v___x_1276_, v___x_1279_);
v_x_1256_ = v___x_1280_;
v_x_1257_ = v_tail_1260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(lean_object* v_i_1284_, lean_object* v_source_1285_, lean_object* v_target_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_array_get_size(v_source_1285_);
v___x_1288_ = lean_nat_dec_lt(v_i_1284_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_source_1285_);
lean_dec(v_i_1284_);
return v_target_1286_;
}
else
{
lean_object* v_es_1289_; lean_object* v___x_1290_; lean_object* v_source_1291_; lean_object* v_target_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_es_1289_ = lean_array_fget(v_source_1285_, v_i_1284_);
v___x_1290_ = lean_box(0);
v_source_1291_ = lean_array_fset(v_source_1285_, v_i_1284_, v___x_1290_);
v_target_1292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_1286_, v_es_1289_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_add(v_i_1284_, v___x_1293_);
lean_dec(v_i_1284_);
v_i_1284_ = v___x_1294_;
v_source_1285_ = v_source_1291_;
v_target_1286_ = v_target_1292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(lean_object* v_data_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v_nbuckets_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1297_ = lean_array_get_size(v_data_1296_);
v___x_1298_ = lean_unsigned_to_nat(2u);
v_nbuckets_1299_ = lean_nat_mul(v___x_1297_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_mk_array(v_nbuckets_1299_, v___x_1301_);
v___x_1303_ = lean_array_propagate_mark(v_data_1296_, v___x_1302_);
v___x_1304_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1300_, v_data_1296_, v___x_1303_);
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
v___x_1386_ = lean_st_ref_put(v_a_1371_, v___x_1385_);
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
lean_dec_ref_known(v___x_1454_, 1);
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
v___x_1417_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_d_1414_, v___y_1416_, v___y_1411_, v___y_1409_, v___y_1413_, v___y_1410_, v___y_1412_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_dec_ref_known(v___x_1417_, 1);
v_e_1400_ = v_b_1415_;
v_a_1401_ = v___y_1416_;
v___y_1402_ = v___y_1411_;
v___y_1403_ = v___y_1409_;
v___y_1404_ = v___y_1413_;
v___y_1405_ = v___y_1410_;
v___y_1406_ = v___y_1412_;
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
lean_dec_ref_known(v_e_1400_, 3);
v___y_1409_ = v___y_1422_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1421_;
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1423_;
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
lean_dec_ref_known(v_e_1400_, 3);
v___y_1409_ = v___y_1422_;
v___y_1410_ = v___y_1424_;
v___y_1411_ = v___y_1421_;
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1423_;
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
lean_dec_ref_known(v_e_1400_, 4);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1433_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_type_1430_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref_known(v___x_1433_, 1);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_value_1431_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref_known(v___x_1434_, 1);
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
lean_dec_ref_known(v_e_1400_, 2);
lean_inc_ref(v_f_1398_);
lean_inc_ref(v_p_1397_);
v___x_1438_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1397_, v_f_1398_, v_stopWhenVisited_1399_, v_fn_1436_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
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
lean_dec_ref_known(v_e_1400_, 2);
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
lean_dec_ref_known(v_e_1400_, 3);
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
lean_object* v_a_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___y_1551_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = l_Lean_Expr_hasFVar(v_a_1547_);
v___x_1549_ = lean_st_mk_ref(v_candidates_1540_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_a_1547_);
lean_dec_ref(v___f_1537_);
v___x_1561_ = lean_box(0);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___x_1549_);
v___x_1562_ = lean_apply_7(v___f_1536_, v___x_1561_, v___x_1549_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___y_1551_ = v___x_1562_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1564_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1563_, v___f_1537_, v_a_1547_, v___x_1538_, v___x_1549_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___x_1549_);
v___x_1566_ = lean_apply_7(v___f_1536_, v_a_1565_, v___x_1549_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
v___y_1551_ = v___x_1566_;
goto v___jp_1550_;
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v___x_1549_);
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
v___jp_1550_:
{
if (lean_obj_tag(v___y_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_a_1552_ = lean_ctor_get(v___y_1551_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___y_1551_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v___y_1551_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___y_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_st_ref_get(v___x_1549_);
lean_dec(v___x_1549_);
lean_dec(v___x_1556_);
if (v_isShared_1555_ == 0)
{
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1552_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_dec(v___x_1549_);
return v___y_1551_;
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
uint8_t v___x_16881__boxed_1593_; lean_object* v_res_1594_; 
v___x_16881__boxed_1593_ = lean_unbox(v___x_1585_);
v_res_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1583_, v___f_1584_, v___x_16881__boxed_1593_, v_e_1586_, v_candidates_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_st_ref_get(v___y_1596_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1619_ = lean_st_ref_take(v___y_1613_);
v___x_1620_ = lean_box(0);
v___x_1621_ = l_Lean_Expr_fvarId_x21(v_e_1612_);
v___x_1622_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1619_, v___x_1621_);
lean_dec(v___x_1621_);
v___x_1623_ = lean_st_ref_put(v___y_1613_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v_e_1625_);
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
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_nbuckets_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1674_ = lean_array_get_size(v_data_1673_);
v___x_1675_ = lean_unsigned_to_nat(2u);
v_nbuckets_1676_ = lean_nat_mul(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_box(0);
v___x_1679_ = lean_mk_array(v_nbuckets_1676_, v___x_1678_);
v___x_1680_ = lean_array_propagate_mark(v_data_1673_, v___x_1679_);
v___x_1681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1677_, v_data_1673_, v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1682_, lean_object* v_a_1683_, lean_object* v_b_1684_){
_start:
{
lean_object* v_size_1685_; lean_object* v_buckets_1686_; lean_object* v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v_fold_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v_bkt_1700_; uint8_t v___x_1701_; 
v_size_1685_ = lean_ctor_get(v_m_1682_, 0);
v_buckets_1686_ = lean_ctor_get(v_m_1682_, 1);
v___x_1687_ = lean_array_get_size(v_buckets_1686_);
v___x_1688_ = l_Lean_instHashableFVarId_hash(v_a_1683_);
v___x_1689_ = 32ULL;
v___x_1690_ = lean_uint64_shift_right(v___x_1688_, v___x_1689_);
v_fold_1691_ = lean_uint64_xor(v___x_1688_, v___x_1690_);
v___x_1692_ = 16ULL;
v___x_1693_ = lean_uint64_shift_right(v_fold_1691_, v___x_1692_);
v___x_1694_ = lean_uint64_xor(v_fold_1691_, v___x_1693_);
v___x_1695_ = lean_uint64_to_usize(v___x_1694_);
v___x_1696_ = lean_usize_of_nat(v___x_1687_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_sub(v___x_1696_, v___x_1697_);
v___x_1699_ = lean_usize_land(v___x_1695_, v___x_1698_);
v_bkt_1700_ = lean_array_uget_borrowed(v_buckets_1686_, v___x_1699_);
v___x_1701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1683_, v_bkt_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1722_; 
lean_inc_ref(v_buckets_1686_);
lean_inc(v_size_1685_);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_m_1682_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; lean_object* v_unused_1724_; 
v_unused_1723_ = lean_ctor_get(v_m_1682_, 1);
lean_dec(v_unused_1723_);
v_unused_1724_ = lean_ctor_get(v_m_1682_, 0);
lean_dec(v_unused_1724_);
v___x_1703_ = v_m_1682_;
v_isShared_1704_ = v_isSharedCheck_1722_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_m_1682_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1722_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v_size_x27_1706_; lean_object* v___x_1707_; lean_object* v_buckets_x27_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1705_ = lean_unsigned_to_nat(1u);
v_size_x27_1706_ = lean_nat_add(v_size_1685_, v___x_1705_);
lean_dec(v_size_1685_);
lean_inc(v_bkt_1700_);
v___x_1707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1707_, 0, v_a_1683_);
lean_ctor_set(v___x_1707_, 1, v_b_1684_);
lean_ctor_set(v___x_1707_, 2, v_bkt_1700_);
v_buckets_x27_1708_ = lean_array_uset(v_buckets_1686_, v___x_1699_, v___x_1707_);
v___x_1709_ = lean_unsigned_to_nat(4u);
v___x_1710_ = lean_nat_mul(v_size_x27_1706_, v___x_1709_);
v___x_1711_ = lean_unsigned_to_nat(3u);
v___x_1712_ = lean_nat_div(v___x_1710_, v___x_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_array_get_size(v_buckets_x27_1708_);
v___x_1714_ = lean_nat_dec_le(v___x_1712_, v___x_1713_);
lean_dec(v___x_1712_);
if (v___x_1714_ == 0)
{
lean_object* v_val_1715_; lean_object* v___x_1717_; 
v_val_1715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1708_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_val_1715_);
lean_ctor_set(v___x_1703_, 0, v_size_x27_1706_);
v___x_1717_ = v___x_1703_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_size_x27_1706_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_val_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
else
{
lean_object* v___x_1720_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_buckets_x27_1708_);
lean_ctor_set(v___x_1703_, 0, v_size_x27_1706_);
v___x_1720_ = v___x_1703_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_size_x27_1706_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_buckets_x27_1708_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_dec(v_b_1684_);
lean_dec(v_a_1683_);
return v_m_1682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1727_, size_t v_sz_1728_, size_t v_i_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1729_, v_sz_1728_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_b_1730_);
return v___x_1737_;
}
else
{
lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1800_; 
v_snd_1738_ = lean_ctor_get(v_b_1730_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_b_1730_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_b_1730_, 0);
lean_dec(v_unused_1801_);
v___x_1740_ = v_b_1730_;
v_isShared_1741_ = v_isSharedCheck_1800_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_dec(v_b_1730_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1800_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v_a_1744_; lean_object* v_a_1751_; 
v___x_1742_ = lean_box(0);
v_a_1751_ = lean_array_uget_borrowed(v_as_1727_, v_i_1729_);
if (lean_obj_tag(v_a_1751_) == 0)
{
v_a_1744_ = v_snd_1738_;
goto v___jp_1743_;
}
else
{
lean_object* v_val_1752_; uint8_t v___x_1753_; 
v_val_1752_ = lean_ctor_get(v_a_1751_, 0);
v___x_1753_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___f_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; lean_object* v_candidates_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___x_1778_; 
v___f_1754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1756_ = l_Lean_LocalDecl_type(v_val_1752_);
lean_inc_ref(v___x_1756_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1754_, v___f_1755_, v___x_1753_, v___x_1756_, v_snd_1738_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_LocalDecl_value_x3f(v_val_1752_, v___x_1753_);
if (lean_obj_tag(v___x_1780_) == 0)
{
v_candidates_1758_ = v_a_1779_;
v___y_1759_ = v___y_1731_;
v___y_1760_ = v___y_1732_;
v___y_1761_ = v___y_1733_;
v___y_1762_ = v___y_1734_;
goto v___jp_1757_;
}
else
{
lean_object* v_val_1781_; lean_object* v___x_1782_; 
v_val_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1754_, v___f_1755_, v___x_1753_, v_val_1781_, v_a_1779_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_candidates_1758_ = v_a_1783_;
v___y_1759_ = v___y_1731_;
v___y_1760_ = v___y_1732_;
v___y_1761_ = v___y_1733_;
v___y_1762_ = v___y_1734_;
goto v___jp_1757_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v___x_1756_);
lean_del_object(v___x_1740_);
v_a_1784_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1782_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v___x_1756_);
lean_del_object(v___x_1740_);
v_a_1792_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1778_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1778_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
v___jp_1757_:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Meta_isProp(v___x_1756_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; uint8_t v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = lean_unbox(v_a_1764_);
lean_dec(v_a_1764_);
if (v___x_1765_ == 0)
{
v_a_1744_ = v_candidates_1758_;
goto v___jp_1743_;
}
else
{
uint8_t v___x_1766_; 
v___x_1766_ = l_Lean_LocalDecl_hasValue(v_val_1752_, v___x_1753_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = l_Lean_LocalDecl_fvarId(v_val_1752_);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1758_, v___x_1767_, v___x_1768_);
v_a_1744_ = v___x_1769_;
goto v___jp_1743_;
}
else
{
v_a_1744_ = v_candidates_1758_;
goto v___jp_1743_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_candidates_1758_);
lean_del_object(v___x_1740_);
v_a_1770_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1763_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1763_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
v_a_1744_ = v_snd_1738_;
goto v___jp_1743_;
}
}
v___jp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_a_1744_);
lean_ctor_set(v___x_1740_, 0, v___x_1742_);
v___x_1746_ = v___x_1740_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_a_1744_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
size_t v___x_1747_; size_t v___x_1748_; 
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1729_, v___x_1747_);
v_i_1729_ = v___x_1748_;
v_b_1730_ = v___x_1746_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1802_, lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_b_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1802_, v_sz_boxed_1811_, v_i_boxed_1812_, v_b_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_as_1802_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1814_, size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1817_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1887_; 
v_snd_1825_ = lean_ctor_get(v_b_1817_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_b_1817_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_b_1817_, 0);
lean_dec(v_unused_1888_);
v___x_1827_ = v_b_1817_;
v_isShared_1828_ = v_isSharedCheck_1887_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1817_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1887_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v_a_1831_; lean_object* v_a_1838_; 
v___x_1829_ = lean_box(0);
v_a_1838_ = lean_array_uget_borrowed(v_as_1814_, v_i_1816_);
if (lean_obj_tag(v_a_1838_) == 0)
{
v_a_1831_ = v_snd_1825_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1839_; uint8_t v___x_1840_; 
v_val_1839_ = lean_ctor_get(v_a_1838_, 0);
v___x_1840_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___f_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v_candidates_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___x_1865_; 
v___f_1841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1843_ = l_Lean_LocalDecl_type(v_val_1839_);
lean_inc_ref(v___x_1843_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1841_, v___f_1842_, v___x_1840_, v___x_1843_, v_snd_1825_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = l_Lean_LocalDecl_value_x3f(v_val_1839_, v___x_1840_);
if (lean_obj_tag(v___x_1867_) == 0)
{
v_candidates_1845_ = v_a_1866_;
v___y_1846_ = v___y_1818_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
v___y_1849_ = v___y_1821_;
goto v___jp_1844_;
}
else
{
lean_object* v_val_1868_; lean_object* v___x_1869_; 
v_val_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1841_, v___f_1842_, v___x_1840_, v_val_1868_, v_a_1866_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_candidates_1845_ = v_a_1870_;
v___y_1846_ = v___y_1818_;
v___y_1847_ = v___y_1819_;
v___y_1848_ = v___y_1820_;
v___y_1849_ = v___y_1821_;
goto v___jp_1844_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1843_);
lean_del_object(v___x_1827_);
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
lean_dec_ref(v___x_1843_);
lean_del_object(v___x_1827_);
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
v___jp_1844_:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Meta_isProp(v___x_1843_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; uint8_t v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1852_ = lean_unbox(v_a_1851_);
lean_dec(v_a_1851_);
if (v___x_1852_ == 0)
{
v_a_1831_ = v_candidates_1845_;
goto v___jp_1830_;
}
else
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_LocalDecl_hasValue(v_val_1839_, v___x_1840_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = l_Lean_LocalDecl_fvarId(v_val_1839_);
v___x_1855_ = lean_box(0);
v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1845_, v___x_1854_, v___x_1855_);
v_a_1831_ = v___x_1856_;
goto v___jp_1830_;
}
else
{
v_a_1831_ = v_candidates_1845_;
goto v___jp_1830_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_candidates_1845_);
lean_del_object(v___x_1827_);
v_a_1857_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1850_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1850_);
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
v_a_1831_ = v_snd_1825_;
goto v___jp_1830_;
}
}
v___jp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v_a_1831_);
lean_ctor_set(v___x_1827_, 0, v___x_1829_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1816_, v___x_1834_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1814_, v_sz_1815_, v___x_1835_, v___x_1833_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1836_;
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
lean_object* v_snd_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1974_; 
v_snd_1912_ = lean_ctor_get(v_b_1904_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_b_1904_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_b_1904_, 0);
lean_dec(v_unused_1975_);
v___x_1914_ = v_b_1904_;
v_isShared_1915_ = v_isSharedCheck_1974_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_snd_1912_);
lean_dec(v_b_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1974_;
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
lean_object* v_val_1926_; uint8_t v___x_1927_; 
v_val_1926_ = lean_ctor_get(v_a_1925_, 0);
v___x_1927_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; lean_object* v_candidates_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___x_1952_; 
v___f_1928_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1930_ = l_Lean_LocalDecl_type(v_val_1926_);
lean_inc_ref(v___x_1930_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1928_, v___f_1929_, v___x_1927_, v___x_1930_, v_snd_1912_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_LocalDecl_value_x3f(v_val_1926_, v___x_1927_);
if (lean_obj_tag(v___x_1954_) == 0)
{
v_candidates_1932_ = v_a_1953_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
goto v___jp_1931_;
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1956_; 
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1928_, v___f_1929_, v___x_1927_, v_val_1955_, v_a_1953_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v_candidates_1932_ = v_a_1957_;
v___y_1933_ = v___y_1905_;
v___y_1934_ = v___y_1906_;
v___y_1935_ = v___y_1907_;
v___y_1936_ = v___y_1908_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1914_);
v_a_1958_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1956_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1914_);
v_a_1966_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1952_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1952_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
v___jp_1931_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Meta_isProp(v___x_1930_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; uint8_t v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1939_ == 0)
{
v_a_1918_ = v_candidates_1932_;
goto v___jp_1917_;
}
else
{
uint8_t v___x_1940_; 
v___x_1940_ = l_Lean_LocalDecl_hasValue(v_val_1926_, v___x_1927_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = l_Lean_LocalDecl_fvarId(v_val_1926_);
v___x_1942_ = lean_box(0);
v___x_1943_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_1932_, v___x_1941_, v___x_1942_);
v_a_1918_ = v___x_1943_;
goto v___jp_1917_;
}
else
{
v_a_1918_ = v_candidates_1932_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_candidates_1932_);
lean_del_object(v___x_1914_);
v_a_1944_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1937_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1937_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1976_, lean_object* v_sz_1977_, lean_object* v_i_1978_, lean_object* v_b_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
size_t v_sz_boxed_1985_; size_t v_i_boxed_1986_; lean_object* v_res_1987_; 
v_sz_boxed_1985_ = lean_unbox_usize(v_sz_1977_);
lean_dec(v_sz_1977_);
v_i_boxed_1986_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1976_, v_sz_boxed_1985_, v_i_boxed_1986_, v_b_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_as_1976_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_b_1991_);
return v___x_1998_;
}
else
{
lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2061_; 
v_snd_1999_ = lean_ctor_get(v_b_1991_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_1991_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_b_1991_, 0);
lean_dec(v_unused_2062_);
v___x_2001_ = v_b_1991_;
v_isShared_2002_ = v_isSharedCheck_2061_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_dec(v_b_1991_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2061_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v_a_2005_; lean_object* v_a_2012_; 
v___x_2003_ = lean_box(0);
v_a_2012_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
if (lean_obj_tag(v_a_2012_) == 0)
{
v_a_2005_ = v_snd_1999_;
goto v___jp_2004_;
}
else
{
lean_object* v_val_2013_; uint8_t v___x_2014_; 
v_val_2013_ = lean_ctor_get(v_a_2012_, 0);
v___x_2014_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v_candidates_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___x_2039_; 
v___f_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2017_ = l_Lean_LocalDecl_type(v_val_2013_);
lean_inc_ref(v___x_2017_);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2015_, v___f_2016_, v___x_2014_, v___x_2017_, v_snd_1999_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = l_Lean_LocalDecl_value_x3f(v_val_2013_, v___x_2014_);
if (lean_obj_tag(v___x_2041_) == 0)
{
v_candidates_2019_ = v_a_2040_;
v___y_2020_ = v___y_1992_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
goto v___jp_2018_;
}
else
{
lean_object* v_val_2042_; lean_object* v___x_2043_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2015_, v___f_2016_, v___x_2014_, v_val_2042_, v_a_2040_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v_candidates_2019_ = v_a_2044_;
v___y_2020_ = v___y_1992_;
v___y_2021_ = v___y_1993_;
v___y_2022_ = v___y_1994_;
v___y_2023_ = v___y_1995_;
goto v___jp_2018_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2045_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2043_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v___x_2017_);
lean_del_object(v___x_2001_);
v_a_2053_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2039_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2039_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
v___jp_2018_:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_isProp(v___x_2017_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; uint8_t v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
if (v___x_2026_ == 0)
{
v_a_2005_ = v_candidates_2019_;
goto v___jp_2004_;
}
else
{
uint8_t v___x_2027_; 
v___x_2027_ = l_Lean_LocalDecl_hasValue(v_val_2013_, v___x_2014_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = l_Lean_LocalDecl_fvarId(v_val_2013_);
v___x_2029_ = lean_box(0);
v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_candidates_2019_, v___x_2028_, v___x_2029_);
v_a_2005_ = v___x_2030_;
goto v___jp_2004_;
}
else
{
v_a_2005_ = v_candidates_2019_;
goto v___jp_2004_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_candidates_2019_);
lean_del_object(v___x_2001_);
v_a_2031_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2024_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2024_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
else
{
v_a_2005_ = v_snd_1999_;
goto v___jp_2004_;
}
}
v___jp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v_a_2005_);
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_a_2005_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
size_t v___x_2008_; size_t v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = ((size_t)1ULL);
v___x_2009_ = lean_usize_add(v_i_1990_, v___x_2008_);
v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1988_, v_sz_1989_, v___x_2009_, v___x_2007_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2063_, lean_object* v_sz_2064_, lean_object* v_i_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
size_t v_sz_boxed_2072_; size_t v_i_boxed_2073_; lean_object* v_res_2074_; 
v_sz_boxed_2072_ = lean_unbox_usize(v_sz_2064_);
lean_dec(v_sz_2064_);
v_i_boxed_2073_ = lean_unbox_usize(v_i_2065_);
lean_dec(v_i_2065_);
v_res_2074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2063_, v_sz_boxed_2072_, v_i_boxed_2073_, v_b_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec_ref(v_as_2063_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2075_, lean_object* v_n_2076_, lean_object* v_b_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
if (lean_obj_tag(v_n_2076_) == 0)
{
lean_object* v_cs_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v_cs_2083_ = lean_ctor_get(v_n_2076_, 0);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v_b_2077_);
v_sz_2086_ = lean_array_size(v_cs_2083_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2075_, v_cs_2083_, v_sz_2086_, v___x_2087_, v___x_2085_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2103_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_fst_2093_; 
v_fst_2093_ = lean_ctor_get(v_a_2089_, 0);
if (lean_obj_tag(v_fst_2093_) == 0)
{
lean_object* v_snd_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_snd_2094_ = lean_ctor_get(v_a_2089_, 1);
lean_inc(v_snd_2094_);
lean_dec(v_a_2089_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_snd_2094_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2095_);
v___x_2097_ = v___x_2091_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
else
{
lean_object* v_val_2099_; lean_object* v___x_2101_; 
lean_inc_ref(v_fst_2093_);
lean_dec(v_a_2089_);
v_val_2099_ = lean_ctor_get(v_fst_2093_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v_fst_2093_, 1);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v_val_2099_);
v___x_2101_ = v___x_2091_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2088_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2088_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_vs_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v_vs_2112_ = lean_ctor_get(v_n_2076_, 0);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_b_2077_);
v_sz_2115_ = lean_array_size(v_vs_2112_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2112_, v_sz_2115_, v___x_2116_, v___x_2114_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2132_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2132_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v_fst_2122_; 
v_fst_2122_ = lean_ctor_get(v_a_2118_, 0);
if (lean_obj_tag(v_fst_2122_) == 0)
{
lean_object* v_snd_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v_snd_2123_ = lean_ctor_get(v_a_2118_, 1);
lean_inc(v_snd_2123_);
lean_dec(v_a_2118_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_snd_2123_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2124_);
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
else
{
lean_object* v_val_2128_; lean_object* v___x_2130_; 
lean_inc_ref(v_fst_2122_);
lean_dec(v_a_2118_);
v_val_2128_ = lean_ctor_get(v_fst_2122_, 0);
lean_inc(v_val_2128_);
lean_dec_ref_known(v_fst_2122_, 1);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v_val_2128_);
v___x_2130_ = v___x_2120_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_val_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_a_2133_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2117_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2117_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2141_, lean_object* v_as_2142_, size_t v_sz_2143_, size_t v_i_2144_, lean_object* v_b_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_usize_dec_lt(v_i_2144_, v_sz_2143_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_b_2145_);
return v___x_2152_;
}
else
{
lean_object* v_snd_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2187_; 
v_snd_2153_ = lean_ctor_get(v_b_2145_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_b_2145_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v_b_2145_, 0);
lean_dec(v_unused_2188_);
v___x_2155_ = v_b_2145_;
v_isShared_2156_ = v_isSharedCheck_2187_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_snd_2153_);
lean_dec(v_b_2145_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2187_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v_a_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v_a_2158_ = lean_array_uget_borrowed(v_as_2142_, v_i_2144_);
lean_inc(v_snd_2153_);
v___x_2159_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2141_, v_a_2158_, v_snd_2153_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2178_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2178_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
if (lean_obj_tag(v_a_2160_) == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2160_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2164_);
v___x_2166_ = v___x_2155_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_snd_2153_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2166_);
v___x_2168_ = v___x_2162_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; 
lean_del_object(v___x_2162_);
lean_dec(v_snd_2153_);
v_a_2171_ = lean_ctor_get(v_a_2160_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v_a_2160_, 1);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_a_2171_);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2173_ = v___x_2155_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_2171_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
size_t v___x_2174_; size_t v___x_2175_; 
v___x_2174_ = ((size_t)1ULL);
v___x_2175_ = lean_usize_add(v_i_2144_, v___x_2174_);
v_i_2144_ = v___x_2175_;
v_b_2145_ = v___x_2173_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_del_object(v___x_2155_);
lean_dec(v_snd_2153_);
v_a_2179_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2159_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2159_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2189_, lean_object* v_as_2190_, lean_object* v_sz_2191_, lean_object* v_i_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2191_);
lean_dec(v_sz_2191_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2189_, v_as_2190_, v_sz_boxed_2199_, v_i_boxed_2200_, v_b_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v_as_2190_);
lean_dec_ref(v_init_2189_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2202_, lean_object* v_n_2203_, lean_object* v_b_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2202_, v_n_2203_, v_b_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec_ref(v_n_2203_);
lean_dec_ref(v_init_2202_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2211_, lean_object* v_init_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_root_2218_; lean_object* v_tail_2219_; lean_object* v___x_2220_; 
v_root_2218_ = lean_ctor_get(v_t_2211_, 0);
v_tail_2219_ = lean_ctor_get(v_t_2211_, 1);
lean_inc_ref(v_init_2212_);
v___x_2220_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2212_, v_root_2218_, v_init_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec_ref(v_init_2212_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2257_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2257_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2257_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
if (lean_obj_tag(v_a_2221_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; 
v_a_2225_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v_a_2221_, 1);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_a_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; size_t v_sz_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2223_);
v_a_2229_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v_a_2221_, 1);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
lean_ctor_set(v___x_2231_, 1, v_a_2229_);
v_sz_2232_ = lean_array_size(v_tail_2219_);
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2219_, v_sz_2232_, v___x_2233_, v___x_2231_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2248_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2248_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2248_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_fst_2239_; 
v_fst_2239_ = lean_ctor_get(v_a_2235_, 0);
if (lean_obj_tag(v_fst_2239_) == 0)
{
lean_object* v_snd_2240_; lean_object* v___x_2242_; 
v_snd_2240_ = lean_ctor_get(v_a_2235_, 1);
lean_inc(v_snd_2240_);
lean_dec(v_a_2235_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v_snd_2240_);
v___x_2242_ = v___x_2237_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_snd_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
else
{
lean_object* v_val_2244_; lean_object* v___x_2246_; 
lean_inc_ref(v_fst_2239_);
lean_dec(v_a_2235_);
v_val_2244_ = lean_ctor_get(v_fst_2239_, 0);
lean_inc(v_val_2244_);
lean_dec_ref_known(v_fst_2239_, 1);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v_val_2244_);
v___x_2246_ = v___x_2237_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_val_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_a_2249_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2234_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2234_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2220_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2220_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2266_, lean_object* v_init_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2266_, v_init_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v_t_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_buckets_2276_; lean_object* v___x_2277_; uint64_t v___x_2278_; uint64_t v___x_2279_; uint64_t v___x_2280_; uint64_t v_fold_2281_; uint64_t v___x_2282_; uint64_t v___x_2283_; uint64_t v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_buckets_2276_ = lean_ctor_get(v_m_2274_, 1);
v___x_2277_ = lean_array_get_size(v_buckets_2276_);
v___x_2278_ = l_Lean_instHashableFVarId_hash(v_a_2275_);
v___x_2279_ = 32ULL;
v___x_2280_ = lean_uint64_shift_right(v___x_2278_, v___x_2279_);
v_fold_2281_ = lean_uint64_xor(v___x_2278_, v___x_2280_);
v___x_2282_ = 16ULL;
v___x_2283_ = lean_uint64_shift_right(v_fold_2281_, v___x_2282_);
v___x_2284_ = lean_uint64_xor(v_fold_2281_, v___x_2283_);
v___x_2285_ = lean_uint64_to_usize(v___x_2284_);
v___x_2286_ = lean_usize_of_nat(v___x_2277_);
v___x_2287_ = ((size_t)1ULL);
v___x_2288_ = lean_usize_sub(v___x_2286_, v___x_2287_);
v___x_2289_ = lean_usize_land(v___x_2285_, v___x_2288_);
v___x_2290_ = lean_array_uget_borrowed(v_buckets_2276_, v___x_2289_);
v___x_2291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2275_, v___x_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2292_, lean_object* v_a_2293_){
_start:
{
uint8_t v_res_2294_; lean_object* v_r_2295_; 
v_res_2294_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_m_2292_);
v_r_2295_ = lean_box(v_res_2294_);
return v_r_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2296_, lean_object* v_as_2297_, size_t v_sz_2298_, size_t v_i_2299_, lean_object* v_b_2300_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_usize_dec_lt(v_i_2299_, v_sz_2298_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_b_2300_);
return v___x_2303_;
}
else
{
lean_object* v_snd_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2322_; 
v_snd_2304_ = lean_ctor_get(v_b_2300_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_b_2300_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_b_2300_, 0);
lean_dec(v_unused_2323_);
v___x_2306_ = v_b_2300_;
v_isShared_2307_ = v_isSharedCheck_2322_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2304_);
lean_dec(v_b_2300_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2322_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v_a_2310_; lean_object* v_a_2317_; 
v___x_2308_ = lean_box(0);
v_a_2317_ = lean_array_uget_borrowed(v_as_2297_, v_i_2299_);
if (lean_obj_tag(v_a_2317_) == 0)
{
v_a_2310_ = v_snd_2304_;
goto v___jp_2309_;
}
else
{
lean_object* v_val_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v_val_2318_ = lean_ctor_get(v_a_2317_, 0);
v___x_2319_ = l_Lean_LocalDecl_fvarId(v_val_2318_);
v___x_2320_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2296_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec(v___x_2319_);
v_a_2310_ = v_snd_2304_;
goto v___jp_2309_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_array_push(v_snd_2304_, v___x_2319_);
v_a_2310_ = v___x_2321_;
goto v___jp_2309_;
}
}
v___jp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v_a_2310_);
lean_ctor_set(v___x_2306_, 0, v___x_2308_);
v___x_2312_ = v___x_2306_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2310_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
size_t v___x_2313_; size_t v___x_2314_; 
v___x_2313_ = ((size_t)1ULL);
v___x_2314_ = lean_usize_add(v_i_2299_, v___x_2313_);
v_i_2299_ = v___x_2314_;
v_b_2300_ = v___x_2312_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2324_, lean_object* v_as_2325_, lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_){
_start:
{
size_t v_sz_boxed_2330_; size_t v_i_boxed_2331_; lean_object* v_res_2332_; 
v_sz_boxed_2330_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2331_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2324_, v_as_2325_, v_sz_boxed_2330_, v_i_boxed_2331_, v_b_2328_);
lean_dec_ref(v_as_2325_);
lean_dec_ref(v_a_2324_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2333_, lean_object* v_as_2334_, size_t v_sz_2335_, size_t v_i_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_lt(v_i_2336_, v_sz_2335_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_b_2337_);
return v___x_2344_;
}
else
{
lean_object* v_snd_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2363_; 
v_snd_2345_ = lean_ctor_get(v_b_2337_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_b_2337_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v_b_2337_, 0);
lean_dec(v_unused_2364_);
v___x_2347_ = v_b_2337_;
v_isShared_2348_ = v_isSharedCheck_2363_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_snd_2345_);
lean_dec(v_b_2337_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2363_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v_a_2351_; lean_object* v_a_2358_; 
v___x_2349_ = lean_box(0);
v_a_2358_ = lean_array_uget_borrowed(v_as_2334_, v_i_2336_);
if (lean_obj_tag(v_a_2358_) == 0)
{
v_a_2351_ = v_snd_2345_;
goto v___jp_2350_;
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_val_2359_ = lean_ctor_get(v_a_2358_, 0);
v___x_2360_ = l_Lean_LocalDecl_fvarId(v_val_2359_);
v___x_2361_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2333_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec(v___x_2360_);
v_a_2351_ = v_snd_2345_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_array_push(v_snd_2345_, v___x_2360_);
v_a_2351_ = v___x_2362_;
goto v___jp_2350_;
}
}
v___jp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 1, v_a_2351_);
lean_ctor_set(v___x_2347_, 0, v___x_2349_);
v___x_2353_ = v___x_2347_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_a_2351_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
size_t v___x_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((size_t)1ULL);
v___x_2355_ = lean_usize_add(v_i_2336_, v___x_2354_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2333_, v_as_2334_, v_sz_2335_, v___x_2355_, v___x_2353_);
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2365_, lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_b_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
size_t v_sz_boxed_2375_; size_t v_i_boxed_2376_; lean_object* v_res_2377_; 
v_sz_boxed_2375_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2376_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2365_, v_as_2366_, v_sz_boxed_2375_, v_i_boxed_2376_, v_b_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v_as_2366_);
lean_dec_ref(v_a_2365_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2378_, lean_object* v_a_2379_, lean_object* v_n_2380_, lean_object* v_b_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
if (lean_obj_tag(v_n_2380_) == 0)
{
lean_object* v_cs_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; 
v_cs_2387_ = lean_ctor_get(v_n_2380_, 0);
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v_b_2381_);
v_sz_2390_ = lean_array_size(v_cs_2387_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2378_, v_a_2379_, v_cs_2387_, v_sz_2390_, v___x_2391_, v___x_2389_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2407_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2407_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2407_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_fst_2397_; 
v_fst_2397_ = lean_ctor_get(v_a_2393_, 0);
if (lean_obj_tag(v_fst_2397_) == 0)
{
lean_object* v_snd_2398_; lean_object* v___x_2399_; lean_object* v___x_2401_; 
v_snd_2398_ = lean_ctor_get(v_a_2393_, 1);
lean_inc(v_snd_2398_);
lean_dec(v_a_2393_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_snd_2398_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2399_);
v___x_2401_ = v___x_2395_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2405_; 
lean_inc_ref(v_fst_2397_);
lean_dec(v_a_2393_);
v_val_2403_ = lean_ctor_get(v_fst_2397_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v_fst_2397_, 1);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v_val_2403_);
v___x_2405_ = v___x_2395_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_val_2403_);
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
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2392_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2392_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v_vs_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; size_t v_sz_2419_; size_t v___x_2420_; lean_object* v___x_2421_; 
v_vs_2416_ = lean_ctor_get(v_n_2380_, 0);
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v_b_2381_);
v_sz_2419_ = lean_array_size(v_vs_2416_);
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2379_, v_vs_2416_, v_sz_2419_, v___x_2420_, v___x_2418_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2436_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2436_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2436_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v_fst_2426_; 
v_fst_2426_ = lean_ctor_get(v_a_2422_, 0);
if (lean_obj_tag(v_fst_2426_) == 0)
{
lean_object* v_snd_2427_; lean_object* v___x_2428_; lean_object* v___x_2430_; 
v_snd_2427_ = lean_ctor_get(v_a_2422_, 1);
lean_inc(v_snd_2427_);
lean_dec(v_a_2422_);
v___x_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_snd_2427_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2428_);
v___x_2430_ = v___x_2424_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
else
{
lean_object* v_val_2432_; lean_object* v___x_2434_; 
lean_inc_ref(v_fst_2426_);
lean_dec(v_a_2422_);
v_val_2432_ = lean_ctor_get(v_fst_2426_, 0);
lean_inc(v_val_2432_);
lean_dec_ref_known(v_fst_2426_, 1);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v_val_2432_);
v___x_2434_ = v___x_2424_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_val_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
v_a_2437_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2421_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2421_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2445_, lean_object* v_a_2446_, lean_object* v_as_2447_, size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2457_, 0, v_b_2450_);
return v___x_2457_;
}
else
{
lean_object* v_snd_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2492_; 
v_snd_2458_ = lean_ctor_get(v_b_2450_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_b_2450_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_b_2450_, 0);
lean_dec(v_unused_2493_);
v___x_2460_ = v_b_2450_;
v_isShared_2461_ = v_isSharedCheck_2492_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2458_);
lean_dec(v_b_2450_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2492_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v_a_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_box(0);
v_a_2463_ = lean_array_uget_borrowed(v_as_2447_, v_i_2449_);
lean_inc(v_snd_2458_);
v___x_2464_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2445_, v_a_2446_, v_a_2463_, v_snd_2458_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2483_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2467_ = v___x_2464_;
v_isShared_2468_ = v_isSharedCheck_2483_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2464_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2483_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
if (lean_obj_tag(v_a_2465_) == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2465_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2469_);
v___x_2471_ = v___x_2460_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_snd_2458_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___x_2471_);
v___x_2473_ = v___x_2467_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; 
lean_del_object(v___x_2467_);
lean_dec(v_snd_2458_);
v_a_2476_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v_a_2465_, 1);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v_a_2476_);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2478_ = v___x_2460_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_a_2476_);
v___x_2478_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
size_t v___x_2479_; size_t v___x_2480_; 
v___x_2479_ = ((size_t)1ULL);
v___x_2480_ = lean_usize_add(v_i_2449_, v___x_2479_);
v_i_2449_ = v___x_2480_;
v_b_2450_ = v___x_2478_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_del_object(v___x_2460_);
lean_dec(v_snd_2458_);
v_a_2484_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2464_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2464_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2494_, lean_object* v_a_2495_, lean_object* v_as_2496_, lean_object* v_sz_2497_, lean_object* v_i_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
size_t v_sz_boxed_2505_; size_t v_i_boxed_2506_; lean_object* v_res_2507_; 
v_sz_boxed_2505_ = lean_unbox_usize(v_sz_2497_);
lean_dec(v_sz_2497_);
v_i_boxed_2506_ = lean_unbox_usize(v_i_2498_);
lean_dec(v_i_2498_);
v_res_2507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2494_, v_a_2495_, v_as_2496_, v_sz_boxed_2505_, v_i_boxed_2506_, v_b_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_as_2496_);
lean_dec_ref(v_a_2495_);
lean_dec_ref(v_init_2494_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2508_, lean_object* v_a_2509_, lean_object* v_n_2510_, lean_object* v_b_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2508_, v_a_2509_, v_n_2510_, v_b_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec_ref(v_n_2510_);
lean_dec_ref(v_a_2509_);
lean_dec_ref(v_init_2508_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2518_, lean_object* v_as_2519_, size_t v_sz_2520_, size_t v_i_2521_, lean_object* v_b_2522_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_usize_dec_lt(v_i_2521_, v_sz_2520_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_b_2522_);
return v___x_2525_;
}
else
{
lean_object* v_snd_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2544_; 
v_snd_2526_ = lean_ctor_get(v_b_2522_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_b_2522_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v_b_2522_, 0);
lean_dec(v_unused_2545_);
v___x_2528_ = v_b_2522_;
v_isShared_2529_ = v_isSharedCheck_2544_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_snd_2526_);
lean_dec(v_b_2522_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2544_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v_a_2532_; lean_object* v_a_2539_; 
v___x_2530_ = lean_box(0);
v_a_2539_ = lean_array_uget_borrowed(v_as_2519_, v_i_2521_);
if (lean_obj_tag(v_a_2539_) == 0)
{
v_a_2532_ = v_snd_2526_;
goto v___jp_2531_;
}
else
{
lean_object* v_val_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_val_2540_ = lean_ctor_get(v_a_2539_, 0);
v___x_2541_ = l_Lean_LocalDecl_fvarId(v_val_2540_);
v___x_2542_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2518_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec(v___x_2541_);
v_a_2532_ = v_snd_2526_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_push(v_snd_2526_, v___x_2541_);
v_a_2532_ = v___x_2543_;
goto v___jp_2531_;
}
}
v___jp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v_a_2532_);
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2534_ = v___x_2528_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2532_);
v___x_2534_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
size_t v___x_2535_; size_t v___x_2536_; 
v___x_2535_ = ((size_t)1ULL);
v___x_2536_ = lean_usize_add(v_i_2521_, v___x_2535_);
v_i_2521_ = v___x_2536_;
v_b_2522_ = v___x_2534_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2546_, lean_object* v_as_2547_, lean_object* v_sz_2548_, lean_object* v_i_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_){
_start:
{
size_t v_sz_boxed_2552_; size_t v_i_boxed_2553_; lean_object* v_res_2554_; 
v_sz_boxed_2552_ = lean_unbox_usize(v_sz_2548_);
lean_dec(v_sz_2548_);
v_i_boxed_2553_ = lean_unbox_usize(v_i_2549_);
lean_dec(v_i_2549_);
v_res_2554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2546_, v_as_2547_, v_sz_boxed_2552_, v_i_boxed_2553_, v_b_2550_);
lean_dec_ref(v_as_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2555_, lean_object* v_as_2556_, size_t v_sz_2557_, size_t v_i_2558_, lean_object* v_b_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = lean_usize_dec_lt(v_i_2558_, v_sz_2557_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_b_2559_);
return v___x_2566_;
}
else
{
lean_object* v_snd_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2585_; 
v_snd_2567_ = lean_ctor_get(v_b_2559_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_b_2559_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_b_2559_, 0);
lean_dec(v_unused_2586_);
v___x_2569_ = v_b_2559_;
v_isShared_2570_ = v_isSharedCheck_2585_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_snd_2567_);
lean_dec(v_b_2559_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2585_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v_a_2573_; lean_object* v_a_2580_; 
v___x_2571_ = lean_box(0);
v_a_2580_ = lean_array_uget_borrowed(v_as_2556_, v_i_2558_);
if (lean_obj_tag(v_a_2580_) == 0)
{
v_a_2573_ = v_snd_2567_;
goto v___jp_2572_;
}
else
{
lean_object* v_val_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_val_2581_ = lean_ctor_get(v_a_2580_, 0);
v___x_2582_ = l_Lean_LocalDecl_fvarId(v_val_2581_);
v___x_2583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2555_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_dec(v___x_2582_);
v_a_2573_ = v_snd_2567_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_array_push(v_snd_2567_, v___x_2582_);
v_a_2573_ = v___x_2584_;
goto v___jp_2572_;
}
}
v___jp_2572_:
{
lean_object* v___x_2575_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v_a_2573_);
lean_ctor_set(v___x_2569_, 0, v___x_2571_);
v___x_2575_ = v___x_2569_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_a_2573_);
v___x_2575_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
size_t v___x_2576_; size_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((size_t)1ULL);
v___x_2577_ = lean_usize_add(v_i_2558_, v___x_2576_);
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2555_, v_as_2556_, v_sz_2557_, v___x_2577_, v___x_2575_);
return v___x_2578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2587_, lean_object* v_as_2588_, lean_object* v_sz_2589_, lean_object* v_i_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
size_t v_sz_boxed_2597_; size_t v_i_boxed_2598_; lean_object* v_res_2599_; 
v_sz_boxed_2597_ = lean_unbox_usize(v_sz_2589_);
lean_dec(v_sz_2589_);
v_i_boxed_2598_ = lean_unbox_usize(v_i_2590_);
lean_dec(v_i_2590_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2587_, v_as_2588_, v_sz_boxed_2597_, v_i_boxed_2598_, v_b_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec_ref(v_as_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2600_, lean_object* v_t_2601_, lean_object* v_init_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_root_2608_; lean_object* v_tail_2609_; lean_object* v___x_2610_; 
v_root_2608_ = lean_ctor_get(v_t_2601_, 0);
v_tail_2609_ = lean_ctor_get(v_t_2601_, 1);
lean_inc_ref(v_init_2602_);
v___x_2610_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2602_, v_a_2600_, v_root_2608_, v_init_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref(v_init_2602_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2647_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2647_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2647_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; 
v_a_2615_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v_a_2611_, 1);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v_a_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; size_t v_sz_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
lean_del_object(v___x_2613_);
v_a_2619_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_a_2611_, 1);
v___x_2620_ = lean_box(0);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v_a_2619_);
v_sz_2622_ = lean_array_size(v_tail_2609_);
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2600_, v_tail_2609_, v_sz_2622_, v___x_2623_, v___x_2621_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2638_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v_fst_2629_; 
v_fst_2629_ = lean_ctor_get(v_a_2625_, 0);
if (lean_obj_tag(v_fst_2629_) == 0)
{
lean_object* v_snd_2630_; lean_object* v___x_2632_; 
v_snd_2630_ = lean_ctor_get(v_a_2625_, 1);
lean_inc(v_snd_2630_);
lean_dec(v_a_2625_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_snd_2630_);
v___x_2632_ = v___x_2627_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_snd_2630_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2636_; 
lean_inc_ref(v_fst_2629_);
lean_dec(v_a_2625_);
v_val_2634_ = lean_ctor_get(v_fst_2629_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v_fst_2629_, 1);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_val_2634_);
v___x_2636_ = v___x_2627_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_val_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2624_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2624_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2648_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2610_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2610_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2656_, lean_object* v_t_2657_, lean_object* v_init_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2656_, v_t_2657_, v_init_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v_t_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2667_, lean_object* v_mvarId_2668_, lean_object* v___f_2669_, lean_object* v___f_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_lctx_2676_; lean_object* v_decls_2677_; lean_object* v___x_2678_; 
v_lctx_2676_ = lean_ctor_get(v___y_2671_, 2);
v_decls_2677_ = lean_ctor_get(v_lctx_2676_, 1);
lean_inc_ref(v_decls_2677_);
v___x_2678_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2677_, v_candidates_2667_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_MVarId_getType(v_mvarId_2668_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v_a_2683_; uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___y_2687_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2681_, v___y_2672_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = l_Lean_Expr_hasFVar(v_a_2683_);
v___x_2685_ = lean_st_mk_ref(v_a_2679_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec(v_a_2683_);
lean_dec_ref(v___f_2670_);
v___x_2711_ = lean_box(0);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___x_2685_);
v___x_2712_ = lean_apply_7(v___f_2669_, v___x_2711_, v___x_2685_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, lean_box(0));
v___y_2687_ = v___x_2712_;
goto v___jp_2686_;
}
else
{
lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2714_ = 0;
v___x_2715_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2713_, v___f_2670_, v_a_2683_, v___x_2714_, v___x_2685_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___x_2685_);
v___x_2717_ = lean_apply_7(v___f_2669_, v_a_2716_, v___x_2685_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, lean_box(0));
v___y_2687_ = v___x_2717_;
goto v___jp_2686_;
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v___x_2685_);
lean_dec_ref(v_decls_2677_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___f_2669_);
v_a_2718_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2715_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2715_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
v___jp_2686_:
{
if (lean_obj_tag(v___y_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2702_; 
v_a_2688_ = lean_ctor_get(v___y_2687_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___y_2687_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2690_ = v___y_2687_;
v_isShared_2691_ = v_isSharedCheck_2702_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___y_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2702_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v_size_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2692_ = lean_st_ref_get(v___x_2685_);
lean_dec(v___x_2685_);
lean_dec(v___x_2692_);
v_size_2693_ = lean_ctor_get(v_a_2688_, 0);
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_nat_dec_eq(v_size_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_del_object(v___x_2690_);
v___x_2696_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2697_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2688_, v_decls_2677_, v___x_2696_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v_decls_2677_);
lean_dec(v_a_2688_);
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec(v_a_2688_);
lean_dec_ref(v_decls_2677_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
v___x_2698_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2698_);
v___x_2700_ = v___x_2690_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v___x_2685_);
lean_dec_ref(v_decls_2677_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
v_a_2703_ = lean_ctor_get(v___y_2687_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___y_2687_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___y_2687_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___y_2687_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2679_);
lean_dec_ref(v_decls_2677_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___f_2670_);
lean_dec_ref(v___f_2669_);
v_a_2726_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2680_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2680_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v_decls_2677_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v___f_2670_);
lean_dec_ref(v___f_2669_);
lean_dec(v_mvarId_2668_);
v_a_2734_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2678_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2678_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2742_, lean_object* v_mvarId_2743_, lean_object* v___f_2744_, lean_object* v___f_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2742_, v_mvarId_2743_, v___f_2744_, v___f_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___f_2760_; lean_object* v___f_2761_; lean_object* v_candidates_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; 
v___f_2760_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2761_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2762_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2754_);
v___f_2763_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2763_, 0, v_candidates_2762_);
lean_closure_set(v___f_2763_, 1, v_mvarId_2754_);
lean_closure_set(v___f_2763_, 2, v___f_2761_);
lean_closure_set(v___f_2763_, 3, v___f_2760_);
v___x_2764_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2754_, v___f_2763_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2772_, lean_object* v_m_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2773_, v_a_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2776_, lean_object* v_m_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2776_, v_m_2777_, v_a_2778_);
lean_dec(v_a_2778_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2780_, lean_object* v_m_2781_, lean_object* v_a_2782_, lean_object* v_b_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2781_, v_a_2782_, v_b_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2785_, lean_object* v_m_2786_, lean_object* v_a_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2786_, v_a_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2789_, lean_object* v_m_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v_res_2792_; lean_object* v_r_2793_; 
v_res_2792_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2789_, v_m_2790_, v_a_2791_);
lean_dec(v_a_2791_);
lean_dec_ref(v_m_2790_);
v_r_2793_ = lean_box(v_res_2792_);
return v_r_2793_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2794_, lean_object* v_a_2795_, lean_object* v_x_2796_){
_start:
{
uint8_t v___x_2797_; 
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2795_, v_x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_x_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2798_, v_a_2799_, v_x_2800_);
lean_dec(v_x_2800_);
lean_dec(v_a_2799_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2803_, lean_object* v_a_2804_, lean_object* v_x_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2804_, v_x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_a_2808_, lean_object* v_x_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2807_, v_a_2808_, v_x_2809_);
lean_dec(v_a_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2811_, lean_object* v_a_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2811_, v_a_2812_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2820_, lean_object* v_a_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2820_, v_a_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec(v_a_2821_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2829_, lean_object* v_data_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2832_, lean_object* v_a_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2832_, v_a_2833_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2841_, lean_object* v_a_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2841_, v_a_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v_a_2842_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2850_, lean_object* v_i_2851_, lean_object* v_source_2852_, lean_object* v_target_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2851_, v_source_2852_, v_target_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2855_, lean_object* v_as_2856_, size_t v_sz_2857_, size_t v_i_2858_, lean_object* v_b_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2855_, v_as_2856_, v_sz_2857_, v_i_2858_, v_b_2859_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2866_, lean_object* v_as_2867_, lean_object* v_sz_2868_, lean_object* v_i_2869_, lean_object* v_b_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2868_);
lean_dec(v_sz_2868_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2866_, v_as_2867_, v_sz_boxed_2876_, v_i_boxed_2877_, v_b_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_as_2867_);
lean_dec_ref(v_a_2866_);
return v_res_2878_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2879_, lean_object* v_m_2880_, lean_object* v_a_2881_){
_start:
{
uint8_t v___x_2882_; 
v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2880_, v_a_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2883_, lean_object* v_m_2884_, lean_object* v_a_2885_){
_start:
{
uint8_t v_res_2886_; lean_object* v_r_2887_; 
v_res_2886_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2883_, v_m_2884_, v_a_2885_);
lean_dec_ref(v_a_2885_);
lean_dec_ref(v_m_2884_);
v_r_2887_ = lean_box(v_res_2886_);
return v_r_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2888_, lean_object* v_m_2889_, lean_object* v_a_2890_, lean_object* v_b_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2889_, v_a_2890_, v_b_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2893_, lean_object* v_x_2894_, lean_object* v_x_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2894_, v_x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2897_, lean_object* v_as_2898_, size_t v_sz_2899_, size_t v_i_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2897_, v_as_2898_, v_sz_2899_, v_i_2900_, v_b_2901_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2908_, lean_object* v_as_2909_, lean_object* v_sz_2910_, lean_object* v_i_2911_, lean_object* v_b_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
size_t v_sz_boxed_2918_; size_t v_i_boxed_2919_; lean_object* v_res_2920_; 
v_sz_boxed_2918_ = lean_unbox_usize(v_sz_2910_);
lean_dec(v_sz_2910_);
v_i_boxed_2919_ = lean_unbox_usize(v_i_2911_);
lean_dec(v_i_2911_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2908_, v_as_2909_, v_sz_boxed_2918_, v_i_boxed_2919_, v_b_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v_as_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2920_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2921_, lean_object* v_a_2922_, lean_object* v_x_2923_){
_start:
{
uint8_t v___x_2924_; 
v___x_2924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2922_, v_x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2925_, lean_object* v_a_2926_, lean_object* v_x_2927_){
_start:
{
uint8_t v_res_2928_; lean_object* v_r_2929_; 
v_res_2928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2925_, v_a_2926_, v_x_2927_);
lean_dec(v_x_2927_);
lean_dec_ref(v_a_2926_);
v_r_2929_ = lean_box(v_res_2928_);
return v_r_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2930_, lean_object* v_data_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2933_, lean_object* v_i_2934_, lean_object* v_source_2935_, lean_object* v_target_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2934_, v_source_2935_, v_target_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2939_, v_x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = l_Lean_maxRecDepthErrorMessage;
v___x_2948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2950_ = l_Lean_MessageData_ofFormat(v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2952_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2953_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v___x_2951_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_ref_2954_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2962_, lean_object* v_ref_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2963_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_ref_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2971_, v_ref_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_2980_, lean_object* v_mvarId_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_toCold_2988_; lean_object* v_currRecDepth_2989_; lean_object* v_ref_2990_; uint16_t v_optionFlags_2991_; uint8_t v_suppressElabErrors_2992_; uint8_t v_isRecordingDeps_2993_; lean_object* v_maxRecDepth_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v_toCold_2988_ = lean_ctor_get(v_a_2985_, 0);
v_currRecDepth_2989_ = lean_ctor_get(v_a_2985_, 1);
v_ref_2990_ = lean_ctor_get(v_a_2985_, 2);
v_optionFlags_2991_ = lean_ctor_get_uint16(v_a_2985_, sizeof(void*)*3);
v_suppressElabErrors_2992_ = lean_ctor_get_uint8(v_a_2985_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2993_ = lean_ctor_get_uint8(v_a_2985_, sizeof(void*)*3 + 3);
v_maxRecDepth_3021_ = lean_ctor_get(v_toCold_2988_, 3);
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_nat_dec_eq(v_maxRecDepth_3021_, v___x_3022_);
if (v___x_3023_ == 0)
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_nat_dec_eq(v_currRecDepth_2989_, v_maxRecDepth_3021_);
if (v___x_3024_ == 0)
{
goto v___jp_2994_;
}
else
{
lean_object* v___x_3025_; 
lean_dec(v_mvarId_2981_);
lean_dec_ref(v_x_2980_);
lean_inc(v_ref_2990_);
v___x_3025_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2990_);
return v___x_3025_;
}
}
else
{
goto v___jp_2994_;
}
v___jp_2994_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2995_ = lean_unsigned_to_nat(1u);
v___x_2996_ = lean_nat_add(v_currRecDepth_2989_, v___x_2995_);
lean_inc(v_ref_2990_);
lean_inc_ref(v_toCold_2988_);
v___x_2997_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2997_, 0, v_toCold_2988_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
lean_ctor_set(v___x_2997_, 2, v_ref_2990_);
lean_ctor_set_uint16(v___x_2997_, sizeof(void*)*3, v_optionFlags_2991_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*3 + 2, v_suppressElabErrors_2992_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*3 + 3, v_isRecordingDeps_2993_);
lean_inc_ref(v_x_2980_);
lean_inc(v_a_2986_);
lean_inc_ref(v___x_2997_);
lean_inc(v_a_2984_);
lean_inc_ref(v_a_2983_);
lean_inc(v_mvarId_2981_);
v___x_2998_ = lean_apply_6(v_x_2980_, v_mvarId_2981_, v_a_2983_, v_a_2984_, v___x_2997_, v_a_2986_, lean_box(0));
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3012_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3012_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3012_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
if (lean_obj_tag(v_a_2999_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
lean_dec_ref_known(v___x_2997_, 3);
lean_dec_ref(v_x_2980_);
v___x_3003_ = lean_st_ref_take(v_a_2982_);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_array_push(v___x_3003_, v_mvarId_2981_);
v___x_3006_ = lean_st_ref_put(v_a_2982_, v___x_3005_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3004_);
v___x_3008_ = v___x_3001_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3004_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
else
{
lean_object* v_val_3010_; lean_object* v___x_3011_; 
lean_del_object(v___x_3001_);
lean_dec(v_mvarId_2981_);
v_val_3010_ = lean_ctor_get(v_a_2999_, 0);
lean_inc(v_val_3010_);
lean_dec_ref_known(v_a_2999_, 1);
v___x_3011_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_2980_, v_val_3010_, v_a_2982_, v_a_2983_, v_a_2984_, v___x_2997_, v_a_2986_);
lean_dec_ref_known(v___x_2997_, 3);
return v___x_3011_;
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref_known(v___x_2997_, 3);
lean_dec(v_mvarId_2981_);
lean_dec_ref(v_x_2980_);
v_a_3013_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2998_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2998_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3026_, lean_object* v_as_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
if (lean_obj_tag(v_as_3027_) == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v_x_3026_);
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
else
{
lean_object* v_head_3036_; lean_object* v_tail_3037_; lean_object* v___x_3038_; 
v_head_3036_ = lean_ctor_get(v_as_3027_, 0);
lean_inc(v_head_3036_);
v_tail_3037_ = lean_ctor_get(v_as_3027_, 1);
lean_inc(v_tail_3037_);
lean_dec_ref_known(v_as_3027_, 2);
lean_inc_ref(v_x_3026_);
v___x_3038_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3026_, v_head_3036_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_dec_ref_known(v___x_3038_, 1);
v_as_3027_ = v_tail_3037_;
goto _start;
}
else
{
lean_dec(v_tail_3037_);
lean_dec_ref(v_x_3026_);
return v___x_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3040_, lean_object* v_as_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3040_, v_as_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3049_, lean_object* v_mvarId_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3049_, v_mvarId_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3058_, lean_object* v_x_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3066_ = lean_st_mk_ref(v___x_3065_);
v___x_3067_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3059_, v_mvarId_3058_, v___x_3066_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3077_);
v___x_3069_ = v___x_3067_;
v_isShared_3070_ = v_isSharedCheck_3076_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v___x_3067_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3076_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3071_ = lean_st_ref_get(v___x_3066_);
lean_dec(v___x_3066_);
v___x_3072_ = lean_array_to_list(v___x_3071_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3072_);
v___x_3074_ = v___x_3069_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___x_3066_);
v_a_3078_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3067_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3067_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3086_, lean_object* v_x_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Meta_saturate(v_mvarId_3086_, v_x_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3094_, lean_object* v_msg_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
if (lean_obj_tag(v_mvarIds_3094_) == 1)
{
lean_object* v_tail_3101_; 
v_tail_3101_ = lean_ctor_get(v_mvarIds_3094_, 1);
if (lean_obj_tag(v_tail_3101_) == 0)
{
lean_object* v_head_3102_; lean_object* v___x_3103_; 
lean_dec_ref(v_msg_3095_);
v_head_3102_ = lean_ctor_get(v_mvarIds_3094_, 0);
lean_inc(v_head_3102_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_head_3102_);
return v___x_3103_;
}
else
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
return v___x_3104_;
}
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3106_, lean_object* v_msg_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Meta_exactlyOne(v_mvarIds_3106_, v_msg_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_);
lean_dec(v_a_3111_);
lean_dec_ref(v_a_3110_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_mvarIds_3106_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3114_, lean_object* v_msg_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
if (lean_obj_tag(v_mvarIds_3114_) == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v_msg_3115_);
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
return v___x_3122_;
}
else
{
lean_object* v_tail_3123_; 
v_tail_3123_ = lean_ctor_get(v_mvarIds_3114_, 1);
if (lean_obj_tag(v_tail_3123_) == 0)
{
lean_object* v_head_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v_msg_3115_);
v_head_3124_ = lean_ctor_get(v_mvarIds_3114_, 0);
lean_inc(v_head_3124_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_head_3124_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
return v___x_3126_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
return v___x_3127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3128_, lean_object* v_msg_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3128_, v_msg_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_mvarIds_3128_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3136_, size_t v_sz_3137_, size_t v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v___x_3145_; 
v___x_3145_ = lean_usize_dec_lt(v_i_3138_, v_sz_3137_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_b_3139_);
return v___x_3146_;
}
else
{
lean_object* v_snd_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3177_; 
v_snd_3147_ = lean_ctor_get(v_b_3139_, 1);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_b_3139_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v_b_3139_, 0);
lean_dec(v_unused_3178_);
v___x_3149_ = v_b_3139_;
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_snd_3147_);
lean_dec(v_b_3139_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3177_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v_a_3153_; lean_object* v_a_3160_; 
v___x_3151_ = lean_box(0);
v_a_3160_ = lean_array_uget_borrowed(v_as_3136_, v_i_3138_);
if (lean_obj_tag(v_a_3160_) == 0)
{
v_a_3153_ = v_snd_3147_;
goto v___jp_3152_;
}
else
{
lean_object* v_val_3161_; uint8_t v___x_3162_; 
v_val_3161_ = lean_ctor_get(v_a_3160_, 0);
v___x_3162_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3161_);
if (v___x_3162_ == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = l_Lean_LocalDecl_type(v_val_3161_);
v___x_3164_ = l_Lean_Meta_isProp(v___x_3163_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; uint8_t v___x_3166_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = lean_unbox(v_a_3165_);
lean_dec(v_a_3165_);
if (v___x_3166_ == 0)
{
v_a_3153_ = v_snd_3147_;
goto v___jp_3152_;
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = l_Lean_LocalDecl_fvarId(v_val_3161_);
v___x_3168_ = lean_array_push(v_snd_3147_, v___x_3167_);
v_a_3153_ = v___x_3168_;
goto v___jp_3152_;
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_del_object(v___x_3149_);
lean_dec(v_snd_3147_);
v_a_3169_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3164_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3164_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
v_a_3153_ = v_snd_3147_;
goto v___jp_3152_;
}
}
v___jp_3152_:
{
lean_object* v___x_3155_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v_a_3153_);
lean_ctor_set(v___x_3149_, 0, v___x_3151_);
v___x_3155_ = v___x_3149_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_a_3153_);
v___x_3155_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
size_t v___x_3156_; size_t v___x_3157_; 
v___x_3156_ = ((size_t)1ULL);
v___x_3157_ = lean_usize_add(v_i_3138_, v___x_3156_);
v_i_3138_ = v___x_3157_;
v_b_3139_ = v___x_3155_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3179_, lean_object* v_sz_3180_, lean_object* v_i_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
size_t v_sz_boxed_3188_; size_t v_i_boxed_3189_; lean_object* v_res_3190_; 
v_sz_boxed_3188_ = lean_unbox_usize(v_sz_3180_);
lean_dec(v_sz_3180_);
v_i_boxed_3189_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_res_3190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3179_, v_sz_boxed_3188_, v_i_boxed_3189_, v_b_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec_ref(v_as_3179_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3191_, size_t v_sz_3192_, size_t v_i_3193_, lean_object* v_b_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
uint8_t v___x_3200_; 
v___x_3200_ = lean_usize_dec_lt(v_i_3193_, v_sz_3192_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_b_3194_);
return v___x_3201_;
}
else
{
lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3232_; 
v_snd_3202_ = lean_ctor_get(v_b_3194_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_b_3194_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v_b_3194_, 0);
lean_dec(v_unused_3233_);
v___x_3204_ = v_b_3194_;
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v_b_3194_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v_a_3208_; lean_object* v_a_3215_; 
v___x_3206_ = lean_box(0);
v_a_3215_ = lean_array_uget_borrowed(v_as_3191_, v_i_3193_);
if (lean_obj_tag(v_a_3215_) == 0)
{
v_a_3208_ = v_snd_3202_;
goto v___jp_3207_;
}
else
{
lean_object* v_val_3216_; uint8_t v___x_3217_; 
v_val_3216_ = lean_ctor_get(v_a_3215_, 0);
v___x_3217_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = l_Lean_LocalDecl_type(v_val_3216_);
v___x_3219_ = l_Lean_Meta_isProp(v___x_3218_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; uint8_t v___x_3221_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3221_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3221_ == 0)
{
v_a_3208_ = v_snd_3202_;
goto v___jp_3207_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = l_Lean_LocalDecl_fvarId(v_val_3216_);
v___x_3223_ = lean_array_push(v_snd_3202_, v___x_3222_);
v_a_3208_ = v___x_3223_;
goto v___jp_3207_;
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_del_object(v___x_3204_);
lean_dec(v_snd_3202_);
v_a_3224_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3219_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3219_);
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
v_a_3208_ = v_snd_3202_;
goto v___jp_3207_;
}
}
v___jp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v_a_3208_);
lean_ctor_set(v___x_3204_, 0, v___x_3206_);
v___x_3210_ = v___x_3204_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_a_3208_);
v___x_3210_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
size_t v___x_3211_; size_t v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = ((size_t)1ULL);
v___x_3212_ = lean_usize_add(v_i_3193_, v___x_3211_);
v___x_3213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3191_, v_sz_3192_, v___x_3212_, v___x_3210_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3234_, lean_object* v_sz_3235_, lean_object* v_i_3236_, lean_object* v_b_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
size_t v_sz_boxed_3243_; size_t v_i_boxed_3244_; lean_object* v_res_3245_; 
v_sz_boxed_3243_ = lean_unbox_usize(v_sz_3235_);
lean_dec(v_sz_3235_);
v_i_boxed_3244_ = lean_unbox_usize(v_i_3236_);
lean_dec(v_i_3236_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3234_, v_sz_boxed_3243_, v_i_boxed_3244_, v_b_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v_as_3234_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3246_, lean_object* v_n_3247_, lean_object* v_b_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
if (lean_obj_tag(v_n_3247_) == 0)
{
lean_object* v_cs_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; size_t v_sz_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v_cs_3254_ = lean_ctor_get(v_n_3247_, 0);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v_b_3248_);
v_sz_3257_ = lean_array_size(v_cs_3254_);
v___x_3258_ = ((size_t)0ULL);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3246_, v_cs_3254_, v_sz_3257_, v___x_3258_, v___x_3256_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3274_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3262_ = v___x_3259_;
v_isShared_3263_ = v_isSharedCheck_3274_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3274_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_fst_3264_; 
v_fst_3264_ = lean_ctor_get(v_a_3260_, 0);
if (lean_obj_tag(v_fst_3264_) == 0)
{
lean_object* v_snd_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v_snd_3265_ = lean_ctor_get(v_a_3260_, 1);
lean_inc(v_snd_3265_);
lean_dec(v_a_3260_);
v___x_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_snd_3265_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v___x_3266_);
v___x_3268_ = v___x_3262_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
else
{
lean_object* v_val_3270_; lean_object* v___x_3272_; 
lean_inc_ref(v_fst_3264_);
lean_dec(v_a_3260_);
v_val_3270_ = lean_ctor_get(v_fst_3264_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v_fst_3264_, 1);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_val_3270_);
v___x_3272_ = v___x_3262_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_val_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
v_a_3275_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3259_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3259_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_object* v_vs_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; size_t v_sz_3286_; size_t v___x_3287_; lean_object* v___x_3288_; 
v_vs_3283_ = lean_ctor_get(v_n_3247_, 0);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_b_3248_);
v_sz_3286_ = lean_array_size(v_vs_3283_);
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3283_, v_sz_3286_, v___x_3287_, v___x_3285_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3303_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3291_ = v___x_3288_;
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3303_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v_fst_3293_; 
v_fst_3293_ = lean_ctor_get(v_a_3289_, 0);
if (lean_obj_tag(v_fst_3293_) == 0)
{
lean_object* v_snd_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v_snd_3294_ = lean_ctor_get(v_a_3289_, 1);
lean_inc(v_snd_3294_);
lean_dec(v_a_3289_);
v___x_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3295_, 0, v_snd_3294_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3295_);
v___x_3297_ = v___x_3291_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
else
{
lean_object* v_val_3299_; lean_object* v___x_3301_; 
lean_inc_ref(v_fst_3293_);
lean_dec(v_a_3289_);
v_val_3299_ = lean_ctor_get(v_fst_3293_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v_fst_3293_, 1);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v_val_3299_);
v___x_3301_ = v___x_3291_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_val_3299_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
v_a_3304_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3288_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3288_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3312_, lean_object* v_as_3313_, size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_b_3316_);
return v___x_3323_;
}
else
{
lean_object* v_snd_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3358_; 
v_snd_3324_ = lean_ctor_get(v_b_3316_, 1);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_b_3316_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v_b_3316_, 0);
lean_dec(v_unused_3359_);
v___x_3326_ = v_b_3316_;
v_isShared_3327_ = v_isSharedCheck_3358_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_snd_3324_);
lean_dec(v_b_3316_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3358_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3330_; 
v___x_3328_ = lean_box(0);
v_a_3329_ = lean_array_uget_borrowed(v_as_3313_, v_i_3315_);
lean_inc(v_snd_3324_);
v___x_3330_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3312_, v_a_3329_, v_snd_3324_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3349_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3349_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3349_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
if (lean_obj_tag(v_a_3331_) == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_a_3331_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3335_);
v___x_3337_ = v___x_3326_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_snd_3324_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3337_);
v___x_3339_ = v___x_3333_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; 
lean_del_object(v___x_3333_);
lean_dec(v_snd_3324_);
v_a_3342_ = lean_ctor_get(v_a_3331_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v_a_3331_, 1);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 1, v_a_3342_);
lean_ctor_set(v___x_3326_, 0, v___x_3328_);
v___x_3344_ = v___x_3326_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_a_3342_);
v___x_3344_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
size_t v___x_3345_; size_t v___x_3346_; 
v___x_3345_ = ((size_t)1ULL);
v___x_3346_ = lean_usize_add(v_i_3315_, v___x_3345_);
v_i_3315_ = v___x_3346_;
v_b_3316_ = v___x_3344_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_del_object(v___x_3326_);
lean_dec(v_snd_3324_);
v_a_3350_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3330_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3330_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3360_, lean_object* v_as_3361_, lean_object* v_sz_3362_, lean_object* v_i_3363_, lean_object* v_b_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
size_t v_sz_boxed_3370_; size_t v_i_boxed_3371_; lean_object* v_res_3372_; 
v_sz_boxed_3370_ = lean_unbox_usize(v_sz_3362_);
lean_dec(v_sz_3362_);
v_i_boxed_3371_ = lean_unbox_usize(v_i_3363_);
lean_dec(v_i_3363_);
v_res_3372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3360_, v_as_3361_, v_sz_boxed_3370_, v_i_boxed_3371_, v_b_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec_ref(v_as_3361_);
lean_dec_ref(v_init_3360_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3373_, lean_object* v_n_3374_, lean_object* v_b_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3373_, v_n_3374_, v_b_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec_ref(v_n_3374_);
lean_dec_ref(v_init_3373_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3382_, size_t v_sz_3383_, size_t v_i_3384_, lean_object* v_b_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_usize_dec_lt(v_i_3384_, v_sz_3383_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v_b_3385_);
return v___x_3392_;
}
else
{
lean_object* v_snd_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3423_; 
v_snd_3393_ = lean_ctor_get(v_b_3385_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_b_3385_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v_b_3385_, 0);
lean_dec(v_unused_3424_);
v___x_3395_ = v_b_3385_;
v_isShared_3396_ = v_isSharedCheck_3423_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snd_3393_);
lean_dec(v_b_3385_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3423_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v_a_3399_; lean_object* v_a_3406_; 
v___x_3397_ = lean_box(0);
v_a_3406_ = lean_array_uget_borrowed(v_as_3382_, v_i_3384_);
if (lean_obj_tag(v_a_3406_) == 0)
{
v_a_3399_ = v_snd_3393_;
goto v___jp_3398_;
}
else
{
lean_object* v_val_3407_; uint8_t v___x_3408_; 
v_val_3407_ = lean_ctor_get(v_a_3406_, 0);
v___x_3408_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = l_Lean_LocalDecl_type(v_val_3407_);
v___x_3410_ = l_Lean_Meta_isProp(v___x_3409_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; uint8_t v___x_3412_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v___x_3412_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3412_ == 0)
{
v_a_3399_ = v_snd_3393_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = l_Lean_LocalDecl_fvarId(v_val_3407_);
v___x_3414_ = lean_array_push(v_snd_3393_, v___x_3413_);
v_a_3399_ = v___x_3414_;
goto v___jp_3398_;
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_del_object(v___x_3395_);
lean_dec(v_snd_3393_);
v_a_3415_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3410_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3410_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
v_a_3399_ = v_snd_3393_;
goto v___jp_3398_;
}
}
v___jp_3398_:
{
lean_object* v___x_3401_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v_a_3399_);
lean_ctor_set(v___x_3395_, 0, v___x_3397_);
v___x_3401_ = v___x_3395_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_a_3399_);
v___x_3401_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
size_t v___x_3402_; size_t v___x_3403_; 
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3384_, v___x_3402_);
v_i_3384_ = v___x_3403_;
v_b_3385_ = v___x_3401_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3425_, lean_object* v_sz_3426_, lean_object* v_i_3427_, lean_object* v_b_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3426_);
lean_dec(v_sz_3426_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3425_, v_sz_boxed_3434_, v_i_boxed_3435_, v_b_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v_as_3425_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3437_, size_t v_sz_3438_, size_t v_i_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3439_, v_sz_3438_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_b_3440_);
return v___x_3447_;
}
else
{
lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3478_; 
v_snd_3448_ = lean_ctor_get(v_b_3440_, 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_b_3440_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v_b_3440_, 0);
lean_dec(v_unused_3479_);
v___x_3450_ = v_b_3440_;
v_isShared_3451_ = v_isSharedCheck_3478_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_dec(v_b_3440_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3478_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v_a_3454_; lean_object* v_a_3461_; 
v___x_3452_ = lean_box(0);
v_a_3461_ = lean_array_uget_borrowed(v_as_3437_, v_i_3439_);
if (lean_obj_tag(v_a_3461_) == 0)
{
v_a_3454_ = v_snd_3448_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3462_; uint8_t v___x_3463_; 
v_val_3462_ = lean_ctor_get(v_a_3461_, 0);
v___x_3463_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = l_Lean_LocalDecl_type(v_val_3462_);
v___x_3465_ = l_Lean_Meta_isProp(v___x_3464_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; uint8_t v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = lean_unbox(v_a_3466_);
lean_dec(v_a_3466_);
if (v___x_3467_ == 0)
{
v_a_3454_ = v_snd_3448_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = l_Lean_LocalDecl_fvarId(v_val_3462_);
v___x_3469_ = lean_array_push(v_snd_3448_, v___x_3468_);
v_a_3454_ = v___x_3469_;
goto v___jp_3453_;
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_del_object(v___x_3450_);
lean_dec(v_snd_3448_);
v_a_3470_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3465_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3465_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
v_a_3454_ = v_snd_3448_;
goto v___jp_3453_;
}
}
v___jp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v_a_3454_);
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3456_ = v___x_3450_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_a_3454_);
v___x_3456_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
size_t v___x_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3439_, v___x_3457_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3437_, v_sz_3438_, v___x_3458_, v___x_3456_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3480_, lean_object* v_sz_3481_, lean_object* v_i_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
size_t v_sz_boxed_3489_; size_t v_i_boxed_3490_; lean_object* v_res_3491_; 
v_sz_boxed_3489_ = lean_unbox_usize(v_sz_3481_);
lean_dec(v_sz_3481_);
v_i_boxed_3490_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_res_3491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3480_, v_sz_boxed_3489_, v_i_boxed_3490_, v_b_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_as_3480_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3492_, lean_object* v_init_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_root_3499_; lean_object* v_tail_3500_; lean_object* v___x_3501_; 
v_root_3499_ = lean_ctor_get(v_t_3492_, 0);
v_tail_3500_ = lean_ctor_get(v_t_3492_, 1);
lean_inc_ref(v_init_3493_);
v___x_3501_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3493_, v_root_3499_, v_init_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec_ref(v_init_3493_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3538_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3538_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3538_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
if (lean_obj_tag(v_a_3502_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; 
v_a_3506_ = lean_ctor_get(v_a_3502_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v_a_3502_, 1);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v_a_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; size_t v_sz_3513_; size_t v___x_3514_; lean_object* v___x_3515_; 
lean_del_object(v___x_3504_);
v_a_3510_ = lean_ctor_get(v_a_3502_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v_a_3502_, 1);
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v_a_3510_);
v_sz_3513_ = lean_array_size(v_tail_3500_);
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3500_, v_sz_3513_, v___x_3514_, v___x_3512_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3529_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_fst_3520_; 
v_fst_3520_ = lean_ctor_get(v_a_3516_, 0);
if (lean_obj_tag(v_fst_3520_) == 0)
{
lean_object* v_snd_3521_; lean_object* v___x_3523_; 
v_snd_3521_ = lean_ctor_get(v_a_3516_, 1);
lean_inc(v_snd_3521_);
lean_dec(v_a_3516_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_snd_3521_);
v___x_3523_ = v___x_3518_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_snd_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
else
{
lean_object* v_val_3525_; lean_object* v___x_3527_; 
lean_inc_ref(v_fst_3520_);
lean_dec(v_a_3516_);
v_val_3525_ = lean_ctor_get(v_fst_3520_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_fst_3520_, 1);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_val_3525_);
v___x_3527_ = v___x_3518_;
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
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
v_a_3530_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3515_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3515_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v_a_3539_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3501_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3501_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3547_, lean_object* v_init_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3547_, v_init_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_t_3547_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_lctx_3560_; lean_object* v_decls_3561_; lean_object* v_result_3562_; lean_object* v___x_3563_; 
v_lctx_3560_ = lean_ctor_get(v_a_3555_, 2);
v_decls_3561_ = lean_ctor_get(v_lctx_3560_, 1);
v_result_3562_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3563_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3561_, v_result_3562_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Meta_getPropHyps(v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
return v_res_3569_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3574_ = l_Lean_MessageData_ofFormat(v___x_3573_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3577_, lean_object* v___x_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; 
lean_inc(v___x_3578_);
lean_inc(v_mvarId_3577_);
v___x_3584_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3577_, v___x_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v___x_3585_; 
lean_dec_ref_known(v___x_3584_, 1);
lean_inc(v_mvarId_3577_);
v___x_3585_ = l_Lean_MVarId_getType(v_mvarId_3577_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
v___x_3587_ = lean_box(0);
v___x_3588_ = l_Lean_Meta_synthInstance(v_a_3586_, v___x_3587_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
lean_inc(v_mvarId_3577_);
v___x_3590_ = l_Lean_mkMVar(v_mvarId_3577_);
v___x_3591_ = l_Lean_Meta_isExprDefEq(v___x_3590_, v_a_3589_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3603_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3594_ = v___x_3591_;
v_isShared_3595_ = v_isSharedCheck_3603_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3603_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_unbox(v_a_3592_);
lean_dec(v_a_3592_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_del_object(v___x_3594_);
v___x_3597_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3598_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3578_, v_mvarId_3577_, v___x_3597_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
return v___x_3598_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec(v___x_3578_);
lean_dec(v_mvarId_3577_);
v___x_3599_ = lean_box(0);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3599_);
v___x_3601_ = v___x_3594_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v___x_3578_);
lean_dec(v_mvarId_3577_);
v_a_3604_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3591_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3591_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v___x_3578_);
lean_dec(v_mvarId_3577_);
v_a_3612_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3588_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3588_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
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
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v___x_3578_);
lean_dec(v_mvarId_3577_);
v_a_3620_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3585_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3585_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
else
{
lean_dec(v___x_3578_);
lean_dec(v_mvarId_3577_);
return v___x_3584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3628_, lean_object* v___x_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3628_, v___x_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___f_3646_; lean_object* v___x_3647_; 
v___x_3645_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3639_);
v___f_3646_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3646_, 0, v_mvarId_3639_);
lean_closure_set(v___f_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3639_, v___f_3646_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_MVarId_inferInstance(v_mvarId_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object* v_x_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_obj_tag_nat(v_x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Meta_TacticResultCNM_ctorIdx___impl(v_x_3657_);
lean_dec(v_x_3657_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3659_, lean_object* v_k_3660_){
_start:
{
if (lean_obj_tag(v_t_3659_) == 2)
{
lean_object* v_mvarId_3661_; lean_object* v___x_3662_; 
v_mvarId_3661_ = lean_ctor_get(v_t_3659_, 0);
lean_inc(v_mvarId_3661_);
lean_dec_ref_known(v_t_3659_, 1);
v___x_3662_ = lean_apply_1(v_k_3660_, v_mvarId_3661_);
return v___x_3662_;
}
else
{
lean_dec(v_t_3659_);
return v_k_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3663_, lean_object* v_ctorIdx_3664_, lean_object* v_t_3665_, lean_object* v_h_3666_, lean_object* v_k_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3665_, v_k_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3669_, lean_object* v_ctorIdx_3670_, lean_object* v_t_3671_, lean_object* v_h_3672_, lean_object* v_k_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3669_, v_ctorIdx_3670_, v_t_3671_, v_h_3672_, v_k_3673_);
lean_dec(v_ctorIdx_3670_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3675_, lean_object* v_closed_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3675_, v_closed_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3678_, lean_object* v_t_3679_, lean_object* v_h_3680_, lean_object* v_closed_3681_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3679_, v_closed_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3683_, lean_object* v_noChange_3684_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3683_, v_noChange_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3686_, lean_object* v_t_3687_, lean_object* v_h_3688_, lean_object* v_noChange_3689_){
_start:
{
lean_object* v___x_3690_; 
v___x_3690_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3687_, v_noChange_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3691_, lean_object* v_modified_3692_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3691_, v_modified_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3694_, lean_object* v_t_3695_, lean_object* v_h_3696_, lean_object* v_modified_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3695_, v_modified_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_a_3709_; lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_MVarId_getType(v_g_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
v___x_3718_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3719_ = lean_unsigned_to_nat(1u);
v___x_3720_ = lean_mk_empty_array_with_capacity(v___x_3719_);
v___x_3721_ = lean_array_push(v___x_3720_, v_a_3717_);
v___x_3722_ = l_Lean_Meta_mkAppM(v___x_3718_, v___x_3721_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = lean_box(0);
v___x_3725_ = l_Lean_Meta_synthInstance(v_a_3723_, v___x_3724_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3734_; 
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v___x_3725_, 0);
lean_dec(v_unused_3735_);
v___x_3727_ = v___x_3725_;
v_isShared_3728_ = v_isSharedCheck_3734_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v___x_3725_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3734_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3729_ = 1;
v___x_3730_ = lean_box(v___x_3729_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3730_);
v___x_3732_ = v___x_3727_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
else
{
lean_object* v_a_3736_; 
v_a_3736_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3725_, 1);
v_a_3709_ = v_a_3736_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_a_3737_; 
v_a_3737_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3722_, 1);
v_a_3709_ = v_a_3737_;
goto v___jp_3708_;
}
}
else
{
lean_object* v_a_3738_; 
v_a_3738_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3716_, 1);
v_a_3709_ = v_a_3738_;
goto v___jp_3708_;
}
v___jp_3708_:
{
uint8_t v___x_3710_; 
v___x_3710_ = l_Lean_Exception_isInterrupt(v_a_3709_);
if (v___x_3710_ == 0)
{
uint8_t v___x_3711_; 
lean_inc_ref(v_a_3709_);
v___x_3711_ = l_Lean_Exception_isRuntime(v_a_3709_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v_a_3709_);
v___x_3712_ = lean_box(v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3714_, 0, v_a_3709_);
return v___x_3714_;
}
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v_a_3709_);
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_MVarId_isSubsingleton(v_g_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3766_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3763_, v___x_3764_, v___x_3765_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3768_;
}
}
lean_object* runtime_initialize_Lean_Util_ForEachExprWhere(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PPGoal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
