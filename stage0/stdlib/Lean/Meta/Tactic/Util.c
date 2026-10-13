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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*, uint8_t);
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
size_t v_x_1022__boxed_903_; size_t v_x_1023__boxed_904_; lean_object* v_res_905_; 
v_x_1022__boxed_903_ = lean_unbox_usize(v_x_899_);
lean_dec(v_x_899_);
v_x_1023__boxed_904_ = lean_unbox_usize(v_x_900_);
lean_dec(v_x_900_);
v_res_905_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_898_, v_x_1022__boxed_903_, v_x_1023__boxed_904_, v_x_901_, v_x_902_);
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
lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v_cache_919_; lean_object* v_zetaDeltaFVarIds_920_; lean_object* v_postponed_921_; lean_object* v_diag_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_952_; 
v___x_917_ = lean_st_ref_take(v___y_915_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
v_cache_919_ = lean_ctor_get(v___x_917_, 1);
v_zetaDeltaFVarIds_920_ = lean_ctor_get(v___x_917_, 2);
v_postponed_921_ = lean_ctor_get(v___x_917_, 3);
v_diag_922_ = lean_ctor_get(v___x_917_, 4);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_952_ == 0)
{
v___x_924_ = v___x_917_;
v_isShared_925_ = v_isSharedCheck_952_;
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
v_isShared_925_ = v_isSharedCheck_952_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_depth_926_; lean_object* v_levelAssignDepth_927_; lean_object* v_lmvarCounter_928_; lean_object* v_mvarCounter_929_; lean_object* v_lDecls_930_; lean_object* v_decls_931_; lean_object* v_userNames_932_; lean_object* v_lAssignment_933_; lean_object* v_eAssignment_934_; lean_object* v_dAssignment_935_; lean_object* v_instanceTypedMVars_936_; lean_object* v_synthNormMemo_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_951_; 
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
v_instanceTypedMVars_936_ = lean_ctor_get(v_mctx_918_, 10);
v_synthNormMemo_937_ = lean_ctor_get(v_mctx_918_, 11);
v_isSharedCheck_951_ = !lean_is_exclusive(v_mctx_918_);
if (v_isSharedCheck_951_ == 0)
{
v___x_939_ = v_mctx_918_;
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_synthNormMemo_937_);
lean_inc(v_instanceTypedMVars_936_);
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
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_951_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_box(0);
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_934_, v_mvarId_913_, v_val_914_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 8, v___x_942_);
v___x_944_ = v___x_939_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_depth_926_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_levelAssignDepth_927_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_lmvarCounter_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_mvarCounter_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_lDecls_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_decls_931_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_userNames_932_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_lAssignment_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 9, v_dAssignment_935_);
lean_ctor_set(v_reuseFailAlloc_950_, 10, v_instanceTypedMVars_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 11, v_synthNormMemo_937_);
v___x_944_ = v_reuseFailAlloc_950_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_944_);
v___x_946_ = v___x_924_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_cache_919_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_zetaDeltaFVarIds_920_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_postponed_921_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_diag_922_);
v___x_946_ = v_reuseFailAlloc_949_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_st_ref_put(v___y_915_, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_941_);
return v___x_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(lean_object* v_mvarId_953_, lean_object* v_val_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_953_, v_val_954_, v___y_955_);
lean_dec(v___y_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0(lean_object* v_mvarId_958_, lean_object* v___x_959_, uint8_t v_synthetic_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; 
lean_inc(v_mvarId_958_);
v___x_966_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_958_, v___x_959_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
lean_dec_ref_known(v___x_966_, 1);
lean_inc(v_mvarId_958_);
v___x_967_ = l_Lean_MVarId_getType(v_mvarId_958_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v___x_969_ = 1;
v___x_970_ = l_Lean_Meta_mkLabeledSorry(v_a_968_, v_synthetic_960_, v___x_969_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_958_, v_a_971_, v___y_962_);
return v___x_972_;
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v_mvarId_958_);
v_a_973_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_970_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_mvarId_958_);
v_a_981_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_967_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_967_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_dec(v_mvarId_958_);
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___lam__0___boxed(lean_object* v_mvarId_989_, lean_object* v___x_990_, lean_object* v_synthetic_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v_synthetic_boxed_997_; lean_object* v_res_998_; 
v_synthetic_boxed_997_ = lean_unbox(v_synthetic_991_);
v_res_998_ = l_Lean_MVarId_admit___lam__0(v_mvarId_989_, v___x_990_, v_synthetic_boxed_997_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit(lean_object* v_mvarId_1002_, uint8_t v_synthetic_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; 
v___x_1009_ = ((lean_object*)(l_Lean_MVarId_admit___closed__1));
v___x_1010_ = lean_box(v_synthetic_1003_);
lean_inc(v_mvarId_1002_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_MVarId_admit___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1011_, 0, v_mvarId_1002_);
lean_closure_set(v___f_1011_, 1, v___x_1009_);
lean_closure_set(v___f_1011_, 2, v___x_1010_);
v___x_1012_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_1002_, v___f_1011_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_admit___boxed(lean_object* v_mvarId_1013_, lean_object* v_synthetic_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_synthetic_boxed_1020_; lean_object* v_res_1021_; 
v_synthetic_boxed_1020_ = lean_unbox(v_synthetic_1014_);
v_res_1021_ = l_Lean_MVarId_admit(v_mvarId_1013_, v_synthetic_boxed_1020_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(lean_object* v_mvarId_1022_, lean_object* v_val_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(v_mvarId_1022_, v_val_1023_, v___y_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(lean_object* v_mvarId_1030_, lean_object* v_val_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(v_mvarId_1030_, v_val_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, size_t v_x_1045_, size_t v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_1343__boxed_1056_; size_t v_x_1344__boxed_1057_; lean_object* v_res_1058_; 
v_x_1343__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_x_1344__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_1050_, v_x_1051_, v_x_1343__boxed_1056_, v_x_1344__boxed_1057_, v_x_1054_, v_x_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b2_1059_, lean_object* v_n_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1060_, v_k_1061_, v_v_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1064_, size_t v_depth_1065_, lean_object* v_keys_1066_, lean_object* v_vals_1067_, lean_object* v_heq_1068_, lean_object* v_i_1069_, lean_object* v_entries_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1065_, v_keys_1066_, v_vals_1067_, v_i_1069_, v_entries_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_depth_1073_, lean_object* v_keys_1074_, lean_object* v_vals_1075_, lean_object* v_heq_1076_, lean_object* v_i_1077_, lean_object* v_entries_1078_){
_start:
{
size_t v_depth_boxed_1079_; lean_object* v_res_1080_; 
v_depth_boxed_1079_ = lean_unbox_usize(v_depth_1073_);
lean_dec(v_depth_1073_);
v_res_1080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1072_, v_depth_boxed_1079_, v_keys_1074_, v_vals_1075_, v_heq_1076_, v_i_1077_, v_entries_1078_);
lean_dec_ref(v_vals_1075_);
lean_dec_ref(v_keys_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType(lean_object* v_mvarId_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___x_1093_; 
lean_inc(v_mvarId_1087_);
v___x_1093_ = l_Lean_MVarId_getType(v_mvarId_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l_Lean_Expr_headBeta(v_a_1094_);
v___x_1096_ = l_Lean_MVarId_setType___redArg(v_mvarId_1087_, v___x_1095_, v_a_1089_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_mvarId_1087_);
v_a_1097_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_headBetaType___boxed(lean_object* v_mvarId_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_MVarId_headBetaType(v_mvarId_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(lean_object* v_a_1112_, lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
uint8_t v___x_1114_; 
v___x_1114_ = 0;
return v___x_1114_;
}
else
{
lean_object* v_key_1115_; lean_object* v_tail_1116_; uint8_t v___x_1117_; 
v_key_1115_ = lean_ctor_get(v_x_1113_, 0);
v_tail_1116_ = lean_ctor_get(v_x_1113_, 2);
v___x_1117_ = l_Lean_instBEqFVarId_beq(v_key_1115_, v_a_1112_);
if (v___x_1117_ == 0)
{
v_x_1113_ = v_tail_1116_;
goto _start;
}
else
{
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1119_, v_x_1120_);
lean_dec(v_x_1120_);
lean_dec(v_a_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
return v_x_1124_;
}
else
{
lean_object* v_key_1125_; lean_object* v_value_1126_; lean_object* v_tail_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v_key_1125_ = lean_ctor_get(v_x_1124_, 0);
v_value_1126_ = lean_ctor_get(v_x_1124_, 1);
v_tail_1127_ = lean_ctor_get(v_x_1124_, 2);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v_x_1124_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_tail_1127_);
lean_inc(v_value_1126_);
lean_inc(v_key_1125_);
lean_dec(v_x_1124_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_instBEqFVarId_beq(v_key_1125_, v_a_1123_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1123_, v_tail_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 2, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_key_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_value_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
else
{
lean_del_object(v___x_1129_);
lean_dec(v_value_1126_);
lean_dec(v_key_1125_);
return v_tail_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(lean_object* v_a_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1137_, v_x_1138_);
lean_dec(v_a_1137_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object* v_m_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_size_1142_; lean_object* v_buckets_1143_; lean_object* v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v_fold_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v_bkt_1157_; uint8_t v___x_1158_; 
v_size_1142_ = lean_ctor_get(v_m_1140_, 0);
v_buckets_1143_ = lean_ctor_get(v_m_1140_, 1);
v___x_1144_ = lean_array_get_size(v_buckets_1143_);
v___x_1145_ = l_Lean_instHashableFVarId_hash(v_a_1141_);
v___x_1146_ = 32ULL;
v___x_1147_ = lean_uint64_shift_right(v___x_1145_, v___x_1146_);
v_fold_1148_ = lean_uint64_xor(v___x_1145_, v___x_1147_);
v___x_1149_ = 16ULL;
v___x_1150_ = lean_uint64_shift_right(v_fold_1148_, v___x_1149_);
v___x_1151_ = lean_uint64_xor(v_fold_1148_, v___x_1150_);
v___x_1152_ = lean_uint64_to_usize(v___x_1151_);
v___x_1153_ = lean_usize_of_nat(v___x_1144_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_sub(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_usize_land(v___x_1152_, v___x_1155_);
v_bkt_1157_ = lean_array_uget_borrowed(v_buckets_1143_, v___x_1156_);
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1141_, v_bkt_1157_);
if (v___x_1158_ == 0)
{
return v_m_1140_;
}
else
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1171_; 
lean_inc(v_bkt_1157_);
lean_inc_ref(v_buckets_1143_);
lean_inc(v_size_1142_);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_m_1140_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; lean_object* v_unused_1173_; 
v_unused_1172_ = lean_ctor_get(v_m_1140_, 1);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_m_1140_, 0);
lean_dec(v_unused_1173_);
v___x_1160_ = v_m_1140_;
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_m_1140_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v_buckets_x27_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1162_ = lean_box(0);
v_buckets_x27_1163_ = lean_array_uset(v_buckets_1143_, v___x_1156_, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_nat_sub(v_size_1142_, v___x_1164_);
lean_dec(v_size_1142_);
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_1141_, v_bkt_1157_);
v___x_1167_ = lean_array_uset(v_buckets_x27_1163_, v___x_1156_, v___x_1166_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1167_);
lean_ctor_set(v___x_1160_, 0, v___x_1165_);
v___x_1169_ = v___x_1160_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_1174_, v_a_1175_);
lean_dec(v_a_1175_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0(lean_object* v_e_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1184_ = lean_st_ref_take(v___y_1178_);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_Lean_Expr_fvarId_x21(v_e_1177_);
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1184_, v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_st_ref_put(v___y_1178_, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(lean_object* v_e_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_MVarId_getNondepPropHyps___lam__0(v_e_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v_e_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1(lean_object* v_____r_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_st_ref_get(v___y_1199_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(lean_object* v_____r_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_MVarId_getNondepPropHyps___lam__1(v_____r_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
return v_res_1214_;
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
v___x_1221_ = ((size_t)8191ULL);
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
v___x_1235_ = lean_st_ref_put(v_a_1216_, v___x_1234_);
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
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_nbuckets_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1298_ = lean_array_get_size(v_data_1297_);
v___x_1299_ = lean_unsigned_to_nat(2u);
v_nbuckets_1300_ = lean_nat_mul(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_mk_array(v_nbuckets_1300_, v___x_1302_);
v___x_1304_ = lean_array_propagate_mark(v_data_1297_, v___x_1303_);
v___x_1305_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_1301_, v_data_1297_, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(lean_object* v_m_1306_, lean_object* v_a_1307_, lean_object* v_b_1308_){
_start:
{
lean_object* v_size_1309_; lean_object* v_buckets_1310_; lean_object* v___x_1311_; uint64_t v___x_1312_; uint64_t v___x_1313_; uint64_t v___x_1314_; uint64_t v_fold_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; size_t v___x_1319_; size_t v___x_1320_; size_t v___x_1321_; size_t v___x_1322_; size_t v___x_1323_; lean_object* v_bkt_1324_; uint8_t v___x_1325_; 
v_size_1309_ = lean_ctor_get(v_m_1306_, 0);
v_buckets_1310_ = lean_ctor_get(v_m_1306_, 1);
v___x_1311_ = lean_array_get_size(v_buckets_1310_);
v___x_1312_ = l_Lean_Expr_hash(v_a_1307_);
v___x_1313_ = 32ULL;
v___x_1314_ = lean_uint64_shift_right(v___x_1312_, v___x_1313_);
v_fold_1315_ = lean_uint64_xor(v___x_1312_, v___x_1314_);
v___x_1316_ = 16ULL;
v___x_1317_ = lean_uint64_shift_right(v_fold_1315_, v___x_1316_);
v___x_1318_ = lean_uint64_xor(v_fold_1315_, v___x_1317_);
v___x_1319_ = lean_uint64_to_usize(v___x_1318_);
v___x_1320_ = lean_usize_of_nat(v___x_1311_);
v___x_1321_ = ((size_t)1ULL);
v___x_1322_ = lean_usize_sub(v___x_1320_, v___x_1321_);
v___x_1323_ = lean_usize_land(v___x_1319_, v___x_1322_);
v_bkt_1324_ = lean_array_uget_borrowed(v_buckets_1310_, v___x_1323_);
v___x_1325_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1307_, v_bkt_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1346_; 
lean_inc_ref(v_buckets_1310_);
lean_inc(v_size_1309_);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_m_1306_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; lean_object* v_unused_1348_; 
v_unused_1347_ = lean_ctor_get(v_m_1306_, 1);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_m_1306_, 0);
lean_dec(v_unused_1348_);
v___x_1327_ = v_m_1306_;
v_isShared_1328_ = v_isSharedCheck_1346_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v_m_1306_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1346_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v_size_x27_1330_; lean_object* v___x_1331_; lean_object* v_buckets_x27_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1329_ = lean_unsigned_to_nat(1u);
v_size_x27_1330_ = lean_nat_add(v_size_1309_, v___x_1329_);
lean_dec(v_size_1309_);
lean_inc(v_bkt_1324_);
v___x_1331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1307_);
lean_ctor_set(v___x_1331_, 1, v_b_1308_);
lean_ctor_set(v___x_1331_, 2, v_bkt_1324_);
v_buckets_x27_1332_ = lean_array_uset(v_buckets_1310_, v___x_1323_, v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(4u);
v___x_1334_ = lean_nat_mul(v_size_x27_1330_, v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(3u);
v___x_1336_ = lean_nat_div(v___x_1334_, v___x_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_array_get_size(v_buckets_x27_1332_);
v___x_1338_ = lean_nat_dec_le(v___x_1336_, v___x_1337_);
lean_dec(v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v_val_1339_; lean_object* v___x_1341_; 
v_val_1339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_1332_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_val_1339_);
lean_ctor_set(v___x_1327_, 0, v_size_x27_1330_);
v___x_1341_ = v___x_1327_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_size_x27_1330_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_val_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
lean_object* v___x_1344_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v_buckets_x27_1332_);
lean_ctor_set(v___x_1327_, 0, v_size_x27_1330_);
v___x_1344_ = v___x_1327_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_size_x27_1330_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_buckets_x27_1332_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_dec(v_b_1308_);
lean_dec_ref(v_a_1307_);
return v_m_1306_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_m_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_buckets_1351_; lean_object* v___x_1352_; uint64_t v___x_1353_; uint64_t v___x_1354_; uint64_t v___x_1355_; uint64_t v_fold_1356_; uint64_t v___x_1357_; uint64_t v___x_1358_; uint64_t v___x_1359_; size_t v___x_1360_; size_t v___x_1361_; size_t v___x_1362_; size_t v___x_1363_; size_t v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_buckets_1351_ = lean_ctor_get(v_m_1349_, 1);
v___x_1352_ = lean_array_get_size(v_buckets_1351_);
v___x_1353_ = l_Lean_Expr_hash(v_a_1350_);
v___x_1354_ = 32ULL;
v___x_1355_ = lean_uint64_shift_right(v___x_1353_, v___x_1354_);
v_fold_1356_ = lean_uint64_xor(v___x_1353_, v___x_1355_);
v___x_1357_ = 16ULL;
v___x_1358_ = lean_uint64_shift_right(v_fold_1356_, v___x_1357_);
v___x_1359_ = lean_uint64_xor(v_fold_1356_, v___x_1358_);
v___x_1360_ = lean_uint64_to_usize(v___x_1359_);
v___x_1361_ = lean_usize_of_nat(v___x_1352_);
v___x_1362_ = ((size_t)1ULL);
v___x_1363_ = lean_usize_sub(v___x_1361_, v___x_1362_);
v___x_1364_ = lean_usize_land(v___x_1360_, v___x_1363_);
v___x_1365_ = lean_array_uget_borrowed(v_buckets_1351_, v___x_1364_);
v___x_1366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_1350_, v___x_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_m_1367_, lean_object* v_a_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_1367_, v_a_1368_);
lean_dec_ref(v_a_1368_);
lean_dec_ref(v_m_1367_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(lean_object* v_e_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_checked_1375_; uint8_t v___x_1376_; 
v___x_1374_ = lean_st_ref_get(v_a_1372_);
v_checked_1375_ = lean_ctor_get(v___x_1374_, 1);
lean_inc_ref(v_checked_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_1375_, v_e_1371_);
lean_dec_ref(v_checked_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v_visited_1378_; lean_object* v_checked_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1391_; 
v___x_1377_ = lean_st_ref_take(v_a_1372_);
v_visited_1378_ = lean_ctor_get(v___x_1377_, 0);
v_checked_1379_ = lean_ctor_get(v___x_1377_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1381_ = v___x_1377_;
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_checked_1379_);
lean_inc(v_visited_1378_);
lean_dec(v___x_1377_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1391_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_1379_, v_e_1371_, v___x_1383_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_visited_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_st_ref_put(v_a_1372_, v___x_1386_);
v___x_1388_ = lean_box(v___x_1376_);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_e_1371_);
v___x_1392_ = lean_box(v___x_1376_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_e_1394_, lean_object* v_a_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1394_, v_a_1395_);
lean_dec(v_a_1395_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(lean_object* v_p_1398_, lean_object* v_f_1399_, uint8_t v_stopWhenVisited_1400_, lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v_d_1415_; lean_object* v_b_1416_; lean_object* v___y_1417_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___x_1447_; 
lean_inc_ref(v_e_1401_);
v___x_1447_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1480_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1480_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_del_object(v___x_1450_);
lean_inc_ref(v_p_1398_);
lean_inc_ref(v_e_1401_);
v___x_1453_ = lean_apply_1(v_p_1398_, v_e_1401_);
v___x_1454_ = lean_unbox(v___x_1453_);
if (v___x_1454_ == 0)
{
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1455_; 
lean_inc_ref(v_e_1401_);
v___x_1455_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_1401_, v_a_1402_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; uint8_t v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_unbox(v_a_1456_);
lean_dec(v_a_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_inc_ref(v_f_1399_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v_e_1401_);
v___x_1458_ = lean_apply_7(v_f_1399_, v_e_1401_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, lean_box(0));
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1458_, 0);
lean_dec(v_unused_1467_);
v___x_1460_ = v___x_1458_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v___x_1458_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (v_stopWhenVisited_1400_ == 0)
{
lean_del_object(v___x_1460_);
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1462_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
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
else
{
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1458_;
}
}
else
{
v___y_1421_ = v_a_1402_;
v___y_1422_ = v___y_1403_;
v___y_1423_ = v___y_1404_;
v___y_1424_ = v___y_1405_;
v___y_1425_ = v___y_1406_;
v___y_1426_ = v___y_1407_;
goto v___jp_1420_;
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v_a_1468_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1455_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1455_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1476_ = lean_box(0);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1476_);
v___x_1478_ = v___x_1450_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v_a_1481_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1447_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1447_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
v___jp_1409_:
{
lean_object* v___x_1418_; 
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1418_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_d_1415_, v___y_1417_, v___y_1411_, v___y_1410_, v___y_1412_, v___y_1414_, v___y_1413_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_dec_ref_known(v___x_1418_, 1);
v_e_1401_ = v_b_1416_;
v_a_1402_ = v___y_1417_;
v___y_1403_ = v___y_1411_;
v___y_1404_ = v___y_1410_;
v___y_1405_ = v___y_1412_;
v___y_1406_ = v___y_1414_;
v___y_1407_ = v___y_1413_;
goto _start;
}
else
{
lean_dec_ref(v_b_1416_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1418_;
}
}
v___jp_1420_:
{
switch(lean_obj_tag(v_e_1401_))
{
case 7:
{
lean_object* v_binderType_1427_; lean_object* v_body_1428_; 
v_binderType_1427_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_binderType_1427_);
v_body_1428_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_body_1428_);
lean_dec_ref_known(v_e_1401_, 3);
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1424_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1425_;
v_d_1415_ = v_binderType_1427_;
v_b_1416_ = v_body_1428_;
v___y_1417_ = v___y_1421_;
goto v___jp_1409_;
}
case 6:
{
lean_object* v_binderType_1429_; lean_object* v_body_1430_; 
v_binderType_1429_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_binderType_1429_);
v_body_1430_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_body_1430_);
lean_dec_ref_known(v_e_1401_, 3);
v___y_1410_ = v___y_1423_;
v___y_1411_ = v___y_1422_;
v___y_1412_ = v___y_1424_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1425_;
v_d_1415_ = v_binderType_1429_;
v_b_1416_ = v_body_1430_;
v___y_1417_ = v___y_1421_;
goto v___jp_1409_;
}
case 8:
{
lean_object* v_type_1431_; lean_object* v_value_1432_; lean_object* v_body_1433_; lean_object* v___x_1434_; 
v_type_1431_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_type_1431_);
v_value_1432_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_value_1432_);
v_body_1433_ = lean_ctor_get(v_e_1401_, 3);
lean_inc_ref(v_body_1433_);
lean_dec_ref_known(v_e_1401_, 4);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1434_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_type_1431_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref_known(v___x_1434_, 1);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1435_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_value_1432_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v_e_1401_ = v_body_1433_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
else
{
lean_dec_ref(v_body_1433_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_body_1433_);
lean_dec_ref(v_value_1432_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1434_;
}
}
case 5:
{
lean_object* v_fn_1437_; lean_object* v_arg_1438_; lean_object* v___x_1439_; 
v_fn_1437_ = lean_ctor_get(v_e_1401_, 0);
lean_inc_ref(v_fn_1437_);
v_arg_1438_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_arg_1438_);
lean_dec_ref_known(v_e_1401_, 2);
lean_inc_ref(v_f_1399_);
lean_inc_ref(v_p_1398_);
v___x_1439_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1398_, v_f_1399_, v_stopWhenVisited_1400_, v_fn_1437_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
v_e_1401_ = v_arg_1438_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
else
{
lean_dec_ref(v_arg_1438_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
return v___x_1439_;
}
}
case 10:
{
lean_object* v_expr_1441_; 
v_expr_1441_ = lean_ctor_get(v_e_1401_, 1);
lean_inc_ref(v_expr_1441_);
lean_dec_ref_known(v_e_1401_, 2);
v_e_1401_ = v_expr_1441_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
case 11:
{
lean_object* v_struct_1443_; 
v_struct_1443_ = lean_ctor_get(v_e_1401_, 2);
lean_inc_ref(v_struct_1443_);
lean_dec_ref_known(v_e_1401_, 3);
v_e_1401_ = v_struct_1443_;
v_a_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1424_;
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1426_;
goto _start;
}
default: 
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_e_1401_);
lean_dec_ref(v_f_1399_);
lean_dec_ref(v_p_1398_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(lean_object* v_p_1489_, lean_object* v_f_1490_, lean_object* v_stopWhenVisited_1491_, lean_object* v_e_1492_, lean_object* v_a_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1500_; lean_object* v_res_1501_; 
v_stopWhenVisited_boxed_1500_ = lean_unbox(v_stopWhenVisited_1491_);
v_res_1501_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1489_, v_f_1490_, v_stopWhenVisited_boxed_1500_, v_e_1492_, v_a_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v_a_1493_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(lean_object* v_p_1502_, lean_object* v_f_1503_, lean_object* v_e_1504_, uint8_t v_stopWhenVisited_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = l_Lean_ForEachExprWhere_initCache;
v___x_1513_ = lean_st_mk_ref(v___x_1512_);
v___x_1514_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_1502_, v_f_1503_, v_stopWhenVisited_1505_, v_e_1504_, v___x_1513_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1523_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1523_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_st_ref_get(v___x_1513_);
lean_dec(v___x_1513_);
lean_dec(v___x_1519_);
if (v_isShared_1518_ == 0)
{
v___x_1521_ = v___x_1517_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1515_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_dec(v___x_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(lean_object* v_p_1524_, lean_object* v_f_1525_, lean_object* v_e_1526_, lean_object* v_stopWhenVisited_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_stopWhenVisited_boxed_1534_; lean_object* v_res_1535_; 
v_stopWhenVisited_boxed_1534_ = lean_unbox(v_stopWhenVisited_1527_);
v_res_1535_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v_p_1524_, v_f_1525_, v_e_1526_, v_stopWhenVisited_boxed_1534_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(lean_object* v___f_1537_, lean_object* v___f_1538_, uint8_t v___x_1539_, lean_object* v_e_1540_, lean_object* v_candidates_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_e_1540_, v___y_1543_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___y_1552_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = l_Lean_Expr_hasFVar(v_a_1548_);
v___x_1550_ = lean_st_mk_ref(v_candidates_1541_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_a_1548_);
lean_dec_ref(v___f_1538_);
v___x_1562_ = lean_box(0);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___x_1550_);
v___x_1563_ = lean_apply_7(v___f_1537_, v___x_1562_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
v___y_1552_ = v___x_1563_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_1565_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_1564_, v___f_1538_, v_a_1548_, v___x_1539_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___x_1550_);
v___x_1567_ = lean_apply_7(v___f_1537_, v_a_1566_, v___x_1550_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
v___y_1552_ = v___x_1567_;
goto v___jp_1551_;
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec(v___x_1550_);
lean_dec_ref(v___f_1537_);
v_a_1568_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1565_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1565_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
v___jp_1551_:
{
if (lean_obj_tag(v___y_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_a_1553_ = lean_ctor_get(v___y_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___y_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v___y_1552_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___y_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_st_ref_get(v___x_1550_);
lean_dec(v___x_1550_);
lean_dec(v___x_1557_);
if (v_isShared_1556_ == 0)
{
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1553_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_dec(v___x_1550_);
return v___y_1552_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_candidates_1541_);
lean_dec_ref(v___f_1538_);
lean_dec_ref(v___f_1537_);
v_a_1576_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1547_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1547_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(lean_object* v___f_1584_, lean_object* v___f_1585_, lean_object* v___x_1586_, lean_object* v_e_1587_, lean_object* v_candidates_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v___x_16915__boxed_1594_; lean_object* v_res_1595_; 
v___x_16915__boxed_1594_ = lean_unbox(v___x_1586_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1584_, v___f_1585_, v___x_16915__boxed_1594_, v_e_1587_, v_candidates_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(lean_object* v_____r_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_st_ref_get(v___y_1597_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(lean_object* v_____r_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_____r_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(lean_object* v_e_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1620_ = lean_st_ref_take(v___y_1614_);
v___x_1621_ = lean_box(0);
v___x_1622_ = l_Lean_Expr_fvarId_x21(v_e_1613_);
v___x_1623_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_1620_, v___x_1622_);
lean_dec(v___x_1622_);
v___x_1624_ = lean_st_ref_put(v___y_1614_, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1621_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(lean_object* v_e_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_e_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v_e_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
return v_x_1634_;
}
else
{
lean_object* v_key_1636_; lean_object* v_value_1637_; lean_object* v_tail_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1661_; 
v_key_1636_ = lean_ctor_get(v_x_1635_, 0);
v_value_1637_ = lean_ctor_get(v_x_1635_, 1);
v_tail_1638_ = lean_ctor_get(v_x_1635_, 2);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1635_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1640_ = v_x_1635_;
v_isShared_1641_ = v_isSharedCheck_1661_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_tail_1638_);
lean_inc(v_value_1637_);
lean_inc(v_key_1636_);
lean_dec(v_x_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1661_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; uint64_t v_fold_1646_; uint64_t v___x_1647_; uint64_t v___x_1648_; uint64_t v___x_1649_; size_t v___x_1650_; size_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1642_ = lean_array_get_size(v_x_1634_);
v___x_1643_ = l_Lean_instHashableFVarId_hash(v_key_1636_);
v___x_1644_ = 32ULL;
v___x_1645_ = lean_uint64_shift_right(v___x_1643_, v___x_1644_);
v_fold_1646_ = lean_uint64_xor(v___x_1643_, v___x_1645_);
v___x_1647_ = 16ULL;
v___x_1648_ = lean_uint64_shift_right(v_fold_1646_, v___x_1647_);
v___x_1649_ = lean_uint64_xor(v_fold_1646_, v___x_1648_);
v___x_1650_ = lean_uint64_to_usize(v___x_1649_);
v___x_1651_ = lean_usize_of_nat(v___x_1642_);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_sub(v___x_1651_, v___x_1652_);
v___x_1654_ = lean_usize_land(v___x_1650_, v___x_1653_);
v___x_1655_ = lean_array_uget_borrowed(v_x_1634_, v___x_1654_);
lean_inc(v___x_1655_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 2, v___x_1655_);
v___x_1657_ = v___x_1640_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_key_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_value_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_uset(v_x_1634_, v___x_1654_, v___x_1657_);
v_x_1634_ = v___x_1658_;
v_x_1635_ = v_tail_1638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(lean_object* v_i_1662_, lean_object* v_source_1663_, lean_object* v_target_1664_){
_start:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = lean_array_get_size(v_source_1663_);
v___x_1666_ = lean_nat_dec_lt(v_i_1662_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_dec_ref(v_source_1663_);
lean_dec(v_i_1662_);
return v_target_1664_;
}
else
{
lean_object* v_es_1667_; lean_object* v___x_1668_; lean_object* v_source_1669_; lean_object* v_target_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_es_1667_ = lean_array_fget(v_source_1663_, v_i_1662_);
v___x_1668_ = lean_box(0);
v_source_1669_ = lean_array_fset(v_source_1663_, v_i_1662_, v___x_1668_);
v_target_1670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_1664_, v_es_1667_);
v___x_1671_ = lean_unsigned_to_nat(1u);
v___x_1672_ = lean_nat_add(v_i_1662_, v___x_1671_);
lean_dec(v_i_1662_);
v_i_1662_ = v___x_1672_;
v_source_1663_ = v_source_1669_;
v_target_1664_ = v_target_1670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(lean_object* v_data_1674_){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_nbuckets_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1675_ = lean_array_get_size(v_data_1674_);
v___x_1676_ = lean_unsigned_to_nat(2u);
v_nbuckets_1677_ = lean_nat_mul(v___x_1675_, v___x_1676_);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_mk_array(v_nbuckets_1677_, v___x_1679_);
v___x_1681_ = lean_array_propagate_mark(v_data_1674_, v___x_1680_);
v___x_1682_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_1678_, v_data_1674_, v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(lean_object* v_m_1683_, lean_object* v_a_1684_, lean_object* v_b_1685_){
_start:
{
lean_object* v_size_1686_; lean_object* v_buckets_1687_; lean_object* v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v___x_1691_; uint64_t v_fold_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; size_t v___x_1700_; lean_object* v_bkt_1701_; uint8_t v___x_1702_; 
v_size_1686_ = lean_ctor_get(v_m_1683_, 0);
v_buckets_1687_ = lean_ctor_get(v_m_1683_, 1);
v___x_1688_ = lean_array_get_size(v_buckets_1687_);
v___x_1689_ = l_Lean_instHashableFVarId_hash(v_a_1684_);
v___x_1690_ = 32ULL;
v___x_1691_ = lean_uint64_shift_right(v___x_1689_, v___x_1690_);
v_fold_1692_ = lean_uint64_xor(v___x_1689_, v___x_1691_);
v___x_1693_ = 16ULL;
v___x_1694_ = lean_uint64_shift_right(v_fold_1692_, v___x_1693_);
v___x_1695_ = lean_uint64_xor(v_fold_1692_, v___x_1694_);
v___x_1696_ = lean_uint64_to_usize(v___x_1695_);
v___x_1697_ = lean_usize_of_nat(v___x_1688_);
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_sub(v___x_1697_, v___x_1698_);
v___x_1700_ = lean_usize_land(v___x_1696_, v___x_1699_);
v_bkt_1701_ = lean_array_uget_borrowed(v_buckets_1687_, v___x_1700_);
v___x_1702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_1684_, v_bkt_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1723_; 
lean_inc_ref(v_buckets_1687_);
lean_inc(v_size_1686_);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_m_1683_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; lean_object* v_unused_1725_; 
v_unused_1724_ = lean_ctor_get(v_m_1683_, 1);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_m_1683_, 0);
lean_dec(v_unused_1725_);
v___x_1704_ = v_m_1683_;
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
else
{
lean_dec(v_m_1683_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1723_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v_size_x27_1707_; lean_object* v___x_1708_; lean_object* v_buckets_x27_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1706_ = lean_unsigned_to_nat(1u);
v_size_x27_1707_ = lean_nat_add(v_size_1686_, v___x_1706_);
lean_dec(v_size_1686_);
lean_inc(v_bkt_1701_);
v___x_1708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1708_, 0, v_a_1684_);
lean_ctor_set(v___x_1708_, 1, v_b_1685_);
lean_ctor_set(v___x_1708_, 2, v_bkt_1701_);
v_buckets_x27_1709_ = lean_array_uset(v_buckets_1687_, v___x_1700_, v___x_1708_);
v___x_1710_ = lean_unsigned_to_nat(4u);
v___x_1711_ = lean_nat_mul(v_size_x27_1707_, v___x_1710_);
v___x_1712_ = lean_unsigned_to_nat(3u);
v___x_1713_ = lean_nat_div(v___x_1711_, v___x_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_array_get_size(v_buckets_x27_1709_);
v___x_1715_ = lean_nat_dec_le(v___x_1713_, v___x_1714_);
lean_dec(v___x_1713_);
if (v___x_1715_ == 0)
{
lean_object* v_val_1716_; lean_object* v___x_1718_; 
v_val_1716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_1709_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_val_1716_);
lean_ctor_set(v___x_1704_, 0, v_size_x27_1707_);
v___x_1718_ = v___x_1704_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_size_x27_1707_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_val_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1721_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_buckets_x27_1709_);
lean_ctor_set(v___x_1704_, 0, v_size_x27_1707_);
v___x_1721_ = v___x_1704_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_size_x27_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_buckets_x27_1709_);
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
else
{
lean_dec(v_b_1685_);
lean_dec(v_a_1684_);
return v_m_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(lean_object* v_as_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_b_1731_);
return v___x_1738_;
}
else
{
lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1806_; 
v_snd_1739_ = lean_ctor_get(v_b_1731_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_b_1731_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_b_1731_, 0);
lean_dec(v_unused_1807_);
v___x_1741_ = v_b_1731_;
v_isShared_1742_ = v_isSharedCheck_1806_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_dec(v_b_1731_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1806_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_a_1745_; lean_object* v_a_1752_; 
v___x_1743_ = lean_box(0);
v_a_1752_ = lean_array_uget_borrowed(v_as_1728_, v_i_1730_);
if (lean_obj_tag(v_a_1752_) == 0)
{
v_a_1745_ = v_snd_1739_;
goto v___jp_1744_;
}
else
{
lean_object* v_val_1753_; lean_object* v___y_1755_; lean_object* v___y_1760_; uint8_t v___y_1761_; uint8_t v___x_1762_; 
v_val_1753_ = lean_ctor_get(v_a_1752_, 0);
v___x_1762_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1753_);
if (v___x_1762_ == 0)
{
lean_object* v___f_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v_candidates_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___x_1784_; 
v___f_1763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1765_ = l_Lean_LocalDecl_type(v_val_1753_);
lean_inc_ref(v___x_1765_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1763_, v___f_1764_, v___x_1762_, v___x_1765_, v_snd_1739_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = l_Lean_LocalDecl_value_x3f(v_val_1753_, v___x_1762_);
if (lean_obj_tag(v___x_1786_) == 0)
{
v_candidates_1767_ = v_a_1785_;
v___y_1768_ = v___y_1732_;
v___y_1769_ = v___y_1733_;
v___y_1770_ = v___y_1734_;
v___y_1771_ = v___y_1735_;
goto v___jp_1766_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; 
v_val_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1763_, v___f_1764_, v___x_1762_, v_val_1787_, v_a_1785_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v_candidates_1767_ = v_a_1789_;
v___y_1768_ = v___y_1732_;
v___y_1769_ = v___y_1733_;
v___y_1770_ = v___y_1734_;
v___y_1771_ = v___y_1735_;
goto v___jp_1766_;
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v___x_1765_);
lean_del_object(v___x_1741_);
v_a_1790_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1788_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1788_);
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
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___x_1765_);
lean_del_object(v___x_1741_);
v_a_1798_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1784_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1784_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
v___jp_1766_:
{
lean_object* v___x_1772_; 
v___x_1772_ = l_Lean_Meta_isProp(v___x_1765_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; uint8_t v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = lean_unbox(v_a_1773_);
lean_dec(v_a_1773_);
if (v___x_1774_ == 0)
{
v___y_1760_ = v_candidates_1767_;
v___y_1761_ = v___x_1762_;
goto v___jp_1759_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = l_Lean_LocalDecl_hasValue(v_val_1753_, v___x_1762_);
if (v___x_1775_ == 0)
{
v___y_1755_ = v_candidates_1767_;
goto v___jp_1754_;
}
else
{
v___y_1760_ = v_candidates_1767_;
v___y_1761_ = v___x_1762_;
goto v___jp_1759_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
lean_dec_ref(v_candidates_1767_);
lean_del_object(v___x_1741_);
v_a_1776_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1772_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1772_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
else
{
v_a_1745_ = v_snd_1739_;
goto v___jp_1744_;
}
v___jp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = l_Lean_LocalDecl_fvarId(v_val_1753_);
v___x_1757_ = lean_box(0);
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1755_, v___x_1756_, v___x_1757_);
v_a_1745_ = v___x_1758_;
goto v___jp_1744_;
}
v___jp_1759_:
{
if (v___y_1761_ == 0)
{
v_a_1745_ = v___y_1760_;
goto v___jp_1744_;
}
else
{
v___y_1755_ = v___y_1760_;
goto v___jp_1754_;
}
}
}
v___jp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v_a_1745_);
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1747_ = v___x_1741_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_a_1745_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
size_t v___x_1748_; size_t v___x_1749_; 
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1730_, v___x_1748_);
v_i_1730_ = v___x_1749_;
v_b_1731_ = v___x_1747_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(lean_object* v_as_1808_, lean_object* v_sz_1809_, lean_object* v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
size_t v_sz_boxed_1817_; size_t v_i_boxed_1818_; lean_object* v_res_1819_; 
v_sz_boxed_1817_ = lean_unbox_usize(v_sz_1809_);
lean_dec(v_sz_1809_);
v_i_boxed_1818_ = lean_unbox_usize(v_i_1810_);
lean_dec(v_i_1810_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1808_, v_sz_boxed_1817_, v_i_boxed_1818_, v_b_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_as_1808_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(lean_object* v_as_1820_, size_t v_sz_1821_, size_t v_i_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_usize_dec_lt(v_i_1822_, v_sz_1821_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_b_1823_);
return v___x_1830_;
}
else
{
lean_object* v_snd_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1898_; 
v_snd_1831_ = lean_ctor_get(v_b_1823_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_b_1823_);
if (v_isSharedCheck_1898_ == 0)
{
lean_object* v_unused_1899_; 
v_unused_1899_ = lean_ctor_get(v_b_1823_, 0);
lean_dec(v_unused_1899_);
v___x_1833_ = v_b_1823_;
v_isShared_1834_ = v_isSharedCheck_1898_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_snd_1831_);
lean_dec(v_b_1823_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1898_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v_a_1837_; lean_object* v_a_1844_; 
v___x_1835_ = lean_box(0);
v_a_1844_ = lean_array_uget_borrowed(v_as_1820_, v_i_1822_);
if (lean_obj_tag(v_a_1844_) == 0)
{
v_a_1837_ = v_snd_1831_;
goto v___jp_1836_;
}
else
{
lean_object* v_val_1845_; lean_object* v___y_1847_; lean_object* v___y_1852_; uint8_t v___y_1853_; uint8_t v___x_1854_; 
v_val_1845_ = lean_ctor_get(v_a_1844_, 0);
v___x_1854_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1845_);
if (v___x_1854_ == 0)
{
lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v_candidates_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___x_1876_; 
v___f_1855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1857_ = l_Lean_LocalDecl_type(v_val_1845_);
lean_inc_ref(v___x_1857_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1855_, v___f_1856_, v___x_1854_, v___x_1857_, v_snd_1831_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l_Lean_LocalDecl_value_x3f(v_val_1845_, v___x_1854_);
if (lean_obj_tag(v___x_1878_) == 0)
{
v_candidates_1859_ = v_a_1877_;
v___y_1860_ = v___y_1824_;
v___y_1861_ = v___y_1825_;
v___y_1862_ = v___y_1826_;
v___y_1863_ = v___y_1827_;
goto v___jp_1858_;
}
else
{
lean_object* v_val_1879_; lean_object* v___x_1880_; 
v_val_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1855_, v___f_1856_, v___x_1854_, v_val_1879_, v_a_1877_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v_candidates_1859_ = v_a_1881_;
v___y_1860_ = v___y_1824_;
v___y_1861_ = v___y_1825_;
v___y_1862_ = v___y_1826_;
v___y_1863_ = v___y_1827_;
goto v___jp_1858_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___x_1857_);
lean_del_object(v___x_1833_);
v_a_1882_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1880_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1880_);
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
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v___x_1857_);
lean_del_object(v___x_1833_);
v_a_1890_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1876_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1876_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_isProp(v___x_1857_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; uint8_t v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = lean_unbox(v_a_1865_);
lean_dec(v_a_1865_);
if (v___x_1866_ == 0)
{
v___y_1852_ = v_candidates_1859_;
v___y_1853_ = v___x_1854_;
goto v___jp_1851_;
}
else
{
uint8_t v___x_1867_; 
v___x_1867_ = l_Lean_LocalDecl_hasValue(v_val_1845_, v___x_1854_);
if (v___x_1867_ == 0)
{
v___y_1847_ = v_candidates_1859_;
goto v___jp_1846_;
}
else
{
v___y_1852_ = v_candidates_1859_;
v___y_1853_ = v___x_1854_;
goto v___jp_1851_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_candidates_1859_);
lean_del_object(v___x_1833_);
v_a_1868_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1864_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1864_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
else
{
v_a_1837_ = v_snd_1831_;
goto v___jp_1836_;
}
v___jp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = l_Lean_LocalDecl_fvarId(v_val_1845_);
v___x_1849_ = lean_box(0);
v___x_1850_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1847_, v___x_1848_, v___x_1849_);
v_a_1837_ = v___x_1850_;
goto v___jp_1836_;
}
v___jp_1851_:
{
if (v___y_1853_ == 0)
{
v_a_1837_ = v___y_1852_;
goto v___jp_1836_;
}
else
{
v___y_1847_ = v___y_1852_;
goto v___jp_1846_;
}
}
}
v___jp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v_a_1837_);
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1839_ = v___x_1833_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1837_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1822_, v___x_1840_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_1820_, v_sz_1821_, v___x_1841_, v___x_1839_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(lean_object* v_as_1900_, lean_object* v_sz_1901_, lean_object* v_i_1902_, lean_object* v_b_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1901_);
lean_dec(v_sz_1901_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1902_);
lean_dec(v_i_1902_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_1900_, v_sz_boxed_1909_, v_i_boxed_1910_, v_b_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v_as_1900_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(lean_object* v_as_1912_, size_t v_sz_1913_, size_t v_i_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
uint8_t v___x_1921_; 
v___x_1921_ = lean_usize_dec_lt(v_i_1914_, v_sz_1913_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_b_1915_);
return v___x_1922_;
}
else
{
lean_object* v_snd_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1990_; 
v_snd_1923_ = lean_ctor_get(v_b_1915_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_b_1915_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v_b_1915_, 0);
lean_dec(v_unused_1991_);
v___x_1925_ = v_b_1915_;
v_isShared_1926_ = v_isSharedCheck_1990_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snd_1923_);
lean_dec(v_b_1915_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1990_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v_a_1929_; lean_object* v_a_1936_; 
v___x_1927_ = lean_box(0);
v_a_1936_ = lean_array_uget_borrowed(v_as_1912_, v_i_1914_);
if (lean_obj_tag(v_a_1936_) == 0)
{
v_a_1929_ = v_snd_1923_;
goto v___jp_1928_;
}
else
{
lean_object* v_val_1937_; lean_object* v___y_1939_; lean_object* v___y_1944_; uint8_t v___y_1945_; uint8_t v___x_1946_; 
v_val_1937_ = lean_ctor_get(v_a_1936_, 0);
v___x_1946_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1937_);
if (v___x_1946_ == 0)
{
lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v_candidates_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___x_1968_; 
v___f_1947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_1948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_1949_ = l_Lean_LocalDecl_type(v_val_1937_);
lean_inc_ref(v___x_1949_);
v___x_1968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1947_, v___f_1948_, v___x_1946_, v___x_1949_, v_snd_1923_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___x_1970_ = l_Lean_LocalDecl_value_x3f(v_val_1937_, v___x_1946_);
if (lean_obj_tag(v___x_1970_) == 0)
{
v_candidates_1951_ = v_a_1969_;
v___y_1952_ = v___y_1916_;
v___y_1953_ = v___y_1917_;
v___y_1954_ = v___y_1918_;
v___y_1955_ = v___y_1919_;
goto v___jp_1950_;
}
else
{
lean_object* v_val_1971_; lean_object* v___x_1972_; 
v_val_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v___x_1970_, 1);
v___x_1972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_1947_, v___f_1948_, v___x_1946_, v_val_1971_, v_a_1969_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v_candidates_1951_ = v_a_1973_;
v___y_1952_ = v___y_1916_;
v___y_1953_ = v___y_1917_;
v___y_1954_ = v___y_1918_;
v___y_1955_ = v___y_1919_;
goto v___jp_1950_;
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1949_);
lean_del_object(v___x_1925_);
v_a_1974_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1972_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v___x_1949_);
lean_del_object(v___x_1925_);
v_a_1982_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1968_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1968_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
v___jp_1950_:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Meta_isProp(v___x_1949_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1958_ == 0)
{
v___y_1944_ = v_candidates_1951_;
v___y_1945_ = v___x_1946_;
goto v___jp_1943_;
}
else
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_LocalDecl_hasValue(v_val_1937_, v___x_1946_);
if (v___x_1959_ == 0)
{
v___y_1939_ = v_candidates_1951_;
goto v___jp_1938_;
}
else
{
v___y_1944_ = v_candidates_1951_;
v___y_1945_ = v___x_1946_;
goto v___jp_1943_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_candidates_1951_);
lean_del_object(v___x_1925_);
v_a_1960_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1956_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1956_);
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
v_a_1929_ = v_snd_1923_;
goto v___jp_1928_;
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = l_Lean_LocalDecl_fvarId(v_val_1937_);
v___x_1941_ = lean_box(0);
v___x_1942_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_1939_, v___x_1940_, v___x_1941_);
v_a_1929_ = v___x_1942_;
goto v___jp_1928_;
}
v___jp_1943_:
{
if (v___y_1945_ == 0)
{
v_a_1929_ = v___y_1944_;
goto v___jp_1928_;
}
else
{
v___y_1939_ = v___y_1944_;
goto v___jp_1938_;
}
}
}
v___jp_1928_:
{
lean_object* v___x_1931_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v_a_1929_);
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1931_ = v___x_1925_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1929_);
v___x_1931_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
size_t v___x_1932_; size_t v___x_1933_; 
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_add(v_i_1914_, v___x_1932_);
v_i_1914_ = v___x_1933_;
v_b_1915_ = v___x_1931_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(lean_object* v_as_1992_, lean_object* v_sz_1993_, lean_object* v_i_1994_, lean_object* v_b_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
size_t v_sz_boxed_2001_; size_t v_i_boxed_2002_; lean_object* v_res_2003_; 
v_sz_boxed_2001_ = lean_unbox_usize(v_sz_1993_);
lean_dec(v_sz_1993_);
v_i_boxed_2002_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_1992_, v_sz_boxed_2001_, v_i_boxed_2002_, v_b_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_as_1992_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(lean_object* v_as_2004_, size_t v_sz_2005_, size_t v_i_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2006_, v_sz_2005_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2007_);
return v___x_2014_;
}
else
{
lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2082_; 
v_snd_2015_ = lean_ctor_get(v_b_2007_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_b_2007_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_b_2007_, 0);
lean_dec(v_unused_2083_);
v___x_2017_ = v_b_2007_;
v_isShared_2018_ = v_isSharedCheck_2082_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_dec(v_b_2007_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2082_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v_a_2021_; lean_object* v_a_2028_; 
v___x_2019_ = lean_box(0);
v_a_2028_ = lean_array_uget_borrowed(v_as_2004_, v_i_2006_);
if (lean_obj_tag(v_a_2028_) == 0)
{
v_a_2021_ = v_snd_2015_;
goto v___jp_2020_;
}
else
{
lean_object* v_val_2029_; lean_object* v___y_2031_; lean_object* v___y_2036_; uint8_t v___y_2037_; uint8_t v___x_2038_; 
v_val_2029_ = lean_ctor_get(v_a_2028_, 0);
v___x_2038_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2029_);
if (v___x_2038_ == 0)
{
lean_object* v___f_2039_; lean_object* v___f_2040_; lean_object* v___x_2041_; lean_object* v_candidates_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___x_2060_; 
v___f_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0));
v___f_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1));
v___x_2041_ = l_Lean_LocalDecl_type(v_val_2029_);
lean_inc_ref(v___x_2041_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2039_, v___f_2040_, v___x_2038_, v___x_2041_, v_snd_2015_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = l_Lean_LocalDecl_value_x3f(v_val_2029_, v___x_2038_);
if (lean_obj_tag(v___x_2062_) == 0)
{
v_candidates_2043_ = v_a_2061_;
v___y_2044_ = v___y_2008_;
v___y_2045_ = v___y_2009_;
v___y_2046_ = v___y_2010_;
v___y_2047_ = v___y_2011_;
goto v___jp_2042_;
}
else
{
lean_object* v_val_2063_; lean_object* v___x_2064_; 
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_2039_, v___f_2040_, v___x_2038_, v_val_2063_, v_a_2061_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v_candidates_2043_ = v_a_2065_;
v___y_2044_ = v___y_2008_;
v___y_2045_ = v___y_2009_;
v___y_2046_ = v___y_2010_;
v___y_2047_ = v___y_2011_;
goto v___jp_2042_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___x_2041_);
lean_del_object(v___x_2017_);
v_a_2066_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2064_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___x_2041_);
lean_del_object(v___x_2017_);
v_a_2074_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2060_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2060_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
v___jp_2042_:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_isProp(v___x_2041_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; uint8_t v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = lean_unbox(v_a_2049_);
lean_dec(v_a_2049_);
if (v___x_2050_ == 0)
{
v___y_2036_ = v_candidates_2043_;
v___y_2037_ = v___x_2038_;
goto v___jp_2035_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_LocalDecl_hasValue(v_val_2029_, v___x_2038_);
if (v___x_2051_ == 0)
{
v___y_2031_ = v_candidates_2043_;
goto v___jp_2030_;
}
else
{
v___y_2036_ = v_candidates_2043_;
v___y_2037_ = v___x_2038_;
goto v___jp_2035_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_candidates_2043_);
lean_del_object(v___x_2017_);
v_a_2052_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2048_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2048_);
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
v_a_2021_ = v_snd_2015_;
goto v___jp_2020_;
}
v___jp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = l_Lean_LocalDecl_fvarId(v_val_2029_);
v___x_2033_ = lean_box(0);
v___x_2034_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_2031_, v___x_2032_, v___x_2033_);
v_a_2021_ = v___x_2034_;
goto v___jp_2020_;
}
v___jp_2035_:
{
if (v___y_2037_ == 0)
{
v_a_2021_ = v___y_2036_;
goto v___jp_2020_;
}
else
{
v___y_2031_ = v___y_2036_;
goto v___jp_2030_;
}
}
}
v___jp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v_a_2021_);
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_a_2021_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
size_t v___x_2024_; size_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_add(v_i_2006_, v___x_2024_);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_2004_, v_sz_2005_, v___x_2025_, v___x_2023_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(lean_object* v_as_2084_, lean_object* v_sz_2085_, lean_object* v_i_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
size_t v_sz_boxed_2093_; size_t v_i_boxed_2094_; lean_object* v_res_2095_; 
v_sz_boxed_2093_ = lean_unbox_usize(v_sz_2085_);
lean_dec(v_sz_2085_);
v_i_boxed_2094_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_2084_, v_sz_boxed_2093_, v_i_boxed_2094_, v_b_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v_as_2084_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(lean_object* v_init_2096_, lean_object* v_n_2097_, lean_object* v_b_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
if (lean_obj_tag(v_n_2097_) == 0)
{
lean_object* v_cs_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; size_t v_sz_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
v_cs_2104_ = lean_ctor_get(v_n_2097_, 0);
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_b_2098_);
v_sz_2107_ = lean_array_size(v_cs_2104_);
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2096_, v_cs_2104_, v_sz_2107_, v___x_2108_, v___x_2106_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2124_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2124_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2124_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_fst_2114_; 
v_fst_2114_ = lean_ctor_get(v_a_2110_, 0);
if (lean_obj_tag(v_fst_2114_) == 0)
{
lean_object* v_snd_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v_snd_2115_ = lean_ctor_get(v_a_2110_, 1);
lean_inc(v_snd_2115_);
lean_dec(v_a_2110_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v_snd_2115_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2116_);
v___x_2118_ = v___x_2112_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2122_; 
lean_inc_ref(v_fst_2114_);
lean_dec(v_a_2110_);
v_val_2120_ = lean_ctor_get(v_fst_2114_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_fst_2114_, 1);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_val_2120_);
v___x_2122_ = v___x_2112_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_val_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
v_a_2125_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2109_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2109_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
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
lean_object* v_vs_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; size_t v_sz_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v_vs_2133_ = lean_ctor_get(v_n_2097_, 0);
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
lean_ctor_set(v___x_2135_, 1, v_b_2098_);
v_sz_2136_ = lean_array_size(v_vs_2133_);
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_2133_, v_sz_2136_, v___x_2137_, v___x_2135_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2153_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2153_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_fst_2143_; 
v_fst_2143_ = lean_ctor_get(v_a_2139_, 0);
if (lean_obj_tag(v_fst_2143_) == 0)
{
lean_object* v_snd_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v_snd_2144_ = lean_ctor_get(v_a_2139_, 1);
lean_inc(v_snd_2144_);
lean_dec(v_a_2139_);
v___x_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_snd_2144_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2145_);
v___x_2147_ = v___x_2141_;
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
else
{
lean_object* v_val_2149_; lean_object* v___x_2151_; 
lean_inc_ref(v_fst_2143_);
lean_dec(v_a_2139_);
v_val_2149_ = lean_ctor_get(v_fst_2143_, 0);
lean_inc(v_val_2149_);
lean_dec_ref_known(v_fst_2143_, 1);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_val_2149_);
v___x_2151_ = v___x_2141_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_val_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_a_2154_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2138_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2138_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(lean_object* v_init_2162_, lean_object* v_as_2163_, size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_b_2166_);
return v___x_2173_;
}
else
{
lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2208_; 
v_snd_2174_ = lean_ctor_get(v_b_2166_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_b_2166_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_b_2166_, 0);
lean_dec(v_unused_2209_);
v___x_2176_ = v_b_2166_;
v_isShared_2177_ = v_isSharedCheck_2208_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_dec(v_b_2166_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2208_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v_a_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_box(0);
v_a_2179_ = lean_array_uget_borrowed(v_as_2163_, v_i_2165_);
lean_inc(v_snd_2174_);
v___x_2180_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2162_, v_a_2179_, v_snd_2174_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2199_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
if (lean_obj_tag(v_a_2181_) == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2181_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2185_);
v___x_2187_ = v___x_2176_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_snd_2174_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2187_);
v___x_2189_ = v___x_2183_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; 
lean_del_object(v___x_2183_);
lean_dec(v_snd_2174_);
v_a_2192_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_a_2192_);
lean_dec_ref_known(v_a_2181_, 1);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_a_2192_);
lean_ctor_set(v___x_2176_, 0, v___x_2178_);
v___x_2194_ = v___x_2176_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2192_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
size_t v___x_2195_; size_t v___x_2196_; 
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2165_, v___x_2195_);
v_i_2165_ = v___x_2196_;
v_b_2166_ = v___x_2194_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
v_a_2200_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2180_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2180_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(lean_object* v_init_2210_, lean_object* v_as_2211_, lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_2210_, v_as_2211_, v_sz_boxed_2220_, v_i_boxed_2221_, v_b_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_as_2211_);
lean_dec_ref(v_init_2210_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(lean_object* v_init_2223_, lean_object* v_n_2224_, lean_object* v_b_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2223_, v_n_2224_, v_b_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v_n_2224_);
lean_dec_ref(v_init_2223_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(lean_object* v_t_2232_, lean_object* v_init_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_root_2239_; lean_object* v_tail_2240_; lean_object* v___x_2241_; 
v_root_2239_ = lean_ctor_get(v_t_2232_, 0);
v_tail_2240_ = lean_ctor_get(v_t_2232_, 1);
lean_inc_ref(v_init_2233_);
v___x_2241_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_2233_, v_root_2239_, v_init_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec_ref(v_init_2233_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2278_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2278_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2278_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
if (lean_obj_tag(v_a_2242_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; 
v_a_2246_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v_a_2242_, 1);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v_a_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; size_t v_sz_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
lean_del_object(v___x_2244_);
v_a_2250_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v_a_2242_, 1);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_a_2250_);
v_sz_2253_ = lean_array_size(v_tail_2240_);
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_2240_, v_sz_2253_, v___x_2254_, v___x_2252_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2269_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2269_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2269_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_fst_2260_; 
v_fst_2260_ = lean_ctor_get(v_a_2256_, 0);
if (lean_obj_tag(v_fst_2260_) == 0)
{
lean_object* v_snd_2261_; lean_object* v___x_2263_; 
v_snd_2261_ = lean_ctor_get(v_a_2256_, 1);
lean_inc(v_snd_2261_);
lean_dec(v_a_2256_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_snd_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_snd_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
else
{
lean_object* v_val_2265_; lean_object* v___x_2267_; 
lean_inc_ref(v_fst_2260_);
lean_dec(v_a_2256_);
v_val_2265_ = lean_ctor_get(v_fst_2260_, 0);
lean_inc(v_val_2265_);
lean_dec_ref_known(v_fst_2260_, 1);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v_val_2265_);
v___x_2267_ = v___x_2258_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_val_2265_);
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
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2270_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2255_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2255_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_a_2279_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2241_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2241_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(lean_object* v_t_2287_, lean_object* v_init_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_t_2287_, v_init_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_t_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(lean_object* v_m_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_buckets_2297_; lean_object* v___x_2298_; uint64_t v___x_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v_fold_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; size_t v___x_2308_; size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v_buckets_2297_ = lean_ctor_get(v_m_2295_, 1);
v___x_2298_ = lean_array_get_size(v_buckets_2297_);
v___x_2299_ = l_Lean_instHashableFVarId_hash(v_a_2296_);
v___x_2300_ = 32ULL;
v___x_2301_ = lean_uint64_shift_right(v___x_2299_, v___x_2300_);
v_fold_2302_ = lean_uint64_xor(v___x_2299_, v___x_2301_);
v___x_2303_ = 16ULL;
v___x_2304_ = lean_uint64_shift_right(v_fold_2302_, v___x_2303_);
v___x_2305_ = lean_uint64_xor(v_fold_2302_, v___x_2304_);
v___x_2306_ = lean_uint64_to_usize(v___x_2305_);
v___x_2307_ = lean_usize_of_nat(v___x_2298_);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_sub(v___x_2307_, v___x_2308_);
v___x_2310_ = lean_usize_land(v___x_2306_, v___x_2309_);
v___x_2311_ = lean_array_uget_borrowed(v_buckets_2297_, v___x_2310_);
v___x_2312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2296_, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(lean_object* v_m_2313_, lean_object* v_a_2314_){
_start:
{
uint8_t v_res_2315_; lean_object* v_r_2316_; 
v_res_2315_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_m_2313_);
v_r_2316_ = lean_box(v_res_2315_);
return v_r_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(lean_object* v_a_2317_, lean_object* v_as_2318_, size_t v_sz_2319_, size_t v_i_2320_, lean_object* v_b_2321_){
_start:
{
uint8_t v___x_2323_; 
v___x_2323_ = lean_usize_dec_lt(v_i_2320_, v_sz_2319_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v_b_2321_);
return v___x_2324_;
}
else
{
lean_object* v_snd_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2343_; 
v_snd_2325_ = lean_ctor_get(v_b_2321_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_b_2321_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_b_2321_, 0);
lean_dec(v_unused_2344_);
v___x_2327_ = v_b_2321_;
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_snd_2325_);
lean_dec(v_b_2321_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2343_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v_a_2331_; lean_object* v_a_2338_; 
v___x_2329_ = lean_box(0);
v_a_2338_ = lean_array_uget_borrowed(v_as_2318_, v_i_2320_);
if (lean_obj_tag(v_a_2338_) == 0)
{
v_a_2331_ = v_snd_2325_;
goto v___jp_2330_;
}
else
{
lean_object* v_val_2339_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v_val_2339_ = lean_ctor_get(v_a_2338_, 0);
v___x_2340_ = l_Lean_LocalDecl_fvarId(v_val_2339_);
v___x_2341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2317_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_dec(v___x_2340_);
v_a_2331_ = v_snd_2325_;
goto v___jp_2330_;
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_array_push(v_snd_2325_, v___x_2340_);
v_a_2331_ = v___x_2342_;
goto v___jp_2330_;
}
}
v___jp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v_a_2331_);
lean_ctor_set(v___x_2327_, 0, v___x_2329_);
v___x_2333_ = v___x_2327_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_a_2331_);
v___x_2333_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
size_t v___x_2334_; size_t v___x_2335_; 
v___x_2334_ = ((size_t)1ULL);
v___x_2335_ = lean_usize_add(v_i_2320_, v___x_2334_);
v_i_2320_ = v___x_2335_;
v_b_2321_ = v___x_2333_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(lean_object* v_a_2345_, lean_object* v_as_2346_, lean_object* v_sz_2347_, lean_object* v_i_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_){
_start:
{
size_t v_sz_boxed_2351_; size_t v_i_boxed_2352_; lean_object* v_res_2353_; 
v_sz_boxed_2351_ = lean_unbox_usize(v_sz_2347_);
lean_dec(v_sz_2347_);
v_i_boxed_2352_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_res_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2345_, v_as_2346_, v_sz_boxed_2351_, v_i_boxed_2352_, v_b_2349_);
lean_dec_ref(v_as_2346_);
lean_dec_ref(v_a_2345_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(lean_object* v_a_2354_, lean_object* v_as_2355_, size_t v_sz_2356_, size_t v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_usize_dec_lt(v_i_2357_, v_sz_2356_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_b_2358_);
return v___x_2365_;
}
else
{
lean_object* v_snd_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2384_; 
v_snd_2366_ = lean_ctor_get(v_b_2358_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_b_2358_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v_b_2358_, 0);
lean_dec(v_unused_2385_);
v___x_2368_ = v_b_2358_;
v_isShared_2369_ = v_isSharedCheck_2384_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_snd_2366_);
lean_dec(v_b_2358_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2384_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v_a_2372_; lean_object* v_a_2379_; 
v___x_2370_ = lean_box(0);
v_a_2379_ = lean_array_uget_borrowed(v_as_2355_, v_i_2357_);
if (lean_obj_tag(v_a_2379_) == 0)
{
v_a_2372_ = v_snd_2366_;
goto v___jp_2371_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2381_; uint8_t v___x_2382_; 
v_val_2380_ = lean_ctor_get(v_a_2379_, 0);
v___x_2381_ = l_Lean_LocalDecl_fvarId(v_val_2380_);
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2354_, v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec(v___x_2381_);
v_a_2372_ = v_snd_2366_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_array_push(v_snd_2366_, v___x_2381_);
v_a_2372_ = v___x_2383_;
goto v___jp_2371_;
}
}
v___jp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 1, v_a_2372_);
lean_ctor_set(v___x_2368_, 0, v___x_2370_);
v___x_2374_ = v___x_2368_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v_a_2372_);
v___x_2374_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
size_t v___x_2375_; size_t v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = ((size_t)1ULL);
v___x_2376_ = lean_usize_add(v_i_2357_, v___x_2375_);
v___x_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2354_, v_as_2355_, v_sz_2356_, v___x_2376_, v___x_2374_);
return v___x_2377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(lean_object* v_a_2386_, lean_object* v_as_2387_, lean_object* v_sz_2388_, lean_object* v_i_2389_, lean_object* v_b_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2388_);
lean_dec(v_sz_2388_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2389_);
lean_dec(v_i_2389_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2386_, v_as_2387_, v_sz_boxed_2396_, v_i_boxed_2397_, v_b_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_as_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(lean_object* v_init_2399_, lean_object* v_a_2400_, lean_object* v_n_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
if (lean_obj_tag(v_n_2401_) == 0)
{
lean_object* v_cs_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v_cs_2408_ = lean_ctor_get(v_n_2401_, 0);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v_b_2402_);
v_sz_2411_ = lean_array_size(v_cs_2408_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2399_, v_a_2400_, v_cs_2408_, v_sz_2411_, v___x_2412_, v___x_2410_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2428_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2428_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2428_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_fst_2418_; 
v_fst_2418_ = lean_ctor_get(v_a_2414_, 0);
if (lean_obj_tag(v_fst_2418_) == 0)
{
lean_object* v_snd_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v_snd_2419_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_snd_2419_);
lean_dec(v_a_2414_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_snd_2419_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2420_);
v___x_2422_ = v___x_2416_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
else
{
lean_object* v_val_2424_; lean_object* v___x_2426_; 
lean_inc_ref(v_fst_2418_);
lean_dec(v_a_2414_);
v_val_2424_ = lean_ctor_get(v_fst_2418_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v_fst_2418_, 1);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_val_2424_);
v___x_2426_ = v___x_2416_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_val_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2413_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2413_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
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
lean_object* v_vs_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v_vs_2437_ = lean_ctor_get(v_n_2401_, 0);
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v_b_2402_);
v_sz_2440_ = lean_array_size(v_vs_2437_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_2400_, v_vs_2437_, v_sz_2440_, v___x_2441_, v___x_2439_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2457_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2457_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2457_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_fst_2447_; 
v_fst_2447_ = lean_ctor_get(v_a_2443_, 0);
if (lean_obj_tag(v_fst_2447_) == 0)
{
lean_object* v_snd_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v_snd_2448_ = lean_ctor_get(v_a_2443_, 1);
lean_inc(v_snd_2448_);
lean_dec(v_a_2443_);
v___x_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_snd_2448_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2449_);
v___x_2451_ = v___x_2445_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
else
{
lean_object* v_val_2453_; lean_object* v___x_2455_; 
lean_inc_ref(v_fst_2447_);
lean_dec(v_a_2443_);
v_val_2453_ = lean_ctor_get(v_fst_2447_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v_fst_2447_, 1);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v_val_2453_);
v___x_2455_ = v___x_2445_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_val_2453_);
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
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2442_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2442_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(lean_object* v_init_2466_, lean_object* v_a_2467_, lean_object* v_as_2468_, size_t v_sz_2469_, size_t v_i_2470_, lean_object* v_b_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_usize_dec_lt(v_i_2470_, v_sz_2469_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_b_2471_);
return v___x_2478_;
}
else
{
lean_object* v_snd_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2513_; 
v_snd_2479_ = lean_ctor_get(v_b_2471_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_b_2471_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v_b_2471_, 0);
lean_dec(v_unused_2514_);
v___x_2481_ = v_b_2471_;
v_isShared_2482_ = v_isSharedCheck_2513_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_snd_2479_);
lean_dec(v_b_2471_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2513_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_box(0);
v_a_2484_ = lean_array_uget_borrowed(v_as_2468_, v_i_2470_);
lean_inc(v_snd_2479_);
v___x_2485_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2466_, v_a_2467_, v_a_2484_, v_snd_2479_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2504_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2504_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2504_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
if (lean_obj_tag(v_a_2486_) == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2486_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2490_);
v___x_2492_ = v___x_2481_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_snd_2479_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2492_);
v___x_2494_ = v___x_2488_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; 
lean_del_object(v___x_2488_);
lean_dec(v_snd_2479_);
v_a_2497_ = lean_ctor_get(v_a_2486_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v_a_2486_, 1);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v_a_2497_);
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2499_ = v___x_2481_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_a_2497_);
v___x_2499_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
size_t v___x_2500_; size_t v___x_2501_; 
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2470_, v___x_2500_);
v_i_2470_ = v___x_2501_;
v_b_2471_ = v___x_2499_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_del_object(v___x_2481_);
lean_dec(v_snd_2479_);
v_a_2505_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2485_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2485_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(lean_object* v_init_2515_, lean_object* v_a_2516_, lean_object* v_as_2517_, lean_object* v_sz_2518_, lean_object* v_i_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
size_t v_sz_boxed_2526_; size_t v_i_boxed_2527_; lean_object* v_res_2528_; 
v_sz_boxed_2526_ = lean_unbox_usize(v_sz_2518_);
lean_dec(v_sz_2518_);
v_i_boxed_2527_ = lean_unbox_usize(v_i_2519_);
lean_dec(v_i_2519_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_2515_, v_a_2516_, v_as_2517_, v_sz_boxed_2526_, v_i_boxed_2527_, v_b_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec_ref(v_as_2517_);
lean_dec_ref(v_a_2516_);
lean_dec_ref(v_init_2515_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(lean_object* v_init_2529_, lean_object* v_a_2530_, lean_object* v_n_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2529_, v_a_2530_, v_n_2531_, v_b_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v_n_2531_);
lean_dec_ref(v_a_2530_);
lean_dec_ref(v_init_2529_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(lean_object* v_a_2539_, lean_object* v_as_2540_, size_t v_sz_2541_, size_t v_i_2542_, lean_object* v_b_2543_){
_start:
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_usize_dec_lt(v_i_2542_, v_sz_2541_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_b_2543_);
return v___x_2546_;
}
else
{
lean_object* v_snd_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2565_; 
v_snd_2547_ = lean_ctor_get(v_b_2543_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_b_2543_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v_b_2543_, 0);
lean_dec(v_unused_2566_);
v___x_2549_ = v_b_2543_;
v_isShared_2550_ = v_isSharedCheck_2565_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_snd_2547_);
lean_dec(v_b_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2565_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v_a_2553_; lean_object* v_a_2560_; 
v___x_2551_ = lean_box(0);
v_a_2560_ = lean_array_uget_borrowed(v_as_2540_, v_i_2542_);
if (lean_obj_tag(v_a_2560_) == 0)
{
v_a_2553_ = v_snd_2547_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v_val_2561_ = lean_ctor_get(v_a_2560_, 0);
v___x_2562_ = l_Lean_LocalDecl_fvarId(v_val_2561_);
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2539_, v___x_2562_);
if (v___x_2563_ == 0)
{
lean_dec(v___x_2562_);
v_a_2553_ = v_snd_2547_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_array_push(v_snd_2547_, v___x_2562_);
v_a_2553_ = v___x_2564_;
goto v___jp_2552_;
}
}
v___jp_2552_:
{
lean_object* v___x_2555_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v_a_2553_);
lean_ctor_set(v___x_2549_, 0, v___x_2551_);
v___x_2555_ = v___x_2549_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_a_2553_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
size_t v___x_2556_; size_t v___x_2557_; 
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2542_, v___x_2556_);
v_i_2542_ = v___x_2557_;
v_b_2543_ = v___x_2555_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(lean_object* v_a_2567_, lean_object* v_as_2568_, lean_object* v_sz_2569_, lean_object* v_i_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_){
_start:
{
size_t v_sz_boxed_2573_; size_t v_i_boxed_2574_; lean_object* v_res_2575_; 
v_sz_boxed_2573_ = lean_unbox_usize(v_sz_2569_);
lean_dec(v_sz_2569_);
v_i_boxed_2574_ = lean_unbox_usize(v_i_2570_);
lean_dec(v_i_2570_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2567_, v_as_2568_, v_sz_boxed_2573_, v_i_boxed_2574_, v_b_2571_);
lean_dec_ref(v_as_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(lean_object* v_a_2576_, lean_object* v_as_2577_, size_t v_sz_2578_, size_t v_i_2579_, lean_object* v_b_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
uint8_t v___x_2586_; 
v___x_2586_ = lean_usize_dec_lt(v_i_2579_, v_sz_2578_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_b_2580_);
return v___x_2587_;
}
else
{
lean_object* v_snd_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2606_; 
v_snd_2588_ = lean_ctor_get(v_b_2580_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_b_2580_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v_b_2580_, 0);
lean_dec(v_unused_2607_);
v___x_2590_ = v_b_2580_;
v_isShared_2591_ = v_isSharedCheck_2606_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_snd_2588_);
lean_dec(v_b_2580_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2606_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v_a_2594_; lean_object* v_a_2601_; 
v___x_2592_ = lean_box(0);
v_a_2601_ = lean_array_uget_borrowed(v_as_2577_, v_i_2579_);
if (lean_obj_tag(v_a_2601_) == 0)
{
v_a_2594_ = v_snd_2588_;
goto v___jp_2593_;
}
else
{
lean_object* v_val_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_val_2602_ = lean_ctor_get(v_a_2601_, 0);
v___x_2603_ = l_Lean_LocalDecl_fvarId(v_val_2602_);
v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_2576_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec(v___x_2603_);
v_a_2594_ = v_snd_2588_;
goto v___jp_2593_;
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_array_push(v_snd_2588_, v___x_2603_);
v_a_2594_ = v___x_2605_;
goto v___jp_2593_;
}
}
v___jp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v_a_2594_);
lean_ctor_set(v___x_2590_, 0, v___x_2592_);
v___x_2596_ = v___x_2590_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_a_2594_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
size_t v___x_2597_; size_t v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2579_, v___x_2597_);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2576_, v_as_2577_, v_sz_2578_, v___x_2598_, v___x_2596_);
return v___x_2599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(lean_object* v_a_2608_, lean_object* v_as_2609_, lean_object* v_sz_2610_, lean_object* v_i_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
size_t v_sz_boxed_2618_; size_t v_i_boxed_2619_; lean_object* v_res_2620_; 
v_sz_boxed_2618_ = lean_unbox_usize(v_sz_2610_);
lean_dec(v_sz_2610_);
v_i_boxed_2619_ = lean_unbox_usize(v_i_2611_);
lean_dec(v_i_2611_);
v_res_2620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2608_, v_as_2609_, v_sz_boxed_2618_, v_i_boxed_2619_, v_b_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_as_2609_);
lean_dec_ref(v_a_2608_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(lean_object* v_a_2621_, lean_object* v_t_2622_, lean_object* v_init_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_root_2629_; lean_object* v_tail_2630_; lean_object* v___x_2631_; 
v_root_2629_ = lean_ctor_get(v_t_2622_, 0);
v_tail_2630_ = lean_ctor_get(v_t_2622_, 1);
lean_inc_ref(v_init_2623_);
v___x_2631_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_2623_, v_a_2621_, v_root_2629_, v_init_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec_ref(v_init_2623_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2668_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2668_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2668_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
if (lean_obj_tag(v_a_2632_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; 
v_a_2636_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v_a_2632_, 1);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_a_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; size_t v_sz_2643_; size_t v___x_2644_; lean_object* v___x_2645_; 
lean_del_object(v___x_2634_);
v_a_2640_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v_a_2632_, 1);
v___x_2641_ = lean_box(0);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v_a_2640_);
v_sz_2643_ = lean_array_size(v_tail_2630_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_2621_, v_tail_2630_, v_sz_2643_, v___x_2644_, v___x_2642_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2659_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2659_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_fst_2650_; 
v_fst_2650_ = lean_ctor_get(v_a_2646_, 0);
if (lean_obj_tag(v_fst_2650_) == 0)
{
lean_object* v_snd_2651_; lean_object* v___x_2653_; 
v_snd_2651_ = lean_ctor_get(v_a_2646_, 1);
lean_inc(v_snd_2651_);
lean_dec(v_a_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_snd_2651_);
v___x_2653_ = v___x_2648_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_snd_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
else
{
lean_object* v_val_2655_; lean_object* v___x_2657_; 
lean_inc_ref(v_fst_2650_);
lean_dec(v_a_2646_);
v_val_2655_ = lean_ctor_get(v_fst_2650_, 0);
lean_inc(v_val_2655_);
lean_dec_ref_known(v_fst_2650_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_val_2655_);
v___x_2657_ = v___x_2648_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_val_2655_);
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
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_a_2660_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2645_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2645_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
v_a_2669_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2631_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2631_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(lean_object* v_a_2677_, lean_object* v_t_2678_, lean_object* v_init_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2677_, v_t_2678_, v_init_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec_ref(v_t_2678_);
lean_dec_ref(v_a_2677_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2(lean_object* v_candidates_2688_, lean_object* v_mvarId_2689_, lean_object* v___f_2690_, lean_object* v___f_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_lctx_2697_; lean_object* v_decls_2698_; lean_object* v___x_2699_; 
v_lctx_2697_ = lean_ctor_get(v___y_2692_, 2);
v_decls_2698_ = lean_ctor_get(v_lctx_2697_, 1);
lean_inc_ref(v_decls_2698_);
v___x_2699_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(v_decls_2698_, v_candidates_2688_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = l_Lean_MVarId_getType(v_mvarId_2689_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v_a_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___y_2708_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_2702_, v___y_2693_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref(v___x_2703_);
v___x_2705_ = l_Lean_Expr_hasFVar(v_a_2704_);
v___x_2706_ = lean_st_mk_ref(v_a_2700_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v_a_2704_);
lean_dec_ref(v___f_2691_);
v___x_2732_ = lean_box(0);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___x_2706_);
v___x_2733_ = lean_apply_7(v___f_2690_, v___x_2732_, v___x_2706_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, lean_box(0));
v___y_2708_ = v___x_2733_;
goto v___jp_2707_;
}
else
{
lean_object* v___x_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0));
v___x_2735_ = 0;
v___x_2736_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_2734_, v___f_2691_, v_a_2704_, v___x_2735_, v___x_2706_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___x_2706_);
v___x_2738_ = lean_apply_7(v___f_2690_, v_a_2737_, v___x_2706_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, lean_box(0));
v___y_2708_ = v___x_2738_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v___x_2706_);
lean_dec_ref(v_decls_2698_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___f_2690_);
v_a_2739_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2736_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2736_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
v___jp_2707_:
{
if (lean_obj_tag(v___y_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2723_; 
v_a_2709_ = lean_ctor_get(v___y_2708_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___y_2708_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2711_ = v___y_2708_;
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___y_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v_size_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2713_ = lean_st_ref_get(v___x_2706_);
lean_dec(v___x_2706_);
lean_dec(v___x_2713_);
v_size_2714_ = lean_ctor_get(v_a_2709_, 0);
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_nat_dec_eq(v_size_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_del_object(v___x_2711_);
v___x_2717_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_2718_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(v_a_2709_, v_decls_2698_, v___x_2717_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v_decls_2698_);
lean_dec(v_a_2709_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec(v_a_2709_);
lean_dec_ref(v_decls_2698_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
v___x_2719_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2719_);
v___x_2721_ = v___x_2711_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v___x_2706_);
lean_dec_ref(v_decls_2698_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
v_a_2724_ = lean_ctor_get(v___y_2708_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___y_2708_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___y_2708_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___y_2708_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_a_2700_);
lean_dec_ref(v_decls_2698_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___f_2690_);
v_a_2747_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2701_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2701_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_decls_2698_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v___f_2691_);
lean_dec_ref(v___f_2690_);
lean_dec(v_mvarId_2689_);
v_a_2755_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2699_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2699_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(lean_object* v_candidates_2763_, lean_object* v_mvarId_2764_, lean_object* v___f_2765_, lean_object* v___f_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_MVarId_getNondepPropHyps___lam__2(v_candidates_2763_, v_mvarId_2764_, v___f_2765_, v___f_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object* v_mvarId_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v_candidates_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; 
v___f_2781_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__0));
v___f_2782_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___closed__1));
v_candidates_2783_ = l_Lean_instEmptyCollectionFVarIdHashSet;
lean_inc(v_mvarId_2775_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lean_MVarId_getNondepPropHyps___lam__2___boxed), 9, 4);
lean_closure_set(v___f_2784_, 0, v_candidates_2783_);
lean_closure_set(v___f_2784_, 1, v_mvarId_2775_);
lean_closure_set(v___f_2784_, 2, v___f_2782_);
lean_closure_set(v___f_2784_, 3, v___f_2781_);
v___x_2785_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_2775_, v___f_2784_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getNondepPropHyps___boxed(lean_object* v_mvarId_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Lean_MVarId_getNondepPropHyps(v_mvarId_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(lean_object* v_00_u03b2_2793_, lean_object* v_m_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_2794_, v_a_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(lean_object* v_00_u03b2_2797_, lean_object* v_m_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(v_00_u03b2_2797_, v_m_2798_, v_a_2799_);
lean_dec(v_a_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(lean_object* v_00_u03b2_2801_, lean_object* v_m_2802_, lean_object* v_a_2803_, lean_object* v_b_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_2802_, v_a_2803_, v_b_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(lean_object* v_00_u03b2_2806_, lean_object* v_m_2807_, lean_object* v_a_2808_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_2807_, v_a_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(lean_object* v_00_u03b2_2810_, lean_object* v_m_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_res_2813_; lean_object* v_r_2814_; 
v_res_2813_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(v_00_u03b2_2810_, v_m_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_m_2811_);
v_r_2814_ = lean_box(v_res_2813_);
return v_r_2814_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(lean_object* v_00_u03b2_2815_, lean_object* v_a_2816_, lean_object* v_x_2817_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_2816_, v_x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2819_, lean_object* v_a_2820_, lean_object* v_x_2821_){
_start:
{
uint8_t v_res_2822_; lean_object* v_r_2823_; 
v_res_2822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_2819_, v_a_2820_, v_x_2821_);
lean_dec(v_x_2821_);
lean_dec(v_a_2820_);
v_r_2823_ = lean_box(v_res_2822_);
return v_r_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(lean_object* v_00_u03b2_2824_, lean_object* v_a_2825_, lean_object* v_x_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_2825_, v_x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2828_, lean_object* v_a_2829_, lean_object* v_x_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_2828_, v_a_2829_, v_x_2830_);
lean_dec(v_a_2829_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(lean_object* v_e_2832_, lean_object* v_a_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_2832_, v_a_2833_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(lean_object* v_e_2841_, lean_object* v_a_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_2841_, v_a_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec(v_a_2842_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(lean_object* v_00_u03b2_2850_, lean_object* v_data_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_2853_, v_a_2854_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_2862_, v_a_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v_a_2863_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_2871_, lean_object* v_i_2872_, lean_object* v_source_2873_, lean_object* v_target_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_2872_, v_source_2873_, v_target_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(lean_object* v_a_2876_, lean_object* v_as_2877_, size_t v_sz_2878_, size_t v_i_2879_, lean_object* v_b_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_2876_, v_as_2877_, v_sz_2878_, v_i_2879_, v_b_2880_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(lean_object* v_a_2887_, lean_object* v_as_2888_, lean_object* v_sz_2889_, lean_object* v_i_2890_, lean_object* v_b_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
size_t v_sz_boxed_2897_; size_t v_i_boxed_2898_; lean_object* v_res_2899_; 
v_sz_boxed_2897_ = lean_unbox_usize(v_sz_2889_);
lean_dec(v_sz_2889_);
v_i_boxed_2898_ = lean_unbox_usize(v_i_2890_);
lean_dec(v_i_2890_);
v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_2887_, v_as_2888_, v_sz_boxed_2897_, v_i_boxed_2898_, v_b_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v_as_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2899_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(lean_object* v_00_u03b2_2900_, lean_object* v_m_2901_, lean_object* v_a_2902_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_2901_, v_a_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b2_2904_, lean_object* v_m_2905_, lean_object* v_a_2906_){
_start:
{
uint8_t v_res_2907_; lean_object* v_r_2908_; 
v_res_2907_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_2904_, v_m_2905_, v_a_2906_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_m_2905_);
v_r_2908_ = lean_box(v_res_2907_);
return v_r_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2909_, lean_object* v_m_2910_, lean_object* v_a_2911_, lean_object* v_b_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_2910_, v_a_2911_, v_b_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_2915_, v_x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(lean_object* v_a_2918_, lean_object* v_as_2919_, size_t v_sz_2920_, size_t v_i_2921_, lean_object* v_b_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_2918_, v_as_2919_, v_sz_2920_, v_i_2921_, v_b_2922_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(lean_object* v_a_2929_, lean_object* v_as_2930_, lean_object* v_sz_2931_, lean_object* v_i_2932_, lean_object* v_b_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
size_t v_sz_boxed_2939_; size_t v_i_boxed_2940_; lean_object* v_res_2941_; 
v_sz_boxed_2939_ = lean_unbox_usize(v_sz_2931_);
lean_dec(v_sz_2931_);
v_i_boxed_2940_ = lean_unbox_usize(v_i_2932_);
lean_dec(v_i_2932_);
v_res_2941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_2929_, v_as_2930_, v_sz_boxed_2939_, v_i_boxed_2940_, v_b_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v_as_2930_);
lean_dec_ref(v_a_2929_);
return v_res_2941_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(lean_object* v_00_u03b2_2942_, lean_object* v_a_2943_, lean_object* v_x_2944_){
_start:
{
uint8_t v___x_2945_; 
v___x_2945_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_2943_, v_x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(lean_object* v_00_u03b2_2946_, lean_object* v_a_2947_, lean_object* v_x_2948_){
_start:
{
uint8_t v_res_2949_; lean_object* v_r_2950_; 
v_res_2949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_2946_, v_a_2947_, v_x_2948_);
lean_dec(v_x_2948_);
lean_dec_ref(v_a_2947_);
v_r_2950_ = lean_box(v_res_2949_);
return v_r_2950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(lean_object* v_00_u03b2_2951_, lean_object* v_data_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(lean_object* v_00_u03b2_2954_, lean_object* v_i_2955_, lean_object* v_source_2956_, lean_object* v_target_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_2955_, v_source_2956_, v_target_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(lean_object* v_00_u03b2_2959_, lean_object* v_x_2960_, lean_object* v_x_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_2960_, v_x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_maxRecDepthErrorMessage;
v___x_2969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
return v___x_2969_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
v___x_2971_ = l_Lean_MessageData_ofFormat(v___x_2970_);
return v___x_2971_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
v___x_2973_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2));
v___x_2974_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(lean_object* v_ref_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_ref_2975_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(lean_object* v_ref_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2980_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(lean_object* v_00_u03b1_2983_, lean_object* v_ref_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_2984_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(lean_object* v_00_u03b1_2992_, lean_object* v_ref_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_2992_, v_ref_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(lean_object* v_x_3001_, lean_object* v_mvarId_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_toCold_3009_; lean_object* v_currRecDepth_3010_; lean_object* v_ref_3011_; uint16_t v_optionFlags_3012_; uint8_t v_suppressElabErrors_3013_; uint8_t v_isRecordingDeps_3014_; lean_object* v_maxRecDepth_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_toCold_3009_ = lean_ctor_get(v_a_3006_, 0);
v_currRecDepth_3010_ = lean_ctor_get(v_a_3006_, 1);
v_ref_3011_ = lean_ctor_get(v_a_3006_, 2);
v_optionFlags_3012_ = lean_ctor_get_uint16(v_a_3006_, sizeof(void*)*3);
v_suppressElabErrors_3013_ = lean_ctor_get_uint8(v_a_3006_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3014_ = lean_ctor_get_uint8(v_a_3006_, sizeof(void*)*3 + 3);
v_maxRecDepth_3042_ = lean_ctor_get(v_toCold_3009_, 3);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_nat_dec_eq(v_maxRecDepth_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = lean_nat_dec_eq(v_currRecDepth_3010_, v_maxRecDepth_3042_);
if (v___x_3045_ == 0)
{
goto v___jp_3015_;
}
else
{
lean_object* v___x_3046_; 
lean_dec(v_mvarId_3002_);
lean_dec_ref(v_x_3001_);
lean_inc(v_ref_3011_);
v___x_3046_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_3011_);
return v___x_3046_;
}
}
else
{
goto v___jp_3015_;
}
v___jp_3015_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_add(v_currRecDepth_3010_, v___x_3016_);
lean_inc(v_ref_3011_);
lean_inc_ref(v_toCold_3009_);
v___x_3018_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3018_, 0, v_toCold_3009_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
lean_ctor_set(v___x_3018_, 2, v_ref_3011_);
lean_ctor_set_uint16(v___x_3018_, sizeof(void*)*3, v_optionFlags_3012_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*3 + 2, v_suppressElabErrors_3013_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*3 + 3, v_isRecordingDeps_3014_);
lean_inc_ref(v_x_3001_);
lean_inc(v_a_3007_);
lean_inc_ref(v___x_3018_);
lean_inc(v_a_3005_);
lean_inc_ref(v_a_3004_);
lean_inc(v_mvarId_3002_);
v___x_3019_ = lean_apply_6(v_x_3001_, v_mvarId_3002_, v_a_3004_, v_a_3005_, v___x_3018_, v_a_3007_, lean_box(0));
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3033_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3033_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
if (lean_obj_tag(v_a_3020_) == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_dec_ref_known(v___x_3018_, 3);
lean_dec_ref(v_x_3001_);
v___x_3024_ = lean_st_ref_take(v_a_3003_);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_array_push(v___x_3024_, v_mvarId_3002_);
v___x_3027_ = lean_st_ref_put(v_a_3003_, v___x_3026_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3025_);
v___x_3029_ = v___x_3022_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3025_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
else
{
lean_object* v_val_3031_; lean_object* v___x_3032_; 
lean_del_object(v___x_3022_);
lean_dec(v_mvarId_3002_);
v_val_3031_ = lean_ctor_get(v_a_3020_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v_a_3020_, 1);
v___x_3032_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3001_, v_val_3031_, v_a_3003_, v_a_3004_, v_a_3005_, v___x_3018_, v_a_3007_);
lean_dec_ref_known(v___x_3018_, 3);
return v___x_3032_;
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref_known(v___x_3018_, 3);
lean_dec(v_mvarId_3002_);
lean_dec_ref(v_x_3001_);
v_a_3034_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3019_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3019_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(lean_object* v_x_3047_, lean_object* v_as_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
if (lean_obj_tag(v_as_3048_) == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v_x_3047_);
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
else
{
lean_object* v_head_3057_; lean_object* v_tail_3058_; lean_object* v___x_3059_; 
v_head_3057_ = lean_ctor_get(v_as_3048_, 0);
lean_inc(v_head_3057_);
v_tail_3058_ = lean_ctor_get(v_as_3048_, 1);
lean_inc(v_tail_3058_);
lean_dec_ref_known(v_as_3048_, 2);
lean_inc_ref(v_x_3047_);
v___x_3059_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3047_, v_head_3057_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
v_as_3048_ = v_tail_3058_;
goto _start;
}
else
{
lean_dec(v_tail_3058_);
lean_dec_ref(v_x_3047_);
return v___x_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(lean_object* v_x_3061_, lean_object* v_as_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_3061_, v_as_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(lean_object* v_x_3070_, lean_object* v_mvarId_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3070_, v_mvarId_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate(lean_object* v_mvarId_3079_, lean_object* v_x_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3087_ = lean_st_mk_ref(v___x_3086_);
v___x_3088_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(v_x_3080_, v_mvarId_3079_, v___x_3087_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3097_; 
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3088_, 0);
lean_dec(v_unused_3098_);
v___x_3090_ = v___x_3088_;
v_isShared_3091_ = v_isSharedCheck_3097_;
goto v_resetjp_3089_;
}
else
{
lean_dec(v___x_3088_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3097_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3092_ = lean_st_ref_get(v___x_3087_);
lean_dec(v___x_3087_);
v___x_3093_ = lean_array_to_list(v___x_3092_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v___x_3087_);
v_a_3099_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3088_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3088_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_saturate___boxed(lean_object* v_mvarId_3107_, lean_object* v_x_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Meta_saturate(v_mvarId_3107_, v_x_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne(lean_object* v_mvarIds_3115_, lean_object* v_msg_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
if (lean_obj_tag(v_mvarIds_3115_) == 1)
{
lean_object* v_tail_3122_; 
v_tail_3122_ = lean_ctor_get(v_mvarIds_3115_, 1);
if (lean_obj_tag(v_tail_3122_) == 0)
{
lean_object* v_head_3123_; lean_object* v___x_3124_; 
lean_dec_ref(v_msg_3116_);
v_head_3123_ = lean_ctor_get(v_mvarIds_3115_, 0);
lean_inc(v_head_3123_);
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_head_3123_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3125_;
}
}
else
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
return v___x_3126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_exactlyOne___boxed(lean_object* v_mvarIds_3127_, lean_object* v_msg_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Meta_exactlyOne(v_mvarIds_3127_, v_msg_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_mvarIds_3127_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne(lean_object* v_mvarIds_3135_, lean_object* v_msg_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
if (lean_obj_tag(v_mvarIds_3135_) == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec_ref(v_msg_3136_);
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
return v___x_3143_;
}
else
{
lean_object* v_tail_3144_; 
v_tail_3144_ = lean_ctor_get(v_mvarIds_3135_, 1);
if (lean_obj_tag(v_tail_3144_) == 0)
{
lean_object* v_head_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec_ref(v_msg_3136_);
v_head_3145_ = lean_ctor_get(v_mvarIds_3135_, 0);
lean_inc(v_head_3145_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_head_3145_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(v_msg_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
return v___x_3148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureAtMostOne___boxed(lean_object* v_mvarIds_3149_, lean_object* v_msg_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Meta_ensureAtMostOne(v_mvarIds_3149_, v_msg_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_mvarIds_3149_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3157_, size_t v_sz_3158_, size_t v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
uint8_t v___x_3166_; 
v___x_3166_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_b_3160_);
return v___x_3167_;
}
else
{
lean_object* v_snd_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3198_; 
v_snd_3168_ = lean_ctor_get(v_b_3160_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_b_3160_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v_b_3160_, 0);
lean_dec(v_unused_3199_);
v___x_3170_ = v_b_3160_;
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_snd_3168_);
lean_dec(v_b_3160_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3198_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v_a_3174_; lean_object* v_a_3181_; 
v___x_3172_ = lean_box(0);
v_a_3181_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
if (lean_obj_tag(v_a_3181_) == 0)
{
v_a_3174_ = v_snd_3168_;
goto v___jp_3173_;
}
else
{
lean_object* v_val_3182_; uint8_t v___x_3183_; 
v_val_3182_ = lean_ctor_get(v_a_3181_, 0);
v___x_3183_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = l_Lean_LocalDecl_type(v_val_3182_);
v___x_3185_ = l_Lean_Meta_isProp(v___x_3184_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; uint8_t v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = lean_unbox(v_a_3186_);
lean_dec(v_a_3186_);
if (v___x_3187_ == 0)
{
v_a_3174_ = v_snd_3168_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = l_Lean_LocalDecl_fvarId(v_val_3182_);
v___x_3189_ = lean_array_push(v_snd_3168_, v___x_3188_);
v_a_3174_ = v___x_3189_;
goto v___jp_3173_;
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_del_object(v___x_3170_);
lean_dec(v_snd_3168_);
v_a_3190_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3185_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3185_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
v_a_3174_ = v_snd_3168_;
goto v___jp_3173_;
}
}
v___jp_3173_:
{
lean_object* v___x_3176_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v_a_3174_);
lean_ctor_set(v___x_3170_, 0, v___x_3172_);
v___x_3176_ = v___x_3170_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_a_3174_);
v___x_3176_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
size_t v___x_3177_; size_t v___x_3178_; 
v___x_3177_ = ((size_t)1ULL);
v___x_3178_ = lean_usize_add(v_i_3159_, v___x_3177_);
v_i_3159_ = v___x_3178_;
v_b_3160_ = v___x_3176_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3200_, lean_object* v_sz_3201_, lean_object* v_i_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
size_t v_sz_boxed_3209_; size_t v_i_boxed_3210_; lean_object* v_res_3211_; 
v_sz_boxed_3209_ = lean_unbox_usize(v_sz_3201_);
lean_dec(v_sz_3201_);
v_i_boxed_3210_ = lean_unbox_usize(v_i_3202_);
lean_dec(v_i_3202_);
v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3200_, v_sz_boxed_3209_, v_i_boxed_3210_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v_as_3200_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_b_3215_);
return v___x_3222_;
}
else
{
lean_object* v_snd_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3253_; 
v_snd_3223_ = lean_ctor_get(v_b_3215_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_b_3215_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v_b_3215_, 0);
lean_dec(v_unused_3254_);
v___x_3225_ = v_b_3215_;
v_isShared_3226_ = v_isSharedCheck_3253_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_snd_3223_);
lean_dec(v_b_3215_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3253_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v_a_3229_; lean_object* v_a_3236_; 
v___x_3227_ = lean_box(0);
v_a_3236_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
if (lean_obj_tag(v_a_3236_) == 0)
{
v_a_3229_ = v_snd_3223_;
goto v___jp_3228_;
}
else
{
lean_object* v_val_3237_; uint8_t v___x_3238_; 
v_val_3237_ = lean_ctor_get(v_a_3236_, 0);
v___x_3238_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = l_Lean_LocalDecl_type(v_val_3237_);
v___x_3240_ = l_Lean_Meta_isProp(v___x_3239_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; uint8_t v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
v___x_3242_ = lean_unbox(v_a_3241_);
lean_dec(v_a_3241_);
if (v___x_3242_ == 0)
{
v_a_3229_ = v_snd_3223_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = l_Lean_LocalDecl_fvarId(v_val_3237_);
v___x_3244_ = lean_array_push(v_snd_3223_, v___x_3243_);
v_a_3229_ = v___x_3244_;
goto v___jp_3228_;
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_del_object(v___x_3225_);
lean_dec(v_snd_3223_);
v_a_3245_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3240_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3240_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
v_a_3229_ = v_snd_3223_;
goto v___jp_3228_;
}
}
v___jp_3228_:
{
lean_object* v___x_3231_; 
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v_a_3229_);
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3231_ = v___x_3225_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_a_3229_);
v___x_3231_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((size_t)1ULL);
v___x_3233_ = lean_usize_add(v_i_3214_, v___x_3232_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_3212_, v_sz_3213_, v___x_3233_, v___x_3231_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3255_, lean_object* v_sz_3256_, lean_object* v_i_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3256_);
lean_dec(v_sz_3256_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3257_);
lean_dec(v_i_3257_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_3255_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec_ref(v_as_3255_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(lean_object* v_init_3267_, lean_object* v_n_3268_, lean_object* v_b_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
if (lean_obj_tag(v_n_3268_) == 0)
{
lean_object* v_cs_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; size_t v_sz_3278_; size_t v___x_3279_; lean_object* v___x_3280_; 
v_cs_3275_ = lean_ctor_get(v_n_3268_, 0);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v_b_3269_);
v_sz_3278_ = lean_array_size(v_cs_3275_);
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3267_, v_cs_3275_, v_sz_3278_, v___x_3279_, v___x_3277_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3295_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3295_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3295_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v_fst_3285_; 
v_fst_3285_ = lean_ctor_get(v_a_3281_, 0);
if (lean_obj_tag(v_fst_3285_) == 0)
{
lean_object* v_snd_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v_snd_3286_ = lean_ctor_get(v_a_3281_, 1);
lean_inc(v_snd_3286_);
lean_dec(v_a_3281_);
v___x_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_snd_3286_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3287_);
v___x_3289_ = v___x_3283_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
else
{
lean_object* v_val_3291_; lean_object* v___x_3293_; 
lean_inc_ref(v_fst_3285_);
lean_dec(v_a_3281_);
v_val_3291_ = lean_ctor_get(v_fst_3285_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v_fst_3285_, 1);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v_val_3291_);
v___x_3293_ = v___x_3283_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_val_3291_);
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
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
v_a_3296_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3280_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3280_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
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
lean_object* v_vs_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; size_t v_sz_3307_; size_t v___x_3308_; lean_object* v___x_3309_; 
v_vs_3304_ = lean_ctor_get(v_n_3268_, 0);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v_b_3269_);
v_sz_3307_ = lean_array_size(v_vs_3304_);
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_3304_, v_sz_3307_, v___x_3308_, v___x_3306_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3324_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3324_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3324_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v_fst_3314_; 
v_fst_3314_ = lean_ctor_get(v_a_3310_, 0);
if (lean_obj_tag(v_fst_3314_) == 0)
{
lean_object* v_snd_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v_snd_3315_ = lean_ctor_get(v_a_3310_, 1);
lean_inc(v_snd_3315_);
lean_dec(v_a_3310_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_snd_3315_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3316_);
v___x_3318_ = v___x_3312_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
else
{
lean_object* v_val_3320_; lean_object* v___x_3322_; 
lean_inc_ref(v_fst_3314_);
lean_dec(v_a_3310_);
v_val_3320_ = lean_ctor_get(v_fst_3314_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v_fst_3314_, 1);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_val_3320_);
v___x_3322_ = v___x_3312_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_val_3320_);
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
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
v_a_3325_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3309_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3309_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(lean_object* v_init_3333_, lean_object* v_as_3334_, size_t v_sz_3335_, size_t v_i_3336_, lean_object* v_b_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
uint8_t v___x_3343_; 
v___x_3343_ = lean_usize_dec_lt(v_i_3336_, v_sz_3335_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_b_3337_);
return v___x_3344_;
}
else
{
lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3379_; 
v_snd_3345_ = lean_ctor_get(v_b_3337_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_b_3337_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v_b_3337_, 0);
lean_dec(v_unused_3380_);
v___x_3347_ = v_b_3337_;
v_isShared_3348_ = v_isSharedCheck_3379_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_dec(v_b_3337_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3379_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_a_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_box(0);
v_a_3350_ = lean_array_uget_borrowed(v_as_3334_, v_i_3336_);
lean_inc(v_snd_3345_);
v___x_3351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3333_, v_a_3350_, v_snd_3345_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3370_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3370_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
if (lean_obj_tag(v_a_3352_) == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3352_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3356_);
v___x_3358_ = v___x_3347_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_snd_3345_);
v___x_3358_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3358_);
v___x_3360_ = v___x_3354_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; 
lean_del_object(v___x_3354_);
lean_dec(v_snd_3345_);
v_a_3363_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v_a_3352_, 1);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 1, v_a_3363_);
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3365_ = v___x_3347_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_a_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3336_, v___x_3366_);
v_i_3336_ = v___x_3367_;
v_b_3337_ = v___x_3365_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_del_object(v___x_3347_);
lean_dec(v_snd_3345_);
v_a_3371_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3351_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3351_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3381_, lean_object* v_as_3382_, lean_object* v_sz_3383_, lean_object* v_i_3384_, lean_object* v_b_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
size_t v_sz_boxed_3391_; size_t v_i_boxed_3392_; lean_object* v_res_3393_; 
v_sz_boxed_3391_ = lean_unbox_usize(v_sz_3383_);
lean_dec(v_sz_3383_);
v_i_boxed_3392_ = lean_unbox_usize(v_i_3384_);
lean_dec(v_i_3384_);
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_3381_, v_as_3382_, v_sz_boxed_3391_, v_i_boxed_3392_, v_b_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v_as_3382_);
lean_dec_ref(v_init_3381_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(lean_object* v_init_3394_, lean_object* v_n_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3394_, v_n_3395_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v_n_3395_);
lean_dec_ref(v_init_3394_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(lean_object* v_as_3403_, size_t v_sz_3404_, size_t v_i_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_usize_dec_lt(v_i_3405_, v_sz_3404_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; 
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v_b_3406_);
return v___x_3413_;
}
else
{
lean_object* v_snd_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3444_; 
v_snd_3414_ = lean_ctor_get(v_b_3406_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_b_3406_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v_b_3406_, 0);
lean_dec(v_unused_3445_);
v___x_3416_ = v_b_3406_;
v_isShared_3417_ = v_isSharedCheck_3444_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_snd_3414_);
lean_dec(v_b_3406_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3444_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v_a_3420_; lean_object* v_a_3427_; 
v___x_3418_ = lean_box(0);
v_a_3427_ = lean_array_uget_borrowed(v_as_3403_, v_i_3405_);
if (lean_obj_tag(v_a_3427_) == 0)
{
v_a_3420_ = v_snd_3414_;
goto v___jp_3419_;
}
else
{
lean_object* v_val_3428_; uint8_t v___x_3429_; 
v_val_3428_ = lean_ctor_get(v_a_3427_, 0);
v___x_3429_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = l_Lean_LocalDecl_type(v_val_3428_);
v___x_3431_ = l_Lean_Meta_isProp(v___x_3430_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; uint8_t v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = lean_unbox(v_a_3432_);
lean_dec(v_a_3432_);
if (v___x_3433_ == 0)
{
v_a_3420_ = v_snd_3414_;
goto v___jp_3419_;
}
else
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = l_Lean_LocalDecl_fvarId(v_val_3428_);
v___x_3435_ = lean_array_push(v_snd_3414_, v___x_3434_);
v_a_3420_ = v___x_3435_;
goto v___jp_3419_;
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_del_object(v___x_3416_);
lean_dec(v_snd_3414_);
v_a_3436_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3431_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3431_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
v_a_3420_ = v_snd_3414_;
goto v___jp_3419_;
}
}
v___jp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v_a_3420_);
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_a_3420_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
size_t v___x_3423_; size_t v___x_3424_; 
v___x_3423_ = ((size_t)1ULL);
v___x_3424_ = lean_usize_add(v_i_3405_, v___x_3423_);
v_i_3405_ = v___x_3424_;
v_b_3406_ = v___x_3422_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3446_, lean_object* v_sz_3447_, lean_object* v_i_3448_, lean_object* v_b_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
size_t v_sz_boxed_3455_; size_t v_i_boxed_3456_; lean_object* v_res_3457_; 
v_sz_boxed_3455_ = lean_unbox_usize(v_sz_3447_);
lean_dec(v_sz_3447_);
v_i_boxed_3456_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3446_, v_sz_boxed_3455_, v_i_boxed_3456_, v_b_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_as_3446_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(lean_object* v_as_3458_, size_t v_sz_3459_, size_t v_i_3460_, lean_object* v_b_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_usize_dec_lt(v_i_3460_, v_sz_3459_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_b_3461_);
return v___x_3468_;
}
else
{
lean_object* v_snd_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3499_; 
v_snd_3469_ = lean_ctor_get(v_b_3461_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_b_3461_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; 
v_unused_3500_ = lean_ctor_get(v_b_3461_, 0);
lean_dec(v_unused_3500_);
v___x_3471_ = v_b_3461_;
v_isShared_3472_ = v_isSharedCheck_3499_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_snd_3469_);
lean_dec(v_b_3461_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3499_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_a_3475_; lean_object* v_a_3482_; 
v___x_3473_ = lean_box(0);
v_a_3482_ = lean_array_uget_borrowed(v_as_3458_, v_i_3460_);
if (lean_obj_tag(v_a_3482_) == 0)
{
v_a_3475_ = v_snd_3469_;
goto v___jp_3474_;
}
else
{
lean_object* v_val_3483_; uint8_t v___x_3484_; 
v_val_3483_ = lean_ctor_get(v_a_3482_, 0);
v___x_3484_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = l_Lean_LocalDecl_type(v_val_3483_);
v___x_3486_ = l_Lean_Meta_isProp(v___x_3485_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; uint8_t v___x_3488_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
v___x_3488_ = lean_unbox(v_a_3487_);
lean_dec(v_a_3487_);
if (v___x_3488_ == 0)
{
v_a_3475_ = v_snd_3469_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = l_Lean_LocalDecl_fvarId(v_val_3483_);
v___x_3490_ = lean_array_push(v_snd_3469_, v___x_3489_);
v_a_3475_ = v___x_3490_;
goto v___jp_3474_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_del_object(v___x_3471_);
lean_dec(v_snd_3469_);
v_a_3491_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3486_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3486_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
else
{
v_a_3475_ = v_snd_3469_;
goto v___jp_3474_;
}
}
v___jp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v_a_3475_);
lean_ctor_set(v___x_3471_, 0, v___x_3473_);
v___x_3477_ = v___x_3471_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3475_);
v___x_3477_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
size_t v___x_3478_; size_t v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = ((size_t)1ULL);
v___x_3479_ = lean_usize_add(v_i_3460_, v___x_3478_);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_3458_, v_sz_3459_, v___x_3479_, v___x_3477_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
return v___x_3480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(lean_object* v_as_3501_, lean_object* v_sz_3502_, lean_object* v_i_3503_, lean_object* v_b_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
size_t v_sz_boxed_3510_; size_t v_i_boxed_3511_; lean_object* v_res_3512_; 
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3502_);
lean_dec(v_sz_3502_);
v_i_boxed_3511_ = lean_unbox_usize(v_i_3503_);
lean_dec(v_i_3503_);
v_res_3512_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_3501_, v_sz_boxed_3510_, v_i_boxed_3511_, v_b_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v_as_3501_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(lean_object* v_t_3513_, lean_object* v_init_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_root_3520_; lean_object* v_tail_3521_; lean_object* v___x_3522_; 
v_root_3520_ = lean_ctor_get(v_t_3513_, 0);
v_tail_3521_ = lean_ctor_get(v_t_3513_, 1);
lean_inc_ref(v_init_3514_);
v___x_3522_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_3514_, v_root_3520_, v_init_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec_ref(v_init_3514_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3559_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3559_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3559_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
if (lean_obj_tag(v_a_3523_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; 
v_a_3527_ = lean_ctor_get(v_a_3523_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v_a_3523_, 1);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v_a_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; size_t v_sz_3534_; size_t v___x_3535_; lean_object* v___x_3536_; 
lean_del_object(v___x_3525_);
v_a_3531_ = lean_ctor_get(v_a_3523_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v_a_3523_, 1);
v___x_3532_ = lean_box(0);
v___x_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_a_3531_);
v_sz_3534_ = lean_array_size(v_tail_3521_);
v___x_3535_ = ((size_t)0ULL);
v___x_3536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_3521_, v_sz_3534_, v___x_3535_, v___x_3533_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3550_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3550_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3550_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_fst_3541_; 
v_fst_3541_ = lean_ctor_get(v_a_3537_, 0);
if (lean_obj_tag(v_fst_3541_) == 0)
{
lean_object* v_snd_3542_; lean_object* v___x_3544_; 
v_snd_3542_ = lean_ctor_get(v_a_3537_, 1);
lean_inc(v_snd_3542_);
lean_dec(v_a_3537_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v_snd_3542_);
v___x_3544_ = v___x_3539_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_snd_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
else
{
lean_object* v_val_3546_; lean_object* v___x_3548_; 
lean_inc_ref(v_fst_3541_);
lean_dec(v_a_3537_);
v_val_3546_ = lean_ctor_get(v_fst_3541_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v_fst_3541_, 1);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v_val_3546_);
v___x_3548_ = v___x_3539_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_val_3546_);
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
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
v_a_3551_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3536_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3536_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_a_3560_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3522_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3522_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(lean_object* v_t_3568_, lean_object* v_init_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_t_3568_, v_init_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v_t_3568_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps(lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v_lctx_3581_; lean_object* v_decls_3582_; lean_object* v_result_3583_; lean_object* v___x_3584_; 
v_lctx_3581_ = lean_ctor_get(v_a_3576_, 2);
v_decls_3582_ = lean_ctor_get(v_lctx_3581_, 1);
v_result_3583_ = ((lean_object*)(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0));
v___x_3584_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(v_decls_3582_, v_result_3583_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getPropHyps___boxed(lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_Meta_getPropHyps(v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
return v_res_3590_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Lean_MVarId_inferInstance___lam__0___closed__1));
v___x_3595_ = l_Lean_MessageData_ofFormat(v___x_3594_);
return v___x_3595_;
}
}
static lean_object* _init_l_Lean_MVarId_inferInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__2, &l_Lean_MVarId_inferInstance___lam__0___closed__2_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__2);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0(lean_object* v_mvarId_3598_, lean_object* v___x_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
lean_inc(v___x_3599_);
lean_inc(v_mvarId_3598_);
v___x_3605_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3598_, v___x_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3606_; 
lean_dec_ref_known(v___x_3605_, 1);
lean_inc(v_mvarId_3598_);
v___x_3606_ = l_Lean_MVarId_getType(v_mvarId_3598_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3608_ = lean_box(0);
v___x_3609_ = l_Lean_Meta_synthInstance(v_a_3607_, v___x_3608_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
lean_inc(v_mvarId_3598_);
v___x_3611_ = l_Lean_mkMVar(v_mvarId_3598_);
v___x_3612_ = l_Lean_Meta_isExprDefEq(v___x_3611_, v_a_3610_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3624_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3624_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3624_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
uint8_t v___x_3617_; 
v___x_3617_ = lean_unbox(v_a_3613_);
lean_dec(v_a_3613_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_del_object(v___x_3615_);
v___x_3618_ = lean_obj_once(&l_Lean_MVarId_inferInstance___lam__0___closed__3, &l_Lean_MVarId_inferInstance___lam__0___closed__3_once, _init_l_Lean_MVarId_inferInstance___lam__0___closed__3);
v___x_3619_ = l_Lean_Meta_throwTacticEx___redArg(v___x_3599_, v_mvarId_3598_, v___x_3618_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec(v___x_3599_);
lean_dec(v_mvarId_3598_);
v___x_3620_ = lean_box(0);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3620_);
v___x_3622_ = v___x_3615_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
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
lean_dec(v___x_3599_);
lean_dec(v_mvarId_3598_);
v_a_3625_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3612_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3612_);
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
lean_dec(v___x_3599_);
lean_dec(v_mvarId_3598_);
v_a_3633_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3609_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3609_);
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
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec(v___x_3599_);
lean_dec(v_mvarId_3598_);
v_a_3641_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3606_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3606_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
lean_dec(v___x_3599_);
lean_dec(v_mvarId_3598_);
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___lam__0___boxed(lean_object* v_mvarId_3649_, lean_object* v___x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_MVarId_inferInstance___lam__0(v_mvarId_3649_, v___x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance(lean_object* v_mvarId_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v___x_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((lean_object*)(l_Lean_MVarId_inferInstance___closed__1));
lean_inc(v_mvarId_3660_);
v___f_3667_ = lean_alloc_closure((void*)(l_Lean_MVarId_inferInstance___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3667_, 0, v_mvarId_3660_);
lean_closure_set(v___f_3667_, 1, v___x_3666_);
v___x_3668_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(v_mvarId_3660_, v___f_3667_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_inferInstance___boxed(lean_object* v_mvarId_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_MVarId_inferInstance(v_mvarId_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl(lean_object* v_x_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_obj_tag_nat(v_x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorIdx___impl___boxed(lean_object* v_x_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_Meta_TacticResultCNM_ctorIdx___impl(v_x_3678_);
lean_dec(v_x_3678_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___redArg(lean_object* v_t_3680_, lean_object* v_k_3681_){
_start:
{
if (lean_obj_tag(v_t_3680_) == 2)
{
lean_object* v_mvarId_3682_; lean_object* v___x_3683_; 
v_mvarId_3682_ = lean_ctor_get(v_t_3680_, 0);
lean_inc(v_mvarId_3682_);
lean_dec_ref_known(v_t_3680_, 1);
v___x_3683_ = lean_apply_1(v_k_3681_, v_mvarId_3682_);
return v___x_3683_;
}
else
{
lean_dec(v_t_3680_);
return v_k_3681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim(lean_object* v_motive_3684_, lean_object* v_ctorIdx_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_, lean_object* v_k_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3686_, v_k_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_ctorElim___boxed(lean_object* v_motive_3690_, lean_object* v_ctorIdx_3691_, lean_object* v_t_3692_, lean_object* v_h_3693_, lean_object* v_k_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_Meta_TacticResultCNM_ctorElim(v_motive_3690_, v_ctorIdx_3691_, v_t_3692_, v_h_3693_, v_k_3694_);
lean_dec(v_ctorIdx_3691_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim___redArg(lean_object* v_t_3696_, lean_object* v_closed_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3696_, v_closed_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_closed_elim(lean_object* v_motive_3699_, lean_object* v_t_3700_, lean_object* v_h_3701_, lean_object* v_closed_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3700_, v_closed_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(lean_object* v_t_3704_, lean_object* v_noChange_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3704_, v_noChange_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_noChange_elim(lean_object* v_motive_3707_, lean_object* v_t_3708_, lean_object* v_h_3709_, lean_object* v_noChange_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3708_, v_noChange_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim___redArg(lean_object* v_t_3712_, lean_object* v_modified_3713_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3712_, v_modified_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_TacticResultCNM_modified_elim(lean_object* v_motive_3715_, lean_object* v_t_3716_, lean_object* v_h_3717_, lean_object* v_modified_3718_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_3716_, v_modified_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton(lean_object* v_g_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v_a_3736_; lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_MVarId_getType(v_g_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v___x_3741_ = ((lean_object*)(l_Lean_MVarId_isSubsingleton___closed__1));
v___x_3742_ = lean_unsigned_to_nat(1u);
v___x_3743_ = lean_mk_empty_array_with_capacity(v___x_3742_);
v___x_3744_ = lean_array_push(v___x_3743_, v_a_3740_);
v___x_3745_ = l_Lean_Meta_mkAppM(v___x_3741_, v___x_3744_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = lean_box(0);
v___x_3748_ = l_Lean_Meta_synthInstance(v_a_3746_, v___x_3747_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3757_; 
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; 
v_unused_3758_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3758_);
v___x_3750_ = v___x_3748_;
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v___x_3748_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
uint8_t v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3752_ = 1;
v___x_3753_ = lean_box(v___x_3752_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3753_);
v___x_3755_ = v___x_3750_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
else
{
lean_object* v_a_3759_; 
v_a_3759_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3748_, 1);
v_a_3736_ = v_a_3759_;
goto v___jp_3735_;
}
}
else
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3745_, 1);
v_a_3736_ = v_a_3760_;
goto v___jp_3735_;
}
}
else
{
lean_object* v_a_3761_; 
v_a_3761_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3739_, 1);
v_a_3736_ = v_a_3761_;
goto v___jp_3735_;
}
v___jp_3729_:
{
if (v___y_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_dec_ref(v___y_3730_);
v___x_3732_ = lean_box(v___y_3731_);
v___x_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
return v___x_3733_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___y_3730_);
return v___x_3734_;
}
}
v___jp_3735_:
{
uint8_t v___x_3737_; 
v___x_3737_ = l_Lean_Exception_isInterrupt(v_a_3736_);
if (v___x_3737_ == 0)
{
uint8_t v___x_3738_; 
lean_inc_ref(v_a_3736_);
v___x_3738_ = l_Lean_Exception_isRuntime(v_a_3736_);
v___y_3730_ = v_a_3736_;
v___y_3731_ = v___x_3738_;
goto v___jp_3729_;
}
else
{
v___y_3730_ = v_a_3736_;
v___y_3731_ = v___x_3737_;
goto v___jp_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isSubsingleton___boxed(lean_object* v_g_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_MVarId_isSubsingleton(v_g_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_));
v___x_3789_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3786_, v___x_3787_, v___x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(lean_object* v_a_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
return v_res_3791_;
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
