// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Util import Lean.Meta.Sym.Util import Lean.Meta.Tactic.Grind.Util
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nestedProof"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 140, 29, 19, 223, 104, 218, 25)}};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nestedDecidable"};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 76, 105, 85, 179, 183, 200, 153)}};
static const lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonApp___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "_private.Lean.Meta.Tactic.Grind.MarkNestedSubsingletons.0.Lean.Meta.Grind.markNestedSubsingletons.visit"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Meta.Tactic.Grind.MarkNestedSubsingletons"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "grind mark subsingleton"};
static const lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_markNestedSubsingletons___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonConst(lean_object* v_e_13_){
_start:
{
if (lean_obj_tag(v_e_13_) == 4)
{
lean_object* v_declName_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_declName_14_ = lean_ctor_get(v_e_13_, 0);
v___x_15_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_16_ = lean_name_eq(v_declName_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5));
v___x_18_ = lean_name_eq(v_declName_14_, v___x_17_);
return v___x_18_;
}
else
{
return v___x_16_;
}
}
else
{
uint8_t v___x_19_; 
v___x_19_ = 0;
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonConst___boxed(lean_object* v_e_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_e_20_);
lean_dec_ref(v_e_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMarkedSubsingletonApp(lean_object* v_e_23_){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l_Lean_Expr_getAppFn(v_e_23_);
v___x_25_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v___x_24_);
lean_dec_ref(v___x_24_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = l_Lean_Expr_getAppNumArgs(v_e_23_);
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMarkedSubsingletonApp___boxed(lean_object* v_e_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_29_);
lean_dec_ref(v_e_29_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_whnfCore(v_e_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_75_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_75_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_75_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_75_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_42_, v_a_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_66_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_66_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_66_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_66_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Expr_cleanupAnnotations(v_a_47_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_dec_ref(v___x_56_);
lean_del_object(v___x_44_);
goto v___jp_51_;
}
else
{
lean_object* v_arg_58_; lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_arg_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc_ref(v_arg_58_);
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_60_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___closed__1));
v___x_61_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_60_);
lean_dec_ref(v___x_59_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_arg_58_);
lean_del_object(v___x_44_);
goto v___jp_51_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_64_; 
lean_del_object(v___x_49_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v_arg_58_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_62_);
v___x_64_ = v___x_44_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
v___jp_51_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_del_object(v___x_44_);
v_a_67_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_46_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_46_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
v_a_76_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_41_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_41_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable___boxed(lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(v_e_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_instMonadEIO(lean_box(0));
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_toApplicative_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_177_; 
v___x_108_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__0);
v___x_109_ = l_StateRefT_x27_instMonad___redArg(v___x_108_);
v_toApplicative_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___x_109_, 1);
lean_dec(v_unused_178_);
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_177_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_toApplicative_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_177_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_toFunctor_114_; lean_object* v_toSeq_115_; lean_object* v_toSeqLeft_116_; lean_object* v_toSeqRight_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_175_; 
v_toFunctor_114_ = lean_ctor_get(v_toApplicative_110_, 0);
v_toSeq_115_ = lean_ctor_get(v_toApplicative_110_, 2);
v_toSeqLeft_116_ = lean_ctor_get(v_toApplicative_110_, 3);
v_toSeqRight_117_ = lean_ctor_get(v_toApplicative_110_, 4);
v_isSharedCheck_175_ = !lean_is_exclusive(v_toApplicative_110_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v_toApplicative_110_, 1);
lean_dec(v_unused_176_);
v___x_119_ = v_toApplicative_110_;
v_isShared_120_ = v_isSharedCheck_175_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_toSeqRight_117_);
lean_inc(v_toSeqLeft_116_);
lean_inc(v_toSeq_115_);
lean_inc(v_toFunctor_114_);
lean_dec(v_toApplicative_110_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_175_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___f_121_; lean_object* v___f_122_; lean_object* v___f_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___f_126_; lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___x_130_; 
v___f_121_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__1));
v___f_122_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__2));
lean_inc_ref(v_toFunctor_114_);
v___f_123_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_123_, 0, v_toFunctor_114_);
v___f_124_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_124_, 0, v_toFunctor_114_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___f_123_);
lean_ctor_set(v___x_125_, 1, v___f_124_);
v___f_126_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_126_, 0, v_toSeqRight_117_);
v___f_127_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_127_, 0, v_toSeqLeft_116_);
v___f_128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_128_, 0, v_toSeq_115_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___f_126_);
lean_ctor_set(v___x_119_, 3, v___f_127_);
lean_ctor_set(v___x_119_, 2, v___f_128_);
lean_ctor_set(v___x_119_, 1, v___f_121_);
lean_ctor_set(v___x_119_, 0, v___x_125_);
v___x_130_ = v___x_119_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___f_121_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v___f_128_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___f_127_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___f_126_);
v___x_130_ = v_reuseFailAlloc_174_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_132_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___f_122_);
lean_ctor_set(v___x_112_, 0, v___x_130_);
v___x_132_ = v___x_112_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___f_122_);
v___x_132_ = v_reuseFailAlloc_173_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v_toApplicative_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_171_; 
v___x_133_ = l_StateRefT_x27_instMonad___redArg(v___x_132_);
v_toApplicative_134_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_133_, 1);
lean_dec(v_unused_172_);
v___x_136_ = v___x_133_;
v_isShared_137_ = v_isSharedCheck_171_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_toApplicative_134_);
lean_dec(v___x_133_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_171_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_toFunctor_138_; lean_object* v_toSeq_139_; lean_object* v_toSeqLeft_140_; lean_object* v_toSeqRight_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_169_; 
v_toFunctor_138_ = lean_ctor_get(v_toApplicative_134_, 0);
v_toSeq_139_ = lean_ctor_get(v_toApplicative_134_, 2);
v_toSeqLeft_140_ = lean_ctor_get(v_toApplicative_134_, 3);
v_toSeqRight_141_ = lean_ctor_get(v_toApplicative_134_, 4);
v_isSharedCheck_169_ = !lean_is_exclusive(v_toApplicative_134_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v_toApplicative_134_, 1);
lean_dec(v_unused_170_);
v___x_143_ = v_toApplicative_134_;
v_isShared_144_ = v_isSharedCheck_169_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_toSeqRight_141_);
lean_inc(v_toSeqLeft_140_);
lean_inc(v_toSeq_139_);
lean_inc(v_toFunctor_138_);
lean_dec(v_toApplicative_134_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_169_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___f_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_154_; 
v___f_145_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__3));
v___f_146_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___closed__4));
lean_inc_ref(v_toFunctor_138_);
v___f_147_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_147_, 0, v_toFunctor_138_);
v___f_148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_148_, 0, v_toFunctor_138_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___f_147_);
lean_ctor_set(v___x_149_, 1, v___f_148_);
v___f_150_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_150_, 0, v_toSeqRight_141_);
v___f_151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_151_, 0, v_toSeqLeft_140_);
v___f_152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_152_, 0, v_toSeq_139_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 4, v___f_150_);
lean_ctor_set(v___x_143_, 3, v___f_151_);
lean_ctor_set(v___x_143_, 2, v___f_152_);
lean_ctor_set(v___x_143_, 1, v___f_145_);
lean_ctor_set(v___x_143_, 0, v___x_149_);
v___x_154_ = v___x_143_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___f_145_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v___f_152_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v___f_151_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v___f_150_);
v___x_154_ = v_reuseFailAlloc_168_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___f_146_);
lean_ctor_set(v___x_136_, 0, v___x_154_);
v___x_156_ = v___x_136_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___f_146_);
v___x_156_ = v_reuseFailAlloc_167_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_71552__overap_165_; lean_object* v___x_166_; 
v___x_157_ = l_StateRefT_x27_instMonad___redArg(v___x_156_);
v___x_158_ = l_ReaderT_instMonad___redArg(v___x_157_);
v___x_159_ = l_StateRefT_x27_instMonad___redArg(v___x_158_);
v___x_160_ = l_ReaderT_instMonad___redArg(v___x_159_);
v___x_161_ = l_ReaderT_instMonad___redArg(v___x_160_);
v___x_162_ = l_StateRefT_x27_instMonad___redArg(v___x_161_);
v___x_163_ = l_Lean_instInhabitedExpr;
v___x_164_ = l_instInhabitedOfMonad___redArg(v___x_162_, v___x_163_);
v___x_71552__overap_165_ = lean_panic_fn_borrowed(v___x_164_, v_msg_96_);
lean_dec(v___x_164_);
lean_inc(v___y_106_);
lean_inc_ref(v___y_105_);
lean_inc(v___y_104_);
lean_inc_ref(v___y_103_);
lean_inc(v___y_102_);
lean_inc_ref(v___y_101_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc(v___y_97_);
v___x_166_ = lean_apply_11(v___x_71552__overap_165_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, lean_box(0));
return v___x_166_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4___boxed(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v_msg_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec(v___y_180_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_value_196_; lean_object* v_tail_197_; uint8_t v___x_198_; 
v_key_195_ = lean_ctor_get(v_x_193_, 0);
v_value_196_ = lean_ctor_get(v_x_193_, 1);
v_tail_197_ = lean_ctor_get(v_x_193_, 2);
v___x_198_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_195_, v_a_192_);
if (v___x_198_ == 0)
{
v_x_193_ = v_tail_197_;
goto _start;
}
else
{
lean_object* v___x_200_; 
lean_inc(v_value_196_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_value_196_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg___boxed(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_201_, v_x_202_);
lean_dec(v_x_202_);
lean_dec_ref(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_buckets_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_buckets_206_ = lean_ctor_get(v_m_204_, 1);
v___x_207_ = lean_array_get_size(v_buckets_206_);
v___x_208_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_205_);
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___x_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___x_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_207_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v___x_220_ = lean_array_uget_borrowed(v_buckets_206_, v___x_219_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_205_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg___boxed(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_222_, v_a_223_);
lean_dec_ref(v_a_223_);
lean_dec_ref(v_m_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(lean_object* v_a_225_, lean_object* v_b_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_dec(v_b_226_);
lean_dec_ref(v_a_225_);
return v_x_227_;
}
else
{
lean_object* v_key_228_; lean_object* v_value_229_; lean_object* v_tail_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_242_; 
v_key_228_ = lean_ctor_get(v_x_227_, 0);
v_value_229_ = lean_ctor_get(v_x_227_, 1);
v_tail_230_ = lean_ctor_get(v_x_227_, 2);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_242_ == 0)
{
v___x_232_ = v_x_227_;
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_tail_230_);
lean_inc(v_value_229_);
lean_inc(v_key_228_);
lean_dec(v_x_227_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_242_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; 
v___x_234_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_228_, v_a_225_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_225_, v_b_226_, v_tail_230_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 2, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_key_228_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_value_229_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_240_; 
lean_dec(v_value_229_);
lean_dec(v_key_228_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_b_226_);
lean_ctor_set(v___x_232_, 0, v_a_225_);
v___x_240_ = v___x_232_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_225_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_b_226_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_tail_230_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
return v_x_243_;
}
else
{
lean_object* v_key_245_; lean_object* v_value_246_; lean_object* v_tail_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_270_; 
v_key_245_ = lean_ctor_get(v_x_244_, 0);
v_value_246_ = lean_ctor_get(v_x_244_, 1);
v_tail_247_ = lean_ctor_get(v_x_244_, 2);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_270_ == 0)
{
v___x_249_ = v_x_244_;
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_tail_247_);
lean_inc(v_value_246_);
lean_inc(v_key_245_);
lean_dec(v_x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_270_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_251_ = lean_array_get_size(v_x_243_);
v___x_252_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_245_);
v___x_253_ = 32ULL;
v___x_254_ = lean_uint64_shift_right(v___x_252_, v___x_253_);
v_fold_255_ = lean_uint64_xor(v___x_252_, v___x_254_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_251_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v___x_264_ = lean_array_uget_borrowed(v_x_243_, v___x_263_);
lean_inc(v___x_264_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 2, v___x_264_);
v___x_266_ = v___x_249_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_key_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_value_246_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_264_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; 
v___x_267_ = lean_array_uset(v_x_243_, v___x_263_, v___x_266_);
v_x_243_ = v___x_267_;
v_x_244_ = v_tail_247_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(lean_object* v_i_271_, lean_object* v_source_272_, lean_object* v_target_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_array_get_size(v_source_272_);
v___x_275_ = lean_nat_dec_lt(v_i_271_, v___x_274_);
if (v___x_275_ == 0)
{
lean_dec_ref(v_source_272_);
lean_dec(v_i_271_);
return v_target_273_;
}
else
{
lean_object* v_es_276_; lean_object* v___x_277_; lean_object* v_source_278_; lean_object* v_target_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_es_276_ = lean_array_fget(v_source_272_, v_i_271_);
v___x_277_ = lean_box(0);
v_source_278_ = lean_array_fset(v_source_272_, v_i_271_, v___x_277_);
v_target_279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(v_target_273_, v_es_276_);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_i_271_, v___x_280_);
lean_dec(v_i_271_);
v_i_271_ = v___x_281_;
v_source_272_ = v_source_278_;
v_target_273_ = v_target_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(lean_object* v_data_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_nbuckets_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_284_ = lean_array_get_size(v_data_283_);
v___x_285_ = lean_unsigned_to_nat(2u);
v_nbuckets_286_ = lean_nat_mul(v___x_284_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_box(0);
v___x_289_ = lean_mk_array(v_nbuckets_286_, v___x_288_);
v___x_290_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(v___x_287_, v_data_283_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(lean_object* v_a_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
else
{
lean_object* v_key_294_; lean_object* v_tail_295_; uint8_t v___x_296_; 
v_key_294_ = lean_ctor_get(v_x_292_, 0);
v_tail_295_ = lean_ctor_get(v_x_292_, 2);
v___x_296_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_key_294_, v_a_291_);
if (v___x_296_ == 0)
{
v_x_292_ = v_tail_295_;
goto _start;
}
else
{
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg___boxed(lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_298_, v_x_299_);
lean_dec(v_x_299_);
lean_dec_ref(v_a_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
lean_object* v_size_305_; lean_object* v_buckets_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_349_; 
v_size_305_ = lean_ctor_get(v_m_302_, 0);
v_buckets_306_ = lean_ctor_get(v_m_302_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_m_302_);
if (v_isSharedCheck_349_ == 0)
{
v___x_308_ = v_m_302_;
v_isShared_309_ = v_isSharedCheck_349_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_buckets_306_);
lean_inc(v_size_305_);
lean_dec(v_m_302_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_349_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v_fold_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v_bkt_323_; uint8_t v___x_324_; 
v___x_310_ = lean_array_get_size(v_buckets_306_);
v___x_311_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_303_);
v___x_312_ = 32ULL;
v___x_313_ = lean_uint64_shift_right(v___x_311_, v___x_312_);
v_fold_314_ = lean_uint64_xor(v___x_311_, v___x_313_);
v___x_315_ = 16ULL;
v___x_316_ = lean_uint64_shift_right(v_fold_314_, v___x_315_);
v___x_317_ = lean_uint64_xor(v_fold_314_, v___x_316_);
v___x_318_ = lean_uint64_to_usize(v___x_317_);
v___x_319_ = lean_usize_of_nat(v___x_310_);
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_sub(v___x_319_, v___x_320_);
v___x_322_ = lean_usize_land(v___x_318_, v___x_321_);
v_bkt_323_ = lean_array_uget_borrowed(v_buckets_306_, v___x_322_);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_303_, v_bkt_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v_size_x27_326_; lean_object* v___x_327_; lean_object* v_buckets_x27_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v_size_x27_326_ = lean_nat_add(v_size_305_, v___x_325_);
lean_dec(v_size_305_);
lean_inc(v_bkt_323_);
v___x_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_327_, 0, v_a_303_);
lean_ctor_set(v___x_327_, 1, v_b_304_);
lean_ctor_set(v___x_327_, 2, v_bkt_323_);
v_buckets_x27_328_ = lean_array_uset(v_buckets_306_, v___x_322_, v___x_327_);
v___x_329_ = lean_unsigned_to_nat(4u);
v___x_330_ = lean_nat_mul(v_size_x27_326_, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = lean_nat_div(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_array_get_size(v_buckets_x27_328_);
v___x_334_ = lean_nat_dec_le(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
if (v___x_334_ == 0)
{
lean_object* v_val_335_; lean_object* v___x_337_; 
v_val_335_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(v_buckets_x27_328_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_val_335_);
lean_ctor_set(v___x_308_, 0, v_size_x27_326_);
v___x_337_ = v___x_308_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_size_x27_326_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_val_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
else
{
lean_object* v___x_340_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_buckets_x27_328_);
lean_ctor_set(v___x_308_, 0, v_size_x27_326_);
v___x_340_ = v___x_308_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_x27_326_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_buckets_x27_328_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v_buckets_x27_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
lean_inc(v_bkt_323_);
v___x_342_ = lean_box(0);
v_buckets_x27_343_ = lean_array_uset(v_buckets_306_, v___x_322_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_303_, v_b_304_, v_bkt_323_);
v___x_345_ = lean_array_uset(v_buckets_x27_343_, v___x_322_, v___x_344_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_345_);
v___x_347_ = v___x_308_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_size_305_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(lean_object* v_e_350_, lean_object* v___y_351_){
_start:
{
uint8_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = l_Lean_Expr_hasMVar(v_e_350_);
v___x_354_ = lean_bool_not(v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v_mctx_356_; lean_object* v___x_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; lean_object* v_cache_361_; lean_object* v_zetaDeltaFVarIds_362_; lean_object* v_postponed_363_; lean_object* v_diag_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v___x_355_ = lean_st_ref_get(v___y_351_);
v_mctx_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_mctx_356_);
lean_dec(v___x_355_);
v___x_357_ = l_Lean_instantiateMVarsCore(v_mctx_356_, v_e_350_);
v_fst_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_fst_358_);
v_snd_359_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_snd_359_);
lean_dec_ref(v___x_357_);
v___x_360_ = lean_st_ref_take(v___y_351_);
v_cache_361_ = lean_ctor_get(v___x_360_, 1);
v_zetaDeltaFVarIds_362_ = lean_ctor_get(v___x_360_, 2);
v_postponed_363_ = lean_ctor_get(v___x_360_, 3);
v_diag_364_ = lean_ctor_get(v___x_360_, 4);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_360_, 0);
lean_dec(v_unused_374_);
v___x_366_ = v___x_360_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_diag_364_);
lean_inc(v_postponed_363_);
lean_inc(v_zetaDeltaFVarIds_362_);
lean_inc(v_cache_361_);
lean_dec(v___x_360_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v_snd_359_);
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_snd_359_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_cache_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_zetaDeltaFVarIds_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_postponed_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_diag_364_);
v___x_369_ = v_reuseFailAlloc_372_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_st_ref_set(v___y_351_, v___x_369_);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_fst_358_);
return v___x_371_;
}
}
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_e_350_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg___boxed(lean_object* v_e_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_376_, v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0(void){
_start:
{
lean_object* v___x_380_; lean_object* v_dummy_381_; 
v___x_380_ = lean_box(0);
v_dummy_381_ = l_Lean_Expr_sort___override(v___x_380_);
return v_dummy_381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__3));
v___x_386_ = lean_unsigned_to_nat(13u);
v___x_387_ = lean_unsigned_to_nat(89u);
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__2));
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__1));
v___x_390_ = l_mkPanicMessageWithDecl(v___x_389_, v___x_388_, v___x_387_, v___x_386_, v___x_385_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(lean_object* v_e_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_391_, v_a_399_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = l_Lean_Core_betaReduce(v_a_404_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Lean_Meta_Sym_unfoldReducible(v_a_406_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_a_408_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_411_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v___x_411_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_a_410_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_Grind_foldProjs(v_a_412_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_415_ = l_Lean_Meta_Sym_normalizeLevels(v_a_414_, v_a_400_, v_a_401_);
return v___x_415_;
}
else
{
return v___x_413_;
}
}
else
{
return v___x_411_;
}
}
else
{
return v___x_409_;
}
}
else
{
return v___x_407_;
}
}
else
{
return v___x_405_;
}
}
else
{
return v___x_403_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
v___x_417_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__5));
v___x_418_ = l_Lean_mkConst(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_box(0);
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_421_ = l_Lean_mkConst(v___x_420_, v___x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(lean_object* v_e_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_e_x27_435_; lean_object* v___y_436_; lean_object* v___y_442_; uint8_t v___y_443_; lean_object* v___y_444_; lean_object* v___y_445_; lean_object* v___y_446_; uint8_t v___y_447_; lean_object* v___y_452_; uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v_b_x27_457_; lean_object* v___y_458_; uint8_t v___x_465_; 
v___x_465_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_422_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_st_ref_get(v_a_423_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v___x_466_, v_e_422_);
lean_dec(v___x_466_);
if (lean_obj_tag(v___x_467_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v_e_422_);
v_val_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_val_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 0);
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_val_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
else
{
lean_object* v___x_476_; 
lean_dec(v___x_467_);
lean_inc(v_a_432_);
lean_inc_ref(v_a_431_);
lean_inc(v_a_430_);
lean_inc_ref(v_a_429_);
lean_inc_ref(v_e_422_);
v___x_476_ = lean_infer_type(v_e_422_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc_n(v_a_477_, 2);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = l_Lean_Meta_isProp(v_a_477_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; uint8_t v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = lean_unbox(v_a_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
v___x_481_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_isDecidable(v_a_477_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_546_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_546_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_546_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_546_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
if (lean_obj_tag(v_a_482_) == 1)
{
lean_object* v_val_524_; lean_object* v___x_525_; 
lean_del_object(v___x_484_);
lean_dec(v_a_479_);
v_val_524_ = lean_ctor_get(v_a_482_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v_a_482_, 1);
v___x_525_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_val_524_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_538_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_538_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_538_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_538_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_530_ = lean_st_ref_take(v_a_423_);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__5);
lean_inc_ref(v_e_422_);
v___x_532_ = l_Lean_mkAppB(v___x_531_, v_a_526_, v_e_422_);
lean_inc_ref(v___x_532_);
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_530_, v_e_422_, v___x_532_);
v___x_534_ = lean_st_ref_set(v_a_423_, v___x_533_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_532_);
v___x_536_ = v___x_528_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_532_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_dec_ref(v_e_422_);
return v___x_525_;
}
}
else
{
uint8_t v___x_539_; 
lean_dec(v_a_482_);
v___x_539_ = l_Lean_Expr_isApp(v_e_422_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Expr_isForall(v_e_422_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Expr_isProj(v_e_422_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Expr_isMData(v_e_422_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; 
lean_dec(v_a_479_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_e_422_);
v___x_544_ = v___x_484_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_422_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_del_object(v___x_484_);
goto v___jp_486_;
}
}
else
{
lean_del_object(v___x_484_);
goto v___jp_486_;
}
}
else
{
lean_del_object(v___x_484_);
goto v___jp_486_;
}
}
else
{
lean_del_object(v___x_484_);
goto v___jp_486_;
}
}
v___jp_486_:
{
switch(lean_obj_tag(v_e_422_))
{
case 5:
{
lean_object* v_dummy_487_; lean_object* v_nargs_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; 
v_dummy_487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__0);
v_nargs_488_ = l_Lean_Expr_getAppNumArgs(v_e_422_);
lean_inc(v_nargs_488_);
v___x_489_ = lean_mk_array(v_nargs_488_, v_dummy_487_);
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_sub(v_nargs_488_, v___x_490_);
lean_dec(v_nargs_488_);
v___x_492_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
lean_inc_ref_n(v_e_422_, 2);
v___x_493_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_422_, v___x_492_, v_e_422_, v___x_489_, v___x_491_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v_e_x27_435_ = v_a_494_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
else
{
lean_dec_ref_known(v_e_422_, 2);
return v___x_493_;
}
}
case 11:
{
lean_object* v_typeName_495_; lean_object* v_idx_496_; lean_object* v_struct_497_; lean_object* v___x_498_; 
lean_dec(v_a_479_);
v_typeName_495_ = lean_ctor_get(v_e_422_, 0);
v_idx_496_ = lean_ctor_get(v_e_422_, 1);
v_struct_497_ = lean_ctor_get(v_e_422_, 2);
lean_inc_ref(v_struct_497_);
v___x_498_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_struct_497_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = lean_ptr_addr(v_struct_497_);
v___x_501_ = lean_ptr_addr(v_a_499_);
v___x_502_ = lean_usize_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_inc(v_idx_496_);
lean_inc(v_typeName_495_);
v___x_503_ = l_Lean_Expr_proj___override(v_typeName_495_, v_idx_496_, v_a_499_);
v_e_x27_435_ = v___x_503_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
else
{
lean_dec(v_a_499_);
lean_inc_ref(v_e_422_);
v_e_x27_435_ = v_e_422_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
}
else
{
lean_dec_ref_known(v_e_422_, 3);
return v___x_498_;
}
}
case 10:
{
lean_object* v_data_504_; lean_object* v_expr_505_; lean_object* v___x_506_; 
lean_dec(v_a_479_);
v_data_504_ = lean_ctor_get(v_e_422_, 0);
v_expr_505_ = lean_ctor_get(v_e_422_, 1);
lean_inc_ref(v_expr_505_);
v___x_506_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_expr_505_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; size_t v___x_508_; size_t v___x_509_; uint8_t v___x_510_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = lean_ptr_addr(v_expr_505_);
v___x_509_ = lean_ptr_addr(v_a_507_);
v___x_510_ = lean_usize_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_inc(v_data_504_);
v___x_511_ = l_Lean_Expr_mdata___override(v_data_504_, v_a_507_);
v_e_x27_435_ = v___x_511_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
else
{
lean_dec(v_a_507_);
lean_inc_ref(v_e_422_);
v_e_x27_435_ = v_e_422_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
}
else
{
lean_dec_ref_known(v_e_422_, 2);
return v___x_506_;
}
}
case 7:
{
lean_object* v_binderName_512_; lean_object* v_binderType_513_; lean_object* v_body_514_; uint8_t v_binderInfo_515_; lean_object* v___x_516_; 
lean_dec(v_a_479_);
v_binderName_512_ = lean_ctor_get(v_e_422_, 0);
v_binderType_513_ = lean_ctor_get(v_e_422_, 1);
v_body_514_ = lean_ctor_get(v_e_422_, 2);
v_binderInfo_515_ = lean_ctor_get_uint8(v_e_422_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_513_);
v___x_516_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_binderType_513_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; uint8_t v___x_518_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = l_Lean_Expr_hasLooseBVars(v_body_514_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_inc_ref(v_body_514_);
v___x_519_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_body_514_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
lean_inc_ref(v_binderType_513_);
lean_inc(v_binderName_512_);
lean_inc_ref(v_body_514_);
v___y_452_ = v_body_514_;
v___y_453_ = v_binderInfo_515_;
v___y_454_ = v_a_517_;
v___y_455_ = v_binderName_512_;
v___y_456_ = v_binderType_513_;
v_b_x27_457_ = v_a_520_;
v___y_458_ = v_a_423_;
goto v___jp_451_;
}
else
{
lean_dec(v_a_517_);
lean_dec_ref_known(v_e_422_, 3);
return v___x_519_;
}
}
else
{
lean_inc_ref(v_binderType_513_);
lean_inc(v_binderName_512_);
lean_inc_ref_n(v_body_514_, 2);
v___y_452_ = v_body_514_;
v___y_453_ = v_binderInfo_515_;
v___y_454_ = v_a_517_;
v___y_455_ = v_binderName_512_;
v___y_456_ = v_binderType_513_;
v_b_x27_457_ = v_body_514_;
v___y_458_ = v_a_423_;
goto v___jp_451_;
}
}
else
{
lean_dec_ref_known(v_e_422_, 3);
return v___x_516_;
}
}
default: 
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v_a_479_);
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__4);
v___x_522_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__4(v___x_521_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v_e_x27_435_ = v_a_523_;
v___y_436_ = v_a_423_;
goto v___jp_434_;
}
else
{
lean_dec_ref(v_e_422_);
return v___x_522_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_a_479_);
lean_dec_ref(v_e_422_);
v_a_547_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_481_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_481_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v___x_555_; 
lean_dec(v_a_479_);
v___x_555_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_477_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_568_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_568_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_560_ = lean_st_ref_take(v_a_423_);
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
lean_inc_ref(v_e_422_);
v___x_562_ = l_Lean_mkAppB(v___x_561_, v_a_556_, v_e_422_);
lean_inc_ref(v___x_562_);
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_560_, v_e_422_, v___x_562_);
v___x_564_ = lean_st_ref_set(v_a_423_, v___x_563_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_566_ = v___x_558_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_562_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
else
{
lean_dec_ref(v_e_422_);
return v___x_555_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_477_);
lean_dec_ref(v_e_422_);
v_a_569_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_478_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_478_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_dec_ref(v_e_422_);
return v___x_476_;
}
}
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_e_422_);
return v___x_577_;
}
v___jp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_st_ref_take(v___y_436_);
lean_inc_ref(v_e_x27_435_);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v___x_437_, v_e_422_, v_e_x27_435_);
v___x_439_ = lean_st_ref_set(v___y_436_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_e_x27_435_);
return v___x_440_;
}
v___jp_441_:
{
if (v___y_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Expr_forallE___override(v___y_446_, v___y_444_, v___y_445_, v___y_443_);
v_e_x27_435_ = v___x_448_;
v___y_436_ = v___y_442_;
goto v___jp_434_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = l_Lean_instBEqBinderInfo_beq(v___y_443_, v___y_443_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Expr_forallE___override(v___y_446_, v___y_444_, v___y_445_, v___y_443_);
v_e_x27_435_ = v___x_450_;
v___y_436_ = v___y_442_;
goto v___jp_434_;
}
else
{
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v___y_444_);
lean_inc_ref(v_e_422_);
v_e_x27_435_ = v_e_422_;
v___y_436_ = v___y_442_;
goto v___jp_434_;
}
}
}
v___jp_451_:
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = lean_ptr_addr(v___y_456_);
lean_dec_ref(v___y_456_);
v___x_460_ = lean_ptr_addr(v___y_454_);
v___x_461_ = lean_usize_dec_eq(v___x_459_, v___x_460_);
if (v___x_461_ == 0)
{
lean_dec_ref(v___y_452_);
v___y_442_ = v___y_458_;
v___y_443_ = v___y_453_;
v___y_444_ = v___y_454_;
v___y_445_ = v_b_x27_457_;
v___y_446_ = v___y_455_;
v___y_447_ = v___x_461_;
goto v___jp_441_;
}
else
{
size_t v___x_462_; size_t v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_ptr_addr(v___y_452_);
lean_dec_ref(v___y_452_);
v___x_463_ = lean_ptr_addr(v_b_x27_457_);
v___x_464_ = lean_usize_dec_eq(v___x_462_, v___x_463_);
v___y_442_ = v___y_458_;
v___y_443_ = v___y_453_;
v___y_444_ = v___y_454_;
v___y_445_ = v_b_x27_457_;
v___y_446_ = v___y_455_;
v___y_447_ = v___x_464_;
goto v___jp_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(lean_object* v_upperBound_578_, lean_object* v_a_579_, lean_object* v_b_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_modified_592_; 
v_modified_592_ = lean_nat_dec_lt(v_a_579_, v_upperBound_578_);
if (v_modified_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v_a_579_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v_b_580_);
return v___x_593_;
}
else
{
lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_624_; 
v_fst_594_ = lean_ctor_get(v_b_580_, 0);
v_snd_595_ = lean_ctor_get(v_b_580_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_b_580_);
if (v_isSharedCheck_624_ == 0)
{
v___x_597_ = v_b_580_;
v_isShared_598_ = v_isSharedCheck_624_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_b_580_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_624_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_array_fget_borrowed(v_snd_595_, v_a_579_);
lean_inc(v___x_599_);
v___x_600_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v___x_599_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_a_603_; uint8_t v___x_607_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_607_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_599_, v_a_601_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_dec(v_fst_594_);
v___x_608_ = lean_array_fset(v_snd_595_, v_a_579_, v_a_601_);
v___x_609_ = lean_box(v_modified_592_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_608_);
lean_ctor_set(v___x_597_, 0, v___x_609_);
v___x_611_ = v___x_597_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_608_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v_a_603_ = v___x_611_;
goto v___jp_602_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v_a_601_);
if (v_isShared_598_ == 0)
{
v___x_614_ = v___x_597_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_fst_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_snd_595_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_603_ = v___x_614_;
goto v___jp_602_;
}
}
v___jp_602_:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_a_579_, v___x_604_);
lean_dec(v_a_579_);
v_a_579_ = v___x_605_;
v_b_580_ = v_a_603_;
goto _start;
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_dec(v_a_579_);
v_a_616_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_600_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_600_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(lean_object* v_e_625_, uint8_t v_a_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
if (lean_obj_tag(v_x_627_) == 5)
{
lean_object* v_fn_641_; lean_object* v_arg_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_fn_641_ = lean_ctor_get(v_x_627_, 0);
lean_inc_ref(v_fn_641_);
v_arg_642_ = lean_ctor_get(v_x_627_, 1);
lean_inc_ref(v_arg_642_);
lean_dec_ref_known(v_x_627_, 2);
v___x_643_ = lean_array_set(v_x_628_, v_x_629_, v_arg_642_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_sub(v_x_629_, v___x_644_);
lean_dec(v_x_629_);
v_x_627_ = v_fn_641_;
v_x_628_ = v___x_643_;
v_x_629_ = v___x_645_;
goto _start;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec(v_x_629_);
v___x_647_ = lean_array_get_size(v_x_628_);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_box(v_a_626_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_x_628_);
v___x_651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v___x_647_, v___x_648_, v___x_650_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_666_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_666_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_666_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; uint8_t v___x_657_; 
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
v___x_657_ = lean_unbox(v_fst_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v_a_652_);
lean_dec_ref(v_x_627_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_e_625_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_e_625_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
lean_object* v_snd_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
lean_dec_ref(v_e_625_);
v_snd_661_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_661_);
lean_dec(v_a_652_);
v___x_662_ = l_Lean_mkAppN(v_x_627_, v_snd_661_);
lean_dec(v_snd_661_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_662_);
v___x_664_ = v___x_654_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_x_627_);
lean_dec_ref(v_e_625_);
v_a_667_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_651_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_651_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3___boxed(lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v_a_74770__boxed_691_; lean_object* v_res_692_; 
v_a_74770__boxed_691_ = lean_unbox(v_a_676_);
v_res_692_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__3(v_e_675_, v_a_74770__boxed_691_, v_x_677_, v_x_678_, v_x_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec(v___y_680_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg___boxed(lean_object* v_upperBound_693_, lean_object* v_a_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_693_, v_a_694_, v_b_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec(v___y_696_);
lean_dec(v_upperBound_693_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess___boxed(lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_e_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec(v_a_709_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___boxed(lean_object* v_e_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec(v_a_722_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6(lean_object* v_e_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___redArg(v_e_734_, v___y_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6___boxed(lean_object* v_e_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess_spec__6(v_e_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec(v___y_748_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0(lean_object* v_00_u03b2_760_, lean_object* v_m_761_, lean_object* v_a_762_, lean_object* v_b_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0___redArg(v_m_761_, v_a_762_, v_b_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(lean_object* v_00_u03b2_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___redArg(v_m_766_, v_a_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1___boxed(lean_object* v_00_u03b2_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1(v_00_u03b2_769_, v_m_770_, v_a_771_);
lean_dec_ref(v_a_771_);
lean_dec_ref(v_m_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(lean_object* v_upperBound_773_, lean_object* v___x_774_, lean_object* v_inst_775_, lean_object* v_R_776_, lean_object* v_a_777_, lean_object* v_b_778_, lean_object* v_c_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___redArg(v_upperBound_773_, v_a_777_, v_b_778_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_792_ = _args[0];
lean_object* v___x_793_ = _args[1];
lean_object* v_inst_794_ = _args[2];
lean_object* v_R_795_ = _args[3];
lean_object* v_a_796_ = _args[4];
lean_object* v_b_797_ = _args[5];
lean_object* v_c_798_ = _args[6];
lean_object* v___y_799_ = _args[7];
lean_object* v___y_800_ = _args[8];
lean_object* v___y_801_ = _args[9];
lean_object* v___y_802_ = _args[10];
lean_object* v___y_803_ = _args[11];
lean_object* v___y_804_ = _args[12];
lean_object* v___y_805_ = _args[13];
lean_object* v___y_806_ = _args[14];
lean_object* v___y_807_ = _args[15];
lean_object* v___y_808_ = _args[16];
lean_object* v___y_809_ = _args[17];
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__2(v_upperBound_792_, v___x_793_, v_inst_794_, v_R_795_, v_a_796_, v_b_797_, v_c_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___x_793_);
lean_dec(v_upperBound_792_);
return v_res_810_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0(lean_object* v_00_u03b2_811_, lean_object* v_a_812_, lean_object* v_x_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___redArg(v_a_812_, v_x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0___boxed(lean_object* v_00_u03b2_815_, lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__0(v_00_u03b2_815_, v_a_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec_ref(v_a_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1(lean_object* v_00_u03b2_820_, lean_object* v_data_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1___redArg(v_data_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2(lean_object* v_00_u03b2_823_, lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v_x_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__2___redArg(v_a_824_, v_b_825_, v_x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__1_spec__4(v_00_u03b2_832_, v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec_ref(v_a_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_836_, lean_object* v_i_837_, lean_object* v_source_838_, lean_object* v_target_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5___redArg(v_i_837_, v_source_838_, v_target_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9(lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit_spec__0_spec__1_spec__5_spec__9___redArg(v_x_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(lean_object* v_category_845_, lean_object* v_opts_846_, lean_object* v_act_847_, lean_object* v_decl_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc_ref(v___y_854_);
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_849_);
v___x_859_ = lean_apply_9(v_act_847_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
v___x_860_ = l_Lean_profileitIOUnsafe___redArg(v_category_845_, v_opts_846_, v___x_859_, v_decl_848_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg___boxed(lean_object* v_category_861_, lean_object* v_opts_862_, lean_object* v_act_863_, lean_object* v_decl_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v_category_861_, v_opts_862_, v_act_863_, v_decl_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v_opts_862_);
lean_dec_ref(v_category_861_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(lean_object* v_00_u03b1_876_, lean_object* v_category_877_, lean_object* v_opts_878_, lean_object* v_act_879_, lean_object* v_decl_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v_category_877_, v_opts_878_, v_act_879_, v_decl_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___boxed(lean_object* v_00_u03b1_892_, lean_object* v_category_893_, lean_object* v_opts_894_, lean_object* v_act_895_, lean_object* v_decl_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0(v_00_u03b1_892_, v_category_893_, v_opts_894_, v_act_895_, v_decl_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v_opts_894_);
lean_dec_ref(v_category_893_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(lean_object* v___x_908_, lean_object* v_e_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_st_mk_ref(v___x_908_);
v___x_921_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit(v_e_909_, v___x_920_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_st_ref_get(v___x_920_);
lean_dec(v___x_920_);
lean_dec(v___x_926_);
if (v_isShared_925_ == 0)
{
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_922_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_dec(v___x_920_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed(lean_object* v___x_931_, lean_object* v_e_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_Grind_markNestedSubsingletons___lam__0(v___x_931_, v_e_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_box(0);
v___x_946_ = lean_unsigned_to_nat(16u);
v___x_947_ = lean_mk_array(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__1, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__1_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__1);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons(lean_object* v_e_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_options_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___f_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_options_962_ = lean_ctor_get(v_a_959_, 2);
v___x_963_ = ((lean_object*)(l_Lean_Meta_Grind_markNestedSubsingletons___closed__0));
v___x_964_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__2, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2);
v___f_965_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_markNestedSubsingletons___lam__0___boxed), 12, 2);
lean_closure_set(v___f_965_, 0, v___x_964_);
lean_closure_set(v___f_965_, 1, v_e_951_);
v___x_966_ = lean_box(0);
v___x_967_ = l_Lean_profileitM___at___00Lean_Meta_Grind_markNestedSubsingletons_spec__0___redArg(v___x_963_, v_options_962_, v___f_965_, v___x_966_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markNestedSubsingletons___boxed(lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_Grind_markNestedSubsingletons(v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc_ref(v_e_980_);
v___x_992_ = lean_infer_type(v_e_980_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_preprocess(v_a_993_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1004_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6, &l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedSubsingletons_visit___closed__6);
v___x_1000_ = l_Lean_mkAppB(v___x_999_, v_a_995_, v_e_980_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
else
{
lean_dec_ref(v_e_980_);
return v___x_994_;
}
}
else
{
lean_dec_ref(v_e_980_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof___boxed(lean_object* v_e_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec(v_a_1006_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Grind_isMarkedSubsingletonConst___closed__3));
v___x_1030_ = l_Lean_Expr_isAppOf(v_e_1018_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_obj_once(&l_Lean_Meta_Grind_markNestedSubsingletons___closed__2, &l_Lean_Meta_Grind_markNestedSubsingletons___closed__2_once, _init_l_Lean_Meta_Grind_markNestedSubsingletons___closed__2);
v___x_1032_ = lean_st_mk_ref(v___x_1031_);
v___x_1033_ = l___private_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons_0__Lean_Meta_Grind_markNestedProof(v_e_1018_, v___x_1032_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_st_ref_get(v___x_1032_);
lean_dec(v___x_1032_);
lean_dec(v___x_1038_);
if (v_isShared_1037_ == 0)
{
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
else
{
lean_dec(v___x_1032_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_e_1018_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markProof___boxed(lean_object* v_e_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Grind_markProof(v_e_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1055_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
}
#ifdef __cplusplus
}
#endif
