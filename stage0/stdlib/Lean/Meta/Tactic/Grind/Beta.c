// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Beta
// Imports: public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Grind_getEqcLambdas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Meta.Tactic.Grind.Types"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Grind.foldEqc"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_getEqcLambdas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getEqcLambdas___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_getEqcLambdas___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getEqcLambdas___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 31, 7, 123, 15, 248, 150, 29)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", using "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(lean_object* v_msg_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toApplicative_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_87_; 
v___x_18_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0, &l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0);
v___x_19_ = l_StateRefT_x27_instMonad___redArg(v___x_18_);
v_toApplicative_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_19_, 1);
lean_dec(v_unused_88_);
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_87_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toApplicative_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_87_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_toFunctor_24_; lean_object* v_toSeq_25_; lean_object* v_toSeqLeft_26_; lean_object* v_toSeqRight_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_85_; 
v_toFunctor_24_ = lean_ctor_get(v_toApplicative_20_, 0);
v_toSeq_25_ = lean_ctor_get(v_toApplicative_20_, 2);
v_toSeqLeft_26_ = lean_ctor_get(v_toApplicative_20_, 3);
v_toSeqRight_27_ = lean_ctor_get(v_toApplicative_20_, 4);
v_isSharedCheck_85_ = !lean_is_exclusive(v_toApplicative_20_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_dec(v_unused_86_);
v___x_29_ = v_toApplicative_20_;
v_isShared_30_ = v_isSharedCheck_85_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_toSeqRight_27_);
lean_inc(v_toSeqLeft_26_);
lean_inc(v_toSeq_25_);
lean_inc(v_toFunctor_24_);
lean_dec(v_toApplicative_20_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_85_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_40_; 
v___f_31_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__1));
v___f_32_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__2));
lean_inc_ref(v_toFunctor_24_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_33_, 0, v_toFunctor_24_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_34_, 0, v_toFunctor_24_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___f_33_);
lean_ctor_set(v___x_35_, 1, v___f_34_);
v___f_36_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_36_, 0, v_toSeqRight_27_);
v___f_37_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_37_, 0, v_toSeqLeft_26_);
v___f_38_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_38_, 0, v_toSeq_25_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___f_36_);
lean_ctor_set(v___x_29_, 3, v___f_37_);
lean_ctor_set(v___x_29_, 2, v___f_38_);
lean_ctor_set(v___x_29_, 1, v___f_31_);
lean_ctor_set(v___x_29_, 0, v___x_35_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v___f_31_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v___f_38_);
lean_ctor_set(v_reuseFailAlloc_84_, 3, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_84_, 4, v___f_36_);
v___x_40_ = v_reuseFailAlloc_84_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___f_32_);
lean_ctor_set(v___x_22_, 0, v___x_40_);
v___x_42_ = v___x_22_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___f_32_);
v___x_42_ = v_reuseFailAlloc_83_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_81_; 
v___x_43_ = l_StateRefT_x27_instMonad___redArg(v___x_42_);
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_81_ == 0)
{
lean_object* v_unused_82_; 
v_unused_82_ = lean_ctor_get(v___x_43_, 1);
lean_dec(v_unused_82_);
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_81_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toApplicative_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_81_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toFunctor_48_; lean_object* v_toSeq_49_; lean_object* v_toSeqLeft_50_; lean_object* v_toSeqRight_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_79_; 
v_toFunctor_48_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toSeq_49_ = lean_ctor_get(v_toApplicative_44_, 2);
v_toSeqLeft_50_ = lean_ctor_get(v_toApplicative_44_, 3);
v_toSeqRight_51_ = lean_ctor_get(v_toApplicative_44_, 4);
v_isSharedCheck_79_ = !lean_is_exclusive(v_toApplicative_44_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_dec(v_unused_80_);
v___x_53_ = v_toApplicative_44_;
v_isShared_54_ = v_isSharedCheck_79_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_toSeqRight_51_);
lean_inc(v_toSeqLeft_50_);
lean_inc(v_toSeq_49_);
lean_inc(v_toFunctor_48_);
lean_dec(v_toApplicative_44_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_79_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_64_; 
v___f_55_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__3));
v___f_56_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__4));
lean_inc_ref(v_toFunctor_48_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_57_, 0, v_toFunctor_48_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_48_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___f_57_);
lean_ctor_set(v___x_59_, 1, v___f_58_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeqRight_51_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqLeft_50_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeq_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___f_60_);
lean_ctor_set(v___x_53_, 3, v___f_61_);
lean_ctor_set(v___x_53_, 2, v___f_62_);
lean_ctor_set(v___x_53_, 1, v___f_55_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_78_, 2, v___f_62_);
lean_ctor_set(v_reuseFailAlloc_78_, 3, v___f_61_);
lean_ctor_set(v_reuseFailAlloc_78_, 4, v___f_60_);
v___x_64_ = v_reuseFailAlloc_78_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___f_56_);
lean_ctor_set(v___x_46_, 0, v___x_64_);
v___x_66_ = v___x_46_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___f_56_);
v___x_66_ = v_reuseFailAlloc_77_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_2194__overap_75_; lean_object* v___x_76_; 
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_66_);
v___x_68_ = l_ReaderT_instMonad___redArg(v___x_67_);
v___x_69_ = l_StateRefT_x27_instMonad___redArg(v___x_68_);
v___x_70_ = l_ReaderT_instMonad___redArg(v___x_69_);
v___x_71_ = l_ReaderT_instMonad___redArg(v___x_70_);
v___x_72_ = l_StateRefT_x27_instMonad___redArg(v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = l_instInhabitedOfMonad___redArg(v___x_72_, v___x_73_);
v___x_2194__overap_75_ = lean_panic_fn_borrowed(v___x_74_, v_msg_6_);
lean_dec(v___x_74_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc(v___y_12_);
lean_inc_ref(v___y_11_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc(v___y_7_);
v___x_76_ = lean_apply_11(v___x_2194__overap_75_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
return v___x_76_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec(v___y_90_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object* v___x_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_160_; 
v___x_110_ = lean_st_ref_get(v___y_104_);
v_snd_111_ = lean_ctor_get(v_b_103_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_b_103_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v_b_103_, 0);
lean_dec(v_unused_161_);
v___x_113_ = v_b_103_;
v_isShared_114_ = v_isSharedCheck_160_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_dec(v_b_103_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_160_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_159_; 
v_fst_115_ = lean_ctor_get(v_snd_111_, 0);
v_snd_116_ = lean_ctor_get(v_snd_111_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_snd_111_);
if (v_isSharedCheck_159_ == 0)
{
v___x_118_ = v_snd_111_;
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_snd_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_159_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; 
lean_inc(v_fst_115_);
v___x_120_ = l_Lean_Meta_Grind_Goal_getENode(v___x_110_, v_fst_115_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___x_110_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_150_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_150_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_150_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_self_125_; lean_object* v_next_126_; lean_object* v___x_127_; lean_object* v_a_129_; uint8_t v___x_148_; 
v_self_125_ = lean_ctor_get(v_a_121_, 0);
lean_inc_ref(v_self_125_);
v_next_126_ = lean_ctor_get(v_a_121_, 1);
lean_inc_ref(v_next_126_);
lean_dec(v_a_121_);
v___x_127_ = lean_box(0);
v___x_148_ = l_Lean_Expr_isLambda(v_self_125_);
if (v___x_148_ == 0)
{
lean_dec_ref(v_self_125_);
v_a_129_ = v_snd_116_;
goto v___jp_128_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_array_push(v_snd_116_, v_self_125_);
v_a_129_ = v___x_149_;
goto v___jp_128_;
}
v___jp_128_:
{
uint8_t v___x_130_; 
v___x_130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_126_, v___x_102_);
if (v___x_130_ == 0)
{
lean_object* v___x_132_; 
lean_del_object(v___x_123_);
lean_dec(v_fst_115_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_129_);
lean_ctor_set(v___x_118_, 0, v_next_126_);
v___x_132_ = v___x_118_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_next_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_129_);
v___x_132_ = v_reuseFailAlloc_137_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_134_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_132_);
lean_ctor_set(v___x_113_, 0, v___x_127_);
v___x_134_ = v___x_113_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_136_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v_b_103_ = v___x_134_;
goto _start;
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec_ref(v_next_126_);
lean_inc_ref(v_a_129_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_a_129_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_129_);
v___x_140_ = v___x_118_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_a_129_);
v___x_140_ = v_reuseFailAlloc_147_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_140_);
lean_ctor_set(v___x_113_, 0, v___x_138_);
v___x_142_ = v___x_113_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_142_);
v___x_144_ = v___x_123_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
v_a_151_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_120_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_120_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object* v___x_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_162_, v_b_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___x_162_);
return v_res_170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_176_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__3));
v___x_177_ = lean_unsigned_to_nat(2u);
v___x_178_ = lean_unsigned_to_nat(1585u);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__2));
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__1));
v___x_181_ = l_mkPanicMessageWithDecl(v___x_180_, v___x_179_, v___x_178_, v___x_177_, v___x_176_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object* v_root_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
uint8_t v_hasLambdas_194_; 
v_hasLambdas_194_ = lean_ctor_get_uint8(v_root_182_, sizeof(void*)*12 + 3);
if (v_hasLambdas_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
else
{
lean_object* v_self_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_self_197_ = lean_ctor_get(v_root_182_, 0);
v___x_198_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_199_ = lean_box(0);
lean_inc_ref(v_self_197_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_self_197_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v_self_197_, v___x_201_, v_a_183_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_232_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_232_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_232_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_fst_207_; 
v_fst_207_ = lean_ctor_get(v_a_203_, 0);
if (lean_obj_tag(v_fst_207_) == 0)
{
lean_object* v_snd_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_del_object(v___x_205_);
v_snd_208_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_snd_208_);
lean_dec(v_a_203_);
v___x_209_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_210_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_209_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_218_; 
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v___x_210_, 0);
lean_dec(v_unused_219_);
v___x_212_ = v___x_210_;
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
else
{
lean_dec(v___x_210_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_218_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_snd_214_; lean_object* v___x_216_; 
v_snd_214_ = lean_ctor_get(v_snd_208_, 1);
lean_inc(v_snd_214_);
lean_dec(v_snd_208_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v_snd_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_snd_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_snd_208_);
v_a_220_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_210_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_210_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_val_228_; lean_object* v___x_230_; 
lean_inc_ref(v_fst_207_);
lean_dec(v_a_203_);
v_val_228_ = lean_ctor_get(v_fst_207_, 0);
lean_inc(v_val_228_);
lean_dec_ref(v_fst_207_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_val_228_);
v___x_230_ = v___x_205_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_val_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_233_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_202_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_202_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object* v_root_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Grind_getEqcLambdas(v_root_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_root_241_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object* v___x_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_254_, v_b_255_, v___y_256_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object* v___x_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(v___x_268_, v_b_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___x_268_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object* v___y_285_, lean_object* v_as_286_, size_t v_sz_287_, size_t v_i_288_, lean_object* v_b_289_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = lean_usize_dec_lt(v_i_288_, v_sz_287_);
if (v___x_290_ == 0)
{
lean_inc_ref(v_b_289_);
return v_b_289_;
}
else
{
lean_object* v___x_291_; lean_object* v_a_292_; uint8_t v___x_293_; 
v___x_291_ = lean_box(0);
v_a_292_ = lean_array_uget_borrowed(v_as_286_, v_i_288_);
v___x_293_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_292_, v___y_285_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; size_t v___x_295_; size_t v___x_296_; 
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0));
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_add(v_i_288_, v___x_295_);
v_i_288_ = v___x_296_;
v_b_289_ = v___x_294_;
goto _start;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_inc(v_a_292_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_a_292_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_291_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object* v___y_301_, lean_object* v_as_302_, lean_object* v_sz_303_, lean_object* v_i_304_, lean_object* v_b_305_){
_start:
{
size_t v_sz_boxed_306_; size_t v_i_boxed_307_; lean_object* v_res_308_; 
v_sz_boxed_306_ = lean_unbox_usize(v_sz_303_);
lean_dec(v_sz_303_);
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_301_, v_as_302_, v_sz_boxed_306_, v_i_boxed_307_, v_b_305_);
lean_dec_ref(v_b_305_);
lean_dec_ref(v_as_302_);
lean_dec_ref(v___y_301_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object* v_e_312_, lean_object* v_b_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_snd_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_383_; 
v___x_320_ = lean_st_ref_get(v___y_314_);
v_snd_321_ = lean_ctor_get(v_b_313_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_b_313_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v_b_313_, 0);
lean_dec(v_unused_384_);
v___x_323_ = v_b_313_;
v_isShared_324_ = v_isSharedCheck_383_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snd_321_);
lean_dec(v_b_313_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_383_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v_fst_325_; lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_382_; 
v_fst_325_ = lean_ctor_get(v_snd_321_, 0);
v_snd_326_ = lean_ctor_get(v_snd_321_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_snd_321_);
if (v_isSharedCheck_382_ == 0)
{
v___x_328_ = v_snd_321_;
v_isShared_329_ = v_isSharedCheck_382_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_inc(v_fst_325_);
lean_dec(v_snd_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_382_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; 
lean_inc(v_fst_325_);
v___x_330_ = l_Lean_Meta_Grind_Goal_getENode(v___x_320_, v_fst_325_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___x_320_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_373_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_373_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_373_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_373_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_self_336_; lean_object* v_next_337_; lean_object* v___x_338_; lean_object* v_a_340_; lean_object* v___y_360_; lean_object* v___y_363_; lean_object* v_fn_370_; lean_object* v___x_371_; 
v___x_335_ = lean_st_ref_get(v___y_314_);
v_self_336_ = lean_ctor_get(v_a_331_, 0);
lean_inc_ref(v_self_336_);
v_next_337_ = lean_ctor_get(v_a_331_, 1);
lean_inc_ref(v_next_337_);
lean_dec(v_a_331_);
v___x_338_ = lean_box(0);
v_fn_370_ = l_Lean_Expr_getAppFn(v_self_336_);
lean_dec_ref(v_self_336_);
v___x_371_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_335_, v_fn_370_);
lean_dec(v___x_335_);
if (lean_obj_tag(v___x_371_) == 0)
{
v___y_363_ = v_fn_370_;
goto v___jp_362_;
}
else
{
lean_object* v_val_372_; 
lean_dec_ref(v_fn_370_);
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref(v___x_371_);
v___y_363_ = v_val_372_;
goto v___jp_362_;
}
v___jp_339_:
{
uint8_t v___x_341_; 
v___x_341_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_337_, v_e_312_);
if (v___x_341_ == 0)
{
lean_object* v___x_343_; 
lean_del_object(v___x_333_);
lean_dec(v_fst_325_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_a_340_);
lean_ctor_set(v___x_328_, 0, v_next_337_);
v___x_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_next_337_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_a_340_);
v___x_343_ = v_reuseFailAlloc_348_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_343_);
lean_ctor_set(v___x_323_, 0, v___x_338_);
v___x_345_ = v___x_323_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_343_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
v_b_313_ = v___x_345_;
goto _start;
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_351_; 
lean_dec_ref(v_next_337_);
lean_inc_ref(v_a_340_);
v___x_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_349_, 0, v_a_340_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_a_340_);
v___x_351_ = v___x_328_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_fst_325_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_340_);
v___x_351_ = v_reuseFailAlloc_358_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_351_);
lean_ctor_set(v___x_323_, 0, v___x_349_);
v___x_353_ = v___x_323_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_353_);
v___x_355_ = v___x_333_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
v___jp_359_:
{
lean_object* v___x_361_; 
v___x_361_ = lean_array_push(v_snd_326_, v___y_360_);
v_a_340_ = v___x_361_;
goto v___jp_339_;
}
v___jp_362_:
{
lean_object* v___x_364_; size_t v_sz_365_; size_t v___x_366_; lean_object* v___x_367_; lean_object* v_fst_368_; 
v___x_364_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0));
v_sz_365_ = lean_array_size(v_snd_326_);
v___x_366_ = ((size_t)0ULL);
v___x_367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_363_, v_snd_326_, v_sz_365_, v___x_366_, v___x_364_);
v_fst_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_368_);
lean_dec_ref(v___x_367_);
if (lean_obj_tag(v_fst_368_) == 0)
{
v___y_360_ = v___y_363_;
goto v___jp_359_;
}
else
{
lean_object* v_val_369_; 
v_val_369_ = lean_ctor_get(v_fst_368_, 0);
lean_inc(v_val_369_);
lean_dec_ref(v_fst_368_);
if (lean_obj_tag(v_val_369_) == 0)
{
v___y_360_ = v___y_363_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v_val_369_);
lean_dec_ref(v___y_363_);
v_a_340_ = v_snd_326_;
goto v___jp_339_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_del_object(v___x_328_);
lean_dec(v_snd_326_);
lean_dec(v_fst_325_);
lean_del_object(v___x_323_);
v_a_374_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_330_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_330_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object* v_e_385_, lean_object* v_b_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_385_, v_b_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v_e_385_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object* v_e_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_407_ = lean_box(0);
lean_inc_ref(v_e_394_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_e_394_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_394_, v___x_409_, v_a_395_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec_ref(v_e_394_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_440_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_440_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_440_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_fst_415_; 
v_fst_415_ = lean_ctor_get(v_a_411_, 0);
if (lean_obj_tag(v_fst_415_) == 0)
{
lean_object* v_snd_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_del_object(v___x_413_);
v_snd_416_ = lean_ctor_get(v_a_411_, 1);
lean_inc(v_snd_416_);
lean_dec(v_a_411_);
v___x_417_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_418_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_417_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_427_);
v___x_420_ = v___x_418_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_dec(v___x_418_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_snd_422_; lean_object* v___x_424_; 
v_snd_422_ = lean_ctor_get(v_snd_416_, 1);
lean_inc(v_snd_422_);
lean_dec(v_snd_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_snd_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_snd_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_snd_416_);
v_a_428_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_object* v_val_436_; lean_object* v___x_438_; 
lean_inc_ref(v_fst_415_);
lean_dec(v_a_411_);
v_val_436_ = lean_ctor_get(v_fst_415_, 0);
lean_inc(v_val_436_);
lean_dec_ref(v_fst_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_val_436_);
v___x_438_ = v___x_413_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_val_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_410_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_410_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object* v_e_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_getFnRoots(v_e_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec(v_a_450_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object* v_e_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_462_, v_b_463_, v___y_464_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object* v_e_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_getFnRoots_spec__1(v_e_476_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v_e_476_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_, lean_object* v_b_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_a_497_; lean_object* v___y_502_; uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
v___x_506_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_505_, v___y_494_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; uint8_t v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
v___x_508_ = lean_nat_dec_le(v_b_493_, v_a_507_);
lean_dec(v_a_507_);
if (v___x_508_ == 0)
{
lean_dec_ref(v___x_506_);
v_a_497_ = v_b_493_;
goto v___jp_496_;
}
else
{
lean_dec(v_b_493_);
v___y_502_ = v___x_506_;
goto v___jp_501_;
}
}
else
{
lean_dec(v_b_493_);
v___y_502_ = v___x_506_;
goto v___jp_501_;
}
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_b_493_);
return v___x_509_;
}
v___jp_496_:
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_491_, v___x_498_);
v_i_491_ = v___x_499_;
v_b_493_ = v_a_497_;
goto _start;
}
v___jp_501_:
{
if (lean_obj_tag(v___y_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___y_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___y_502_);
v_a_497_ = v_a_503_;
goto v___jp_496_;
}
else
{
return v___y_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object* v_as_510_, lean_object* v_i_511_, lean_object* v_stop_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_512_);
lean_dec(v_stop_512_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_510_, v_i_boxed_516_, v_stop_boxed_517_, v_b_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v_as_510_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(lean_object* v_msgData_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v_mctx_528_; lean_object* v_lctx_529_; lean_object* v_options_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_525_ = lean_st_ref_get(v___y_523_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = lean_st_ref_get(v___y_521_);
v_mctx_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_mctx_528_);
lean_dec(v___x_527_);
v_lctx_529_ = lean_ctor_get(v___y_520_, 2);
v_options_530_ = lean_ctor_get(v___y_522_, 2);
lean_inc_ref(v_options_530_);
lean_inc_ref(v_lctx_529_);
v___x_531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_531_, 0, v_env_526_);
lean_ctor_set(v___x_531_, 1, v_mctx_528_);
lean_ctor_set(v___x_531_, 2, v_lctx_529_);
lean_ctor_set(v___x_531_, 3, v_options_530_);
v___x_532_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_msgData_519_);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(lean_object* v_msgData_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_541_; double v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_float_of_nat(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object* v_cls_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_ref_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_599_; 
v_ref_553_ = lean_ctor_get(v___y_550_, 5);
v___x_554_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_599_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_599_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_599_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v_traceState_560_; lean_object* v_env_561_; lean_object* v_nextMacroScope_562_; lean_object* v_ngen_563_; lean_object* v_auxDeclNGen_564_; lean_object* v_cache_565_; lean_object* v_messages_566_; lean_object* v_infoState_567_; lean_object* v_snapshotTasks_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_598_; 
v___x_559_ = lean_st_ref_take(v___y_551_);
v_traceState_560_ = lean_ctor_get(v___x_559_, 4);
v_env_561_ = lean_ctor_get(v___x_559_, 0);
v_nextMacroScope_562_ = lean_ctor_get(v___x_559_, 1);
v_ngen_563_ = lean_ctor_get(v___x_559_, 2);
v_auxDeclNGen_564_ = lean_ctor_get(v___x_559_, 3);
v_cache_565_ = lean_ctor_get(v___x_559_, 5);
v_messages_566_ = lean_ctor_get(v___x_559_, 6);
v_infoState_567_ = lean_ctor_get(v___x_559_, 7);
v_snapshotTasks_568_ = lean_ctor_get(v___x_559_, 8);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_598_ == 0)
{
v___x_570_ = v___x_559_;
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snapshotTasks_568_);
lean_inc(v_infoState_567_);
lean_inc(v_messages_566_);
lean_inc(v_cache_565_);
lean_inc(v_traceState_560_);
lean_inc(v_auxDeclNGen_564_);
lean_inc(v_ngen_563_);
lean_inc(v_nextMacroScope_562_);
lean_inc(v_env_561_);
lean_dec(v___x_559_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_598_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint64_t v_tid_572_; lean_object* v_traces_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_597_; 
v_tid_572_ = lean_ctor_get_uint64(v_traceState_560_, sizeof(void*)*1);
v_traces_573_ = lean_ctor_get(v_traceState_560_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_traceState_560_);
if (v_isSharedCheck_597_ == 0)
{
v___x_575_ = v_traceState_560_;
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_traces_573_);
lean_dec(v_traceState_560_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_597_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; double v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0);
v___x_579_ = 0;
v___x_580_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1));
v___x_581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_581_, 0, v_cls_546_);
lean_ctor_set(v___x_581_, 1, v___x_577_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3, v___x_578_);
lean_ctor_set_float(v___x_581_, sizeof(void*)*3 + 8, v___x_578_);
lean_ctor_set_uint8(v___x_581_, sizeof(void*)*3 + 16, v___x_579_);
v___x_582_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2));
v___x_583_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v_a_555_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_inc(v_ref_553_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_ref_553_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_PersistentArray_push___redArg(v_traces_573_, v___x_584_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_585_);
v___x_587_ = v___x_575_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_585_);
lean_ctor_set_uint64(v_reuseFailAlloc_596_, sizeof(void*)*1, v_tid_572_);
v___x_587_ = v_reuseFailAlloc_596_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_589_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___x_587_);
v___x_589_ = v___x_570_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_env_561_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_nextMacroScope_562_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_ngen_563_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_auxDeclNGen_564_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_cache_565_);
lean_ctor_set(v_reuseFailAlloc_595_, 6, v_messages_566_);
lean_ctor_set(v_reuseFailAlloc_595_, 7, v_infoState_567_);
lean_ctor_set(v_reuseFailAlloc_595_, 8, v_snapshotTasks_568_);
v___x_589_ = v_reuseFailAlloc_595_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_590_ = lean_st_ref_set(v___y_551_, v___x_589_);
v___x_591_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_591_);
v___x_593_ = v___x_557_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object* v_cls_600_, lean_object* v_msg_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_600_, v_msg_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object* v_as_608_, size_t v_sz_609_, size_t v_i_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_611_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; 
v_a_619_ = lean_array_uget_borrowed(v_as_608_, v_i_610_);
lean_inc(v_a_619_);
v___x_620_ = l_Lean_Meta_mkCongrFun(v_b_611_, v_a_619_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; size_t v___x_622_; size_t v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref(v___x_620_);
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_610_, v___x_622_);
v_i_610_ = v___x_623_;
v_b_611_ = v_a_621_;
goto _start;
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
size_t v_sz_boxed_634_; size_t v_i_boxed_635_; lean_object* v_res_636_; 
v_sz_boxed_634_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_635_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_625_, v_sz_boxed_634_, v_i_boxed_635_, v_b_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_as_625_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5));
v___x_650_ = l_Lean_Name_append(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object* v_args_659_, lean_object* v_f_660_, lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_a_677_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_b_664_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___x_710_; lean_object* v_a_712_; lean_object* v___y_809_; uint8_t v___x_819_; 
lean_dec_ref(v_b_664_);
v___x_683_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_a_684_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
lean_inc_ref(v_args_659_);
lean_inc(v_a_684_);
v___x_710_ = l_Lean_Expr_beta(v_a_684_, v_args_659_);
v___x_819_ = l_Lean_Expr_isLambda(v___x_710_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_684_, v___y_665_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
v___x_822_ = l_Lean_Meta_Grind_getGeneration___redArg(v_f_660_, v___y_665_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___y_825_; uint8_t v___x_836_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_822_);
v___x_836_ = lean_nat_dec_le(v_a_821_, v_a_823_);
if (v___x_836_ == 0)
{
lean_dec(v_a_823_);
v___y_825_ = v_a_821_;
goto v___jp_824_;
}
else
{
lean_dec(v_a_821_);
v___y_825_ = v_a_823_;
goto v___jp_824_;
}
v___jp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_array_get_size(v_args_659_);
v___x_828_ = lean_nat_dec_lt(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
v_a_712_ = v___y_825_;
goto v___jp_711_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = lean_nat_dec_le(v___x_827_, v___x_827_);
if (v___x_829_ == 0)
{
if (v___x_828_ == 0)
{
v_a_712_ = v___y_825_;
goto v___jp_711_;
}
else
{
size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_of_nat(v___x_827_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_659_, v___x_830_, v___x_831_, v___y_825_, v___y_665_);
v___y_809_ = v___x_832_;
goto v___jp_808_;
}
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_827_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_659_, v___x_833_, v___x_834_, v___y_825_, v___y_665_);
v___y_809_ = v___x_835_;
goto v___jp_808_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec(v_a_821_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_837_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_822_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_822_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_845_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_820_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_820_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_dec_ref(v___x_710_);
v_a_677_ = v___x_683_;
goto v___jp_676_;
}
v___jp_685_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_inc(v_a_684_);
v___x_699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_699_, 0, v_a_684_);
v___x_700_ = lean_box(1);
v___x_701_ = l_Lean_Meta_Grind_addNewRawFact(v___y_686_, v___y_687_, v___y_688_, v___x_699_, v___x_700_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_dec_ref(v___x_701_);
v_a_677_ = v___x_683_;
goto v___jp_676_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
v___jp_711_:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_667_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_799_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_799_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_799_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_799_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_a_712_, v___x_718_);
lean_dec(v_a_712_);
v___x_720_ = lean_nat_dec_le(v_a_714_, v___x_719_);
lean_dec(v_a_714_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_del_object(v___x_716_);
lean_inc_ref_n(v_f_660_, 2);
v___x_721_ = l_Lean_mkAppN(v_f_660_, v_args_659_);
lean_inc(v_a_684_);
v___x_722_ = l_Lean_Meta_Grind_hasSameType(v_f_660_, v_a_684_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; uint8_t v___x_724_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_722_);
v___x_724_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v___x_721_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_710_);
v_a_677_ = v___x_683_;
goto v___jp_676_;
}
else
{
lean_object* v___x_725_; 
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc(v___y_670_);
lean_inc_ref(v___y_669_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc(v___y_665_);
lean_inc(v_a_684_);
lean_inc_ref(v_f_660_);
v___x_725_ = lean_grind_mk_eq_proof(v_f_660_, v_a_684_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; size_t v_sz_727_; size_t v___x_728_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref(v___x_725_);
v_sz_727_ = lean_array_size(v_args_659_);
v___x_728_ = ((size_t)0ULL);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_659_, v_sz_727_, v___x_728_, v_a_726_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_729_);
v___x_731_ = l_Lean_Meta_mkEq(v___x_721_, v___x_710_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_options_732_; uint8_t v_hasTrace_733_; 
v_options_732_ = lean_ctor_get(v___y_673_, 2);
v_hasTrace_733_ = lean_ctor_get_uint8(v_options_732_, sizeof(void*)*1);
if (v_hasTrace_733_ == 0)
{
lean_object* v_a_734_; 
v_a_734_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_734_);
lean_dec_ref(v___x_731_);
v___y_686_ = v_a_730_;
v___y_687_ = v_a_734_;
v___y_688_ = v___x_719_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
v___y_694_ = v___y_670_;
v___y_695_ = v___y_671_;
v___y_696_ = v___y_672_;
v___y_697_ = v___y_673_;
v___y_698_ = v___y_674_;
goto v___jp_685_;
}
else
{
lean_object* v_a_735_; lean_object* v_inheritedTraceOptions_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_a_735_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_735_);
lean_dec_ref(v___x_731_);
v_inheritedTraceOptions_736_ = lean_ctor_get(v___y_673_, 13);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_738_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6);
v___x_739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_736_, v_options_732_, v___x_738_);
if (v___x_739_ == 0)
{
v___y_686_ = v_a_730_;
v___y_687_ = v_a_735_;
v___y_688_ = v___x_719_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
v___y_694_ = v___y_670_;
v___y_695_ = v___y_671_;
v___y_696_ = v___y_672_;
v___y_697_ = v___y_673_;
v___y_698_ = v___y_674_;
goto v___jp_685_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Grind_updateLastTag(v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v___x_740_);
lean_inc(v_a_735_);
v___x_741_ = l_Lean_MessageData_ofExpr(v_a_735_);
v___x_742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_inc(v_a_684_);
v___x_744_ = l_Lean_MessageData_ofExpr(v_a_684_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_737_, v___x_745_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref(v___x_746_);
v___y_686_ = v_a_730_;
v___y_687_ = v_a_735_;
v___y_688_ = v___x_719_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
v___y_694_ = v___y_670_;
v___y_695_ = v___y_671_;
v___y_696_ = v___y_672_;
v___y_697_ = v___y_673_;
v___y_698_ = v___y_674_;
goto v___jp_685_;
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_735_);
lean_dec(v_a_730_);
lean_dec(v___x_719_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_735_);
lean_dec(v_a_730_);
lean_dec(v___x_719_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_755_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_740_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_740_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
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
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_a_730_);
lean_dec(v___x_719_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_763_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_731_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_731_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___x_721_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_771_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_729_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_729_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___x_721_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_779_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_725_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_725_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v___x_721_);
lean_dec(v___x_719_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_787_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_722_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_722_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
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
else
{
lean_object* v___x_795_; lean_object* v___x_797_; 
lean_dec(v___x_719_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10));
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_795_);
v___x_797_ = v___x_716_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_a_712_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_800_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_713_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_713_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
v___jp_808_:
{
if (lean_obj_tag(v___y_809_) == 0)
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___y_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___y_809_);
v_a_712_ = v_a_810_;
goto v___jp_711_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v_f_660_);
lean_dec_ref(v_args_659_);
v_a_811_ = lean_ctor_get(v___y_809_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___y_809_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___y_809_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___y_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
v___jp_676_:
{
size_t v___x_678_; size_t v___x_679_; 
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_663_, v___x_678_);
lean_inc_ref(v_a_677_);
v_i_663_ = v___x_679_;
v_b_664_ = v_a_677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object** _args){
lean_object* v_args_853_ = _args[0];
lean_object* v_f_854_ = _args[1];
lean_object* v_as_855_ = _args[2];
lean_object* v_sz_856_ = _args[3];
lean_object* v_i_857_ = _args[4];
lean_object* v_b_858_ = _args[5];
lean_object* v___y_859_ = _args[6];
lean_object* v___y_860_ = _args[7];
lean_object* v___y_861_ = _args[8];
lean_object* v___y_862_ = _args[9];
lean_object* v___y_863_ = _args[10];
lean_object* v___y_864_ = _args[11];
lean_object* v___y_865_ = _args[12];
lean_object* v___y_866_ = _args[13];
lean_object* v___y_867_ = _args[14];
lean_object* v___y_868_ = _args[15];
lean_object* v___y_869_ = _args[16];
_start:
{
size_t v_sz_boxed_870_; size_t v_i_boxed_871_; lean_object* v_res_872_; 
v_sz_boxed_870_ = lean_unbox_usize(v_sz_856_);
lean_dec(v_sz_856_);
v_i_boxed_871_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_853_, v_f_854_, v_as_855_, v_sz_boxed_870_, v_i_boxed_871_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v_as_855_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object* v_lams_873_, lean_object* v_f_874_, lean_object* v_args_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_array_get_size(v_args_875_);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_nat_dec_eq(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_890_ = lean_box(0);
v___x_891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_sz_892_ = lean_array_size(v_lams_873_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_875_, v_f_874_, v_lams_873_, v_sz_892_, v___x_893_, v___x_891_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_907_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_907_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_907_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_907_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_fst_899_; 
v_fst_899_ = lean_ctor_get(v_a_895_, 0);
lean_inc(v_fst_899_);
lean_dec(v_a_895_);
if (lean_obj_tag(v_fst_899_) == 0)
{
lean_object* v___x_901_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_890_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_890_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; 
v_val_903_ = lean_ctor_get(v_fst_899_, 0);
lean_inc(v_val_903_);
lean_dec_ref(v_fst_899_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_val_903_);
v___x_905_ = v___x_897_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_val_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_894_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_894_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_args_875_);
lean_dec_ref(v_f_874_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object* v_lams_918_, lean_object* v_f_919_, lean_object* v_args_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_918_, v_f_919_, v_args_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_lams_918_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_933_, v_sz_934_, v_i_935_, v_b_936_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object* v_as_949_, lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_sz_boxed_964_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_965_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_949_, v_sz_boxed_964_, v_i_boxed_965_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v_as_949_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object* v_cls_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_967_, v_msg_968_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object* v_cls_981_, lean_object* v_msg_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_981_, v_msg_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec(v___y_983_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object* v_as_995_, size_t v_i_996_, size_t v_stop_997_, lean_object* v_b_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_995_, v_i_996_, v_stop_997_, v_b_998_, v___y_999_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
size_t v_i_boxed_1026_; size_t v_stop_boxed_1027_; lean_object* v_res_1028_; 
v_i_boxed_1026_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1027_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_as_1011_, v_i_boxed_1026_, v_stop_boxed_1027_, v_b_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v_as_1011_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object* v_f_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_1029_, v_a_1030_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1074_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1074_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1074_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; 
if (lean_obj_tag(v_a_1042_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1073_; 
v_val_1064_ = lean_ctor_get(v_a_1042_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_a_1042_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1066_ = v_a_1042_;
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v_a_1042_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1073_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
uint8_t v_hasLambdas_1068_; 
v_hasLambdas_1068_ = lean_ctor_get_uint8(v_val_1064_, sizeof(void*)*12 + 3);
lean_dec(v_val_1064_);
if (v_hasLambdas_1068_ == 0)
{
lean_del_object(v___x_1066_);
v___y_1047_ = v_a_1030_;
v___y_1048_ = v_a_1031_;
v___y_1049_ = v_a_1032_;
v___y_1050_ = v_a_1033_;
v___y_1051_ = v_a_1034_;
v___y_1052_ = v_a_1035_;
v___y_1053_ = v_a_1036_;
v___y_1054_ = v_a_1037_;
v___y_1055_ = v_a_1038_;
v___y_1056_ = v_a_1039_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_del_object(v___x_1044_);
v___x_1069_ = lean_box(v_hasLambdas_1068_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1069_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_dec(v_a_1042_);
v___y_1047_ = v_a_1030_;
v___y_1048_ = v_a_1031_;
v___y_1049_ = v_a_1032_;
v___y_1050_ = v_a_1033_;
v___y_1051_ = v_a_1034_;
v___y_1052_ = v_a_1035_;
v___y_1053_ = v_a_1036_;
v___y_1054_ = v_a_1037_;
v___y_1055_ = v_a_1038_;
v___y_1056_ = v_a_1039_;
goto v___jp_1046_;
}
v___jp_1046_:
{
if (lean_obj_tag(v_f_1029_) == 5)
{
lean_object* v_fn_1057_; 
lean_del_object(v___x_1044_);
v_fn_1057_ = lean_ctor_get(v_f_1029_, 0);
v_f_1029_ = v_fn_1057_;
v_a_1030_ = v___y_1047_;
v_a_1031_ = v___y_1048_;
v_a_1032_ = v___y_1049_;
v_a_1033_ = v___y_1050_;
v_a_1034_ = v___y_1051_;
v_a_1035_ = v___y_1052_;
v_a_1036_ = v___y_1053_;
v_a_1037_ = v___y_1054_;
v_a_1038_ = v___y_1055_;
v_a_1039_ = v___y_1056_;
goto _start;
}
else
{
uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1059_ = 0;
v___x_1060_ = lean_box(v___x_1059_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1060_);
v___x_1062_ = v___x_1044_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1041_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1041_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object* v_f_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_f_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_f_1083_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object* v_e_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
if (lean_obj_tag(v_e_1096_) == 5)
{
lean_object* v_fn_1108_; lean_object* v___x_1109_; 
v_fn_1108_ = lean_ctor_get(v_e_1096_, 0);
v___x_1109_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_fn_1108_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1109_;
}
else
{
uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = 0;
v___x_1111_ = lean_box(v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_e_1113_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_snd_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1203_; 
v_snd_1138_ = lean_ctor_get(v_b_1126_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_b_1126_, 0);
lean_dec(v_unused_1204_);
v___x_1140_ = v_b_1126_;
v_isShared_1141_ = v_isSharedCheck_1203_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_snd_1138_);
lean_dec(v_b_1126_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1203_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1202_; 
v_fst_1142_ = lean_ctor_get(v_snd_1138_, 0);
v_snd_1143_ = lean_ctor_get(v_snd_1138_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_snd_1138_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1145_ = v_snd_1138_;
v_isShared_1146_ = v_isSharedCheck_1202_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_inc(v_fst_1142_);
lean_dec(v_snd_1138_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1202_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1147_ = lean_box(0);
v___x_1167_ = lean_array_get_size(v_snd_1143_);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_nat_dec_eq(v___x_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_1142_, v___y_1127_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref(v___x_1170_);
if (lean_obj_tag(v_a_1171_) == 1)
{
lean_object* v_val_1172_; uint8_t v_hasLambdas_1173_; 
v_val_1172_ = lean_ctor_get(v_a_1171_, 0);
lean_inc(v_val_1172_);
lean_dec_ref(v_a_1171_);
v_hasLambdas_1173_ = lean_ctor_get_uint8(v_val_1172_, sizeof(void*)*12 + 3);
if (v_hasLambdas_1173_ == 0)
{
lean_dec(v_val_1172_);
goto v___jp_1148_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Meta_Grind_getEqcLambdas(v_val_1172_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v_val_1172_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref(v___x_1174_);
lean_inc(v_snd_1143_);
v___x_1176_ = l_Array_reverse___redArg(v_snd_1143_);
lean_inc(v_fst_1142_);
v___x_1177_ = l_Lean_Meta_Grind_propagateBetaEqs(v_a_1175_, v_fst_1142_, v___x_1176_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v_a_1175_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_dec_ref(v___x_1177_);
goto v___jp_1148_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1145_);
lean_dec(v_snd_1143_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_del_object(v___x_1145_);
lean_dec(v_snd_1143_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
v_a_1186_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1174_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1174_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_dec(v_a_1171_);
goto v___jp_1148_;
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1145_);
lean_dec(v_snd_1143_);
lean_dec(v_fst_1142_);
lean_del_object(v___x_1140_);
v_a_1194_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1170_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1170_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
goto v___jp_1148_;
}
v___jp_1148_:
{
if (lean_obj_tag(v_fst_1142_) == 5)
{
lean_object* v_fn_1149_; lean_object* v_arg_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v_fn_1149_ = lean_ctor_get(v_fst_1142_, 0);
lean_inc_ref(v_fn_1149_);
v_arg_1150_ = lean_ctor_get(v_fst_1142_, 1);
lean_inc_ref(v_arg_1150_);
lean_dec_ref(v_fst_1142_);
v___x_1151_ = lean_array_push(v_snd_1143_, v_arg_1150_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v___x_1151_);
lean_ctor_set(v___x_1145_, 0, v_fn_1149_);
v___x_1153_ = v___x_1145_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_fn_1149_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1153_);
lean_ctor_set(v___x_1140_, 0, v___x_1147_);
v___x_1155_ = v___x_1140_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v_b_1126_ = v___x_1155_;
goto _start;
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9));
if (v_isShared_1146_ == 0)
{
v___x_1161_ = v___x_1145_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_fst_1142_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_snd_1143_);
v___x_1161_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1161_);
lean_ctor_set(v___x_1140_, 0, v___x_1159_);
v___x_1163_ = v___x_1140_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object* v_b_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_b_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec(v___y_1206_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1267_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1267_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1267_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_unbox(v_a_1231_);
lean_dec(v_a_1231_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec_ref(v_e_1218_);
v___x_1236_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_del_object(v___x_1233_);
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_e_1218_);
lean_ctor_set(v___x_1242_, 1, v___x_1240_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v___x_1243_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1258_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1258_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1258_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; 
v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
lean_inc(v_fst_1249_);
lean_dec(v_a_1245_);
if (lean_obj_tag(v_fst_1249_) == 0)
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v_val_1254_; lean_object* v___x_1256_; 
v_val_1254_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc(v_val_1254_);
lean_dec_ref(v_fst_1249_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_val_1254_);
v___x_1256_ = v___x_1247_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_val_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1244_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1244_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_e_1218_);
v_a_1268_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1230_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1230_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object* v_e_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec(v_a_1277_);
return v_res_1288_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Beta(builtin);
}
#ifdef __cplusplus
}
#endif
