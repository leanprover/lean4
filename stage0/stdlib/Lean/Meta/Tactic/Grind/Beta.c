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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(12, 31, 7, 123, 15, 248, 150, 29)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", using "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0_value;
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
v___x_178_ = lean_unsigned_to_nat(1525u);
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
v_hasLambdas_194_ = lean_ctor_get_uint8(v_root_182_, sizeof(void*)*11 + 3);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(lean_object* v_msgData_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_env_497_; lean_object* v___x_498_; lean_object* v_mctx_499_; lean_object* v_lctx_500_; lean_object* v_options_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_496_ = lean_st_ref_get(v___y_494_);
v_env_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_496_);
v___x_498_ = lean_st_ref_get(v___y_492_);
v_mctx_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_mctx_499_);
lean_dec(v___x_498_);
v_lctx_500_ = lean_ctor_get(v___y_491_, 2);
v_options_501_ = lean_ctor_get(v___y_493_, 2);
lean_inc_ref(v_options_501_);
lean_inc_ref(v_lctx_500_);
v___x_502_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_502_, 0, v_env_497_);
lean_ctor_set(v___x_502_, 1, v_mctx_499_);
lean_ctor_set(v___x_502_, 2, v_lctx_500_);
lean_ctor_set(v___x_502_, 3, v_options_501_);
v___x_503_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_msgData_490_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(lean_object* v_msgData_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_511_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_512_; double v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_float_of_nat(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object* v_cls_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_ref_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_570_; 
v_ref_524_ = lean_ctor_get(v___y_521_, 5);
v___x_525_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_570_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_570_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_570_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v_traceState_531_; lean_object* v_env_532_; lean_object* v_nextMacroScope_533_; lean_object* v_ngen_534_; lean_object* v_auxDeclNGen_535_; lean_object* v_cache_536_; lean_object* v_messages_537_; lean_object* v_infoState_538_; lean_object* v_snapshotTasks_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_569_; 
v___x_530_ = lean_st_ref_take(v___y_522_);
v_traceState_531_ = lean_ctor_get(v___x_530_, 4);
v_env_532_ = lean_ctor_get(v___x_530_, 0);
v_nextMacroScope_533_ = lean_ctor_get(v___x_530_, 1);
v_ngen_534_ = lean_ctor_get(v___x_530_, 2);
v_auxDeclNGen_535_ = lean_ctor_get(v___x_530_, 3);
v_cache_536_ = lean_ctor_get(v___x_530_, 5);
v_messages_537_ = lean_ctor_get(v___x_530_, 6);
v_infoState_538_ = lean_ctor_get(v___x_530_, 7);
v_snapshotTasks_539_ = lean_ctor_get(v___x_530_, 8);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_569_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_569_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snapshotTasks_539_);
lean_inc(v_infoState_538_);
lean_inc(v_messages_537_);
lean_inc(v_cache_536_);
lean_inc(v_traceState_531_);
lean_inc(v_auxDeclNGen_535_);
lean_inc(v_ngen_534_);
lean_inc(v_nextMacroScope_533_);
lean_inc(v_env_532_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_569_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint64_t v_tid_543_; lean_object* v_traces_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_568_; 
v_tid_543_ = lean_ctor_get_uint64(v_traceState_531_, sizeof(void*)*1);
v_traces_544_ = lean_ctor_get(v_traceState_531_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_traceState_531_);
if (v_isSharedCheck_568_ == 0)
{
v___x_546_ = v_traceState_531_;
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_traces_544_);
lean_dec(v_traceState_531_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_568_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; double v___x_549_; uint8_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_548_ = lean_box(0);
v___x_549_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0);
v___x_550_ = 0;
v___x_551_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1));
v___x_552_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_552_, 0, v_cls_517_);
lean_ctor_set(v___x_552_, 1, v___x_548_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
lean_ctor_set_float(v___x_552_, sizeof(void*)*3, v___x_549_);
lean_ctor_set_float(v___x_552_, sizeof(void*)*3 + 8, v___x_549_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*3 + 16, v___x_550_);
v___x_553_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2));
v___x_554_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v_a_526_);
lean_ctor_set(v___x_554_, 2, v___x_553_);
lean_inc(v_ref_524_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v_ref_524_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_PersistentArray_push___redArg(v_traces_544_, v___x_555_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_556_);
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_556_);
lean_ctor_set_uint64(v_reuseFailAlloc_567_, sizeof(void*)*1, v_tid_543_);
v___x_558_ = v_reuseFailAlloc_567_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v___x_558_);
v___x_560_ = v___x_541_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_env_532_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_nextMacroScope_533_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_ngen_534_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_auxDeclNGen_535_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 5, v_cache_536_);
lean_ctor_set(v_reuseFailAlloc_566_, 6, v_messages_537_);
lean_ctor_set(v_reuseFailAlloc_566_, 7, v_infoState_538_);
lean_ctor_set(v_reuseFailAlloc_566_, 8, v_snapshotTasks_539_);
v___x_560_ = v_reuseFailAlloc_566_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = lean_st_ref_set(v___y_522_, v___x_560_);
v___x_562_ = lean_box(0);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_562_);
v___x_564_ = v___x_528_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object* v_cls_571_, lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_571_, v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object* v_as_579_, size_t v_sz_580_, size_t v_i_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_lt(v_i_581_, v_sz_580_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_b_582_);
return v___x_590_;
}
else
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_array_uget_borrowed(v_as_579_, v_i_581_);
v___x_592_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_591_, v___y_583_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_618_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
v_fst_594_ = lean_ctor_get(v_b_582_, 0);
v_snd_595_ = lean_ctor_get(v_b_582_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_b_582_);
if (v_isSharedCheck_618_ == 0)
{
v___x_597_ = v_b_582_;
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_b_582_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_618_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___y_600_; uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_le(v_fst_594_, v_a_593_);
if (v___x_617_ == 0)
{
lean_dec(v_a_593_);
v___y_600_ = v_fst_594_;
goto v___jp_599_;
}
else
{
lean_dec(v_fst_594_);
v___y_600_ = v_a_593_;
goto v___jp_599_;
}
v___jp_599_:
{
lean_object* v___x_601_; 
lean_inc(v_a_591_);
v___x_601_ = l_Lean_Meta_mkCongrFun(v_snd_595_, v_a_591_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___x_601_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v_a_602_);
lean_ctor_set(v___x_597_, 0, v___y_600_);
v___x_604_ = v___x_597_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___y_600_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_602_);
v___x_604_ = v_reuseFailAlloc_608_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
size_t v___x_605_; size_t v___x_606_; 
v___x_605_ = ((size_t)1ULL);
v___x_606_ = lean_usize_add(v_i_581_, v___x_605_);
v_i_581_ = v___x_606_;
v_b_582_ = v___x_604_;
goto _start;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v___y_600_);
lean_del_object(v___x_597_);
v_a_609_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_601_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_601_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec_ref(v_b_582_);
v_a_619_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_592_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_592_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object* v_as_627_, lean_object* v_sz_628_, lean_object* v_i_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_628_);
lean_dec(v_sz_628_);
v_i_boxed_638_ = lean_unbox_usize(v_i_629_);
lean_dec(v_i_629_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_627_, v_sz_boxed_637_, v_i_boxed_638_, v_b_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v_as_627_);
return v_res_639_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2));
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__4));
v___x_650_ = l_Lean_Name_append(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__6));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object* v_args_654_, lean_object* v_f_655_, lean_object* v_as_656_, size_t v_sz_657_, size_t v_i_658_, lean_object* v_b_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_a_672_; uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_b_659_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v_a_679_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_678_ = lean_box(0);
v_a_679_ = lean_array_uget_borrowed(v_as_656_, v_i_658_);
lean_inc_ref(v_args_654_);
lean_inc(v_a_679_);
v___x_698_ = l_Lean_Expr_beta(v_a_679_, v_args_654_);
v___x_699_ = l_Lean_Expr_isLambda(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_679_, v___y_660_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
v___x_702_ = l_Lean_Meta_Grind_getGeneration___redArg(v_f_655_, v___y_660_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___y_705_; uint8_t v___x_775_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_775_ = lean_nat_dec_le(v_a_701_, v_a_703_);
if (v___x_775_ == 0)
{
lean_dec(v_a_703_);
v___y_705_ = v_a_701_;
goto v___jp_704_;
}
else
{
lean_dec(v_a_701_);
v___y_705_ = v_a_703_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref_n(v_f_655_, 2);
v___x_706_ = l_Lean_mkAppN(v_f_655_, v_args_654_);
lean_inc(v_a_679_);
v___x_707_ = l_Lean_Meta_Grind_hasSameType(v_f_655_, v_a_679_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; uint8_t v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_unbox(v_a_708_);
lean_dec(v_a_708_);
if (v___x_709_ == 0)
{
lean_dec_ref(v___x_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___x_698_);
v_a_672_ = v___x_678_;
goto v___jp_671_;
}
else
{
lean_object* v___x_710_; 
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
lean_inc(v___y_663_);
lean_inc_ref(v___y_662_);
lean_inc(v___y_661_);
lean_inc(v___y_660_);
lean_inc(v_a_679_);
lean_inc_ref(v_f_655_);
v___x_710_ = lean_grind_mk_eq_proof(v_f_655_, v_a_679_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_710_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___y_705_);
lean_ctor_set(v___x_712_, 1, v_a_711_);
v_sz_713_ = lean_array_size(v_args_654_);
v___x_714_ = ((size_t)0ULL);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_654_, v_sz_713_, v___x_714_, v___x_712_, v___y_660_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref(v___x_715_);
v___x_717_ = l_Lean_Meta_mkEq(v___x_706_, v___x_698_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_options_718_; uint8_t v_hasTrace_719_; 
v_options_718_ = lean_ctor_get(v___y_668_, 2);
v_hasTrace_719_ = lean_ctor_get_uint8(v_options_718_, sizeof(void*)*1);
if (v_hasTrace_719_ == 0)
{
lean_object* v_a_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; 
v_a_720_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_717_);
v_fst_721_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_fst_721_);
v_snd_722_ = lean_ctor_get(v_a_716_, 1);
lean_inc(v_snd_722_);
lean_dec(v_a_716_);
v___y_681_ = v_fst_721_;
v___y_682_ = v_a_720_;
v___y_683_ = v_snd_722_;
v___y_684_ = v___y_660_;
v___y_685_ = v___y_661_;
v___y_686_ = v___y_662_;
v___y_687_ = v___y_663_;
v___y_688_ = v___y_664_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
goto v___jp_680_;
}
else
{
lean_object* v_a_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_742_; 
v_a_723_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_723_);
lean_dec_ref(v___x_717_);
v_fst_724_ = lean_ctor_get(v_a_716_, 0);
v_snd_725_ = lean_ctor_get(v_a_716_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_742_ == 0)
{
v___x_727_ = v_a_716_;
v_isShared_728_ = v_isSharedCheck_742_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_a_716_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_742_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_inheritedTraceOptions_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_inheritedTraceOptions_729_ = lean_ctor_get(v___y_668_, 13);
v___x_730_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__2));
v___x_731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__5);
v___x_732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_729_, v_options_718_, v___x_731_);
if (v___x_732_ == 0)
{
lean_del_object(v___x_727_);
v___y_681_ = v_fst_724_;
v___y_682_ = v_a_723_;
v___y_683_ = v_snd_725_;
v___y_684_ = v___y_660_;
v___y_685_ = v___y_661_;
v___y_686_ = v___y_662_;
v___y_687_ = v___y_663_;
v___y_688_ = v___y_664_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
goto v___jp_680_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_updateLastTag(v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec_ref(v___x_733_);
lean_inc(v_a_723_);
v___x_734_ = l_Lean_MessageData_ofExpr(v_a_723_);
v___x_735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___closed__7);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 7);
lean_ctor_set(v___x_727_, 1, v___x_735_);
lean_ctor_set(v___x_727_, 0, v___x_734_);
v___x_737_ = v___x_727_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_inc(v_a_679_);
v___x_738_ = l_Lean_MessageData_ofExpr(v_a_679_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_730_, v___x_739_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_dec_ref(v___x_740_);
v___y_681_ = v_fst_724_;
v___y_682_ = v_a_723_;
v___y_683_ = v_snd_725_;
v___y_684_ = v___y_660_;
v___y_685_ = v___y_661_;
v___y_686_ = v___y_662_;
v___y_687_ = v___y_663_;
v___y_688_ = v___y_664_;
v___y_689_ = v___y_665_;
v___y_690_ = v___y_666_;
v___y_691_ = v___y_667_;
v___y_692_ = v___y_668_;
v___y_693_ = v___y_669_;
goto v___jp_680_;
}
else
{
lean_dec(v_snd_725_);
lean_dec(v_fst_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
return v___x_740_;
}
}
}
else
{
lean_del_object(v___x_727_);
lean_dec(v_snd_725_);
lean_dec(v_fst_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
return v___x_733_;
}
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_716_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_743_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_717_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_717_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v___x_706_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_751_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_715_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_715_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v___x_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_759_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_710_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_710_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v___x_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_767_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_707_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_707_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_701_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_776_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_702_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_702_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v___x_698_);
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
v_a_784_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_700_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_700_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_dec_ref(v___x_698_);
v_a_672_ = v___x_678_;
goto v___jp_671_;
}
v___jp_680_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v___y_681_, v___x_694_);
lean_dec(v___y_681_);
lean_inc(v_a_679_);
v___x_696_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_696_, 0, v_a_679_);
v___x_697_ = l_Lean_Meta_Grind_addNewRawFact(v___y_683_, v___y_682_, v___x_695_, v___x_696_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_dec_ref(v___x_697_);
v_a_672_ = v___x_678_;
goto v___jp_671_;
}
else
{
lean_dec_ref(v_f_655_);
lean_dec_ref(v_args_654_);
return v___x_697_;
}
}
}
v___jp_671_:
{
size_t v___x_673_; size_t v___x_674_; 
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_658_, v___x_673_);
v_i_658_ = v___x_674_;
v_b_659_ = v_a_672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object** _args){
lean_object* v_args_792_ = _args[0];
lean_object* v_f_793_ = _args[1];
lean_object* v_as_794_ = _args[2];
lean_object* v_sz_795_ = _args[3];
lean_object* v_i_796_ = _args[4];
lean_object* v_b_797_ = _args[5];
lean_object* v___y_798_ = _args[6];
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
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_810_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_args_792_, v_f_793_, v_as_794_, v_sz_boxed_809_, v_i_boxed_810_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v_as_794_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object* v_lams_812_, lean_object* v_f_813_, lean_object* v_args_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_array_get_size(v_args_814_);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_nat_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; size_t v_sz_830_; size_t v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_box(0);
v_sz_830_ = lean_array_size(v_lams_812_);
v___x_831_ = ((size_t)0ULL);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_args_814_, v_f_813_, v_lams_812_, v_sz_830_, v___x_831_, v___x_829_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_829_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_829_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
return v___x_832_;
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v_args_814_);
lean_dec_ref(v_f_813_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object* v_lams_843_, lean_object* v_f_844_, lean_object* v_args_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_843_, v_f_844_, v_args_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_lams_843_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object* v_as_858_, size_t v_sz_859_, size_t v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_858_, v_sz_859_, v_i_860_, v_b_861_, v___y_862_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object* v_as_874_, lean_object* v_sz_875_, lean_object* v_i_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_sz_boxed_889_ = lean_unbox_usize(v_sz_875_);
lean_dec(v_sz_875_);
v_i_boxed_890_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_874_, v_sz_boxed_889_, v_i_boxed_890_, v_b_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v_as_874_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object* v_cls_892_, lean_object* v_msg_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_892_, v_msg_893_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object* v_cls_906_, lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_906_, v_msg_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object* v_f_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_920_, v_a_921_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_965_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_965_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_965_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_965_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; 
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v_val_955_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_964_ == 0)
{
v___x_957_ = v_a_933_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_val_955_);
lean_dec(v_a_933_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v_hasLambdas_959_; 
v_hasLambdas_959_ = lean_ctor_get_uint8(v_val_955_, sizeof(void*)*11 + 3);
lean_dec(v_val_955_);
if (v_hasLambdas_959_ == 0)
{
lean_del_object(v___x_957_);
v___y_938_ = v_a_921_;
v___y_939_ = v_a_922_;
v___y_940_ = v_a_923_;
v___y_941_ = v_a_924_;
v___y_942_ = v_a_925_;
v___y_943_ = v_a_926_;
v___y_944_ = v_a_927_;
v___y_945_ = v_a_928_;
v___y_946_ = v_a_929_;
v___y_947_ = v_a_930_;
goto v___jp_937_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_962_; 
lean_del_object(v___x_935_);
v___x_960_ = lean_box(v_hasLambdas_959_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 0);
lean_ctor_set(v___x_957_, 0, v___x_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_dec(v_a_933_);
v___y_938_ = v_a_921_;
v___y_939_ = v_a_922_;
v___y_940_ = v_a_923_;
v___y_941_ = v_a_924_;
v___y_942_ = v_a_925_;
v___y_943_ = v_a_926_;
v___y_944_ = v_a_927_;
v___y_945_ = v_a_928_;
v___y_946_ = v_a_929_;
v___y_947_ = v_a_930_;
goto v___jp_937_;
}
v___jp_937_:
{
if (lean_obj_tag(v_f_920_) == 5)
{
lean_object* v_fn_948_; 
lean_del_object(v___x_935_);
v_fn_948_ = lean_ctor_get(v_f_920_, 0);
v_f_920_ = v_fn_948_;
v_a_921_ = v___y_938_;
v_a_922_ = v___y_939_;
v_a_923_ = v___y_940_;
v_a_924_ = v___y_941_;
v_a_925_ = v___y_942_;
v_a_926_ = v___y_943_;
v_a_927_ = v___y_944_;
v_a_928_ = v___y_945_;
v_a_929_ = v___y_946_;
v_a_930_ = v___y_947_;
goto _start;
}
else
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = 0;
v___x_951_ = lean_box(v___x_950_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_951_);
v___x_953_ = v___x_935_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v_a_966_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_932_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_932_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object* v_f_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_f_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_f_974_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
if (lean_obj_tag(v_e_987_) == 5)
{
lean_object* v_fn_999_; lean_object* v___x_1000_; 
v_fn_999_ = lean_ctor_get(v_e_987_, 0);
v___x_1000_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_fn_999_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = 0;
v___x_1002_ = lean_box(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object* v_e_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec_ref(v_e_1004_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object* v_b_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1096_; 
v_snd_1031_ = lean_ctor_get(v_b_1019_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_b_1019_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_b_1019_, 0);
lean_dec(v_unused_1097_);
v___x_1033_ = v_b_1019_;
v_isShared_1034_ = v_isSharedCheck_1096_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_dec(v_b_1019_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1096_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1095_; 
v_fst_1035_ = lean_ctor_get(v_snd_1031_, 0);
v_snd_1036_ = lean_ctor_get(v_snd_1031_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_snd_1031_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1038_ = v_snd_1031_;
v_isShared_1039_ = v_isSharedCheck_1095_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_snd_1031_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1095_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1040_ = lean_box(0);
v___x_1060_ = lean_array_get_size(v_snd_1036_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_nat_dec_eq(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_1035_, v___y_1020_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1063_);
if (lean_obj_tag(v_a_1064_) == 1)
{
lean_object* v_val_1065_; uint8_t v_hasLambdas_1066_; 
v_val_1065_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref(v_a_1064_);
v_hasLambdas_1066_ = lean_ctor_get_uint8(v_val_1065_, sizeof(void*)*11 + 3);
if (v_hasLambdas_1066_ == 0)
{
lean_dec(v_val_1065_);
goto v___jp_1041_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Grind_getEqcLambdas(v_val_1065_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v_val_1065_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1067_);
lean_inc(v_snd_1036_);
v___x_1069_ = l_Array_reverse___redArg(v_snd_1036_);
lean_inc(v_fst_1035_);
v___x_1070_ = l_Lean_Meta_Grind_propagateBetaEqs(v_a_1068_, v_fst_1035_, v___x_1069_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v_a_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_dec_ref(v___x_1070_);
goto v___jp_1041_;
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_1038_);
lean_dec(v_snd_1036_);
lean_dec(v_fst_1035_);
lean_del_object(v___x_1033_);
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1038_);
lean_dec(v_snd_1036_);
lean_dec(v_fst_1035_);
lean_del_object(v___x_1033_);
v_a_1079_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1067_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1067_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
else
{
lean_dec(v_a_1064_);
goto v___jp_1041_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_del_object(v___x_1038_);
lean_dec(v_snd_1036_);
lean_dec(v_fst_1035_);
lean_del_object(v___x_1033_);
v_a_1087_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1063_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1063_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
else
{
goto v___jp_1041_;
}
v___jp_1041_:
{
if (lean_obj_tag(v_fst_1035_) == 5)
{
lean_object* v_fn_1042_; lean_object* v_arg_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v_fn_1042_ = lean_ctor_get(v_fst_1035_, 0);
lean_inc_ref(v_fn_1042_);
v_arg_1043_ = lean_ctor_get(v_fst_1035_, 1);
lean_inc_ref(v_arg_1043_);
lean_dec_ref(v_fst_1035_);
v___x_1044_ = lean_array_push(v_snd_1036_, v_arg_1043_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1044_);
lean_ctor_set(v___x_1038_, 0, v_fn_1042_);
v___x_1046_ = v___x_1038_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_fn_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1046_);
lean_ctor_set(v___x_1033_, 0, v___x_1040_);
v___x_1048_ = v___x_1033_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
v_b_1019_ = v___x_1048_;
goto _start;
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___closed__0));
if (v_isShared_1039_ == 0)
{
v___x_1054_ = v___x_1038_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1036_);
v___x_1054_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1054_);
lean_ctor_set(v___x_1033_, 0, v___x_1052_);
v___x_1056_ = v___x_1033_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_b_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object* v_e_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1160_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1160_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1160_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_dec_ref(v_e_1111_);
v___x_1129_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
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
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_del_object(v___x_1126_);
v___x_1133_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_e_1111_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v___x_1136_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1151_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1151_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1151_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_fst_1142_; 
v_fst_1142_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_fst_1142_);
lean_dec(v_a_1138_);
if (lean_obj_tag(v_fst_1142_) == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; 
v_val_1147_ = lean_ctor_get(v_fst_1142_, 0);
lean_inc(v_val_1147_);
lean_dec_ref(v_fst_1142_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_val_1147_);
v___x_1149_ = v___x_1140_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_val_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1137_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1137_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_e_1111_);
v_a_1161_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1123_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1123_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object* v_e_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec(v_a_1170_);
return v_res_1181_;
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
