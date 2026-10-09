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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getMaxGeneration___redArg(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(lean_object* v_msg_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
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
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_1881__overap_75_; lean_object* v___x_76_; 
v___x_67_ = l_StateRefT_x27_instMonad___redArg(v___x_66_);
v___x_68_ = l_ReaderT_instMonad___redArg(v___x_67_);
v___x_69_ = l_StateRefT_x27_instMonad___redArg(v___x_68_);
v___x_70_ = l_ReaderT_instMonad___redArg(v___x_69_);
v___x_71_ = l_ReaderT_instMonad___redArg(v___x_70_);
v___x_72_ = l_StateRefT_x27_instMonad___redArg(v___x_71_);
v___x_73_ = lean_box(0);
v___x_74_ = l_instInhabitedOfMonad___redArg(v___x_72_, v___x_73_);
v___x_1881__overap_75_ = lean_panic_fn_borrowed(v___x_74_, v_msg_6_);
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
v___x_76_ = lean_apply_11(v___x_1881__overap_75_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_6_ = stack[0].m_obj;
lean_object* v___y_7_ = stack[1].m_obj;
lean_object* v___y_8_ = stack[2].m_obj;
lean_object* v___y_9_ = stack[3].m_obj;
lean_object* v___y_10_ = stack[4].m_obj;
lean_object* v___y_11_ = stack[5].m_obj;
lean_object* v___y_12_ = stack[6].m_obj;
lean_object* v___y_13_ = stack[7].m_obj;
lean_object* v___y_14_ = stack[8].m_obj;
lean_object* v___y_15_ = stack[9].m_obj;
lean_object* v___y_16_ = stack[10].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v_msg_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1___boxed(lean_object* v_msg_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v_msg_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec(v___y_91_);
return v_res_102_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object* v___x_103_, lean_object* v_a_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_snd_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_163_; 
v_snd_111_ = lean_ctor_get(v_a_104_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v_a_104_, 0);
lean_dec(v_unused_164_);
v___x_113_ = v_a_104_;
v_isShared_114_ = v_isSharedCheck_163_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_snd_111_);
lean_dec(v_a_104_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_163_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_162_; 
v_fst_115_ = lean_ctor_get(v_snd_111_, 0);
v_snd_116_ = lean_ctor_get(v_snd_111_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_snd_111_);
if (v_isSharedCheck_162_ == 0)
{
v___x_118_ = v_snd_111_;
v_isShared_119_ = v_isSharedCheck_162_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_snd_111_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_162_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_st_ref_get(v___y_105_);
lean_inc(v_fst_115_);
v___x_122_ = l_Lean_Meta_Grind_Goal_getENode(v___x_121_, v_fst_115_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___x_121_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_153_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_153_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_153_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_153_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v_self_127_; lean_object* v_next_128_; lean_object* v_a_130_; uint8_t v___x_151_; 
v_self_127_ = lean_ctor_get(v_a_123_, 0);
lean_inc_ref(v_self_127_);
v_next_128_ = lean_ctor_get(v_a_123_, 1);
lean_inc_ref(v_next_128_);
lean_dec(v_a_123_);
v___x_151_ = l_Lean_Expr_isLambda(v_self_127_);
if (v___x_151_ == 0)
{
lean_dec_ref(v_self_127_);
v_a_130_ = v_snd_116_;
goto v___jp_129_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = lean_array_push(v_snd_116_, v_self_127_);
v_a_130_ = v___x_152_;
goto v___jp_129_;
}
v___jp_129_:
{
size_t v___x_131_; size_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_ptr_addr(v_next_128_);
v___x_132_ = lean_ptr_addr(v___x_103_);
v___x_133_ = lean_usize_dec_eq(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_135_; 
lean_del_object(v___x_125_);
lean_dec(v_fst_115_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_130_);
lean_ctor_set(v___x_118_, 0, v_next_128_);
v___x_135_ = v___x_118_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_next_128_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_a_130_);
v___x_135_ = v_reuseFailAlloc_140_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_137_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_135_);
lean_ctor_set(v___x_113_, 0, v___x_120_);
v___x_137_ = v___x_113_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_139_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
v_a_104_ = v___x_137_;
goto _start;
}
}
}
else
{
lean_object* v___x_141_; lean_object* v___x_143_; 
lean_dec_ref(v_next_128_);
lean_inc_ref(v_a_130_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_a_130_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_a_130_);
v___x_143_ = v___x_118_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_a_130_);
v___x_143_ = v_reuseFailAlloc_150_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_143_);
lean_ctor_set(v___x_113_, 0, v___x_141_);
v___x_145_ = v___x_113_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_145_);
v___x_147_ = v___x_125_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_del_object(v___x_118_);
lean_dec(v_snd_116_);
lean_dec(v_fst_115_);
lean_del_object(v___x_113_);
v_a_154_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_122_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_122_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_103_ = stack[0].m_obj;
lean_object* v_a_104_ = stack[1].m_obj;
lean_object* v___y_105_ = stack[2].m_obj;
lean_object* v___y_106_ = stack[3].m_obj;
lean_object* v___y_107_ = stack[4].m_obj;
lean_object* v___y_108_ = stack[5].m_obj;
lean_object* v___y_109_ = stack[6].m_obj;
lean_object* v_res_165_;
v_res_165_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_103_, v_a_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object* v___x_166_, lean_object* v_a_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_166_, v_a_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___x_166_);
return v_res_174_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__3));
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_unsigned_to_nat(1627u);
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__2));
v___x_184_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__1));
v___x_185_ = l_mkPanicMessageWithDecl(v___x_184_, v___x_183_, v___x_182_, v___x_181_, v___x_180_);
return v___x_185_;
}
}
lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object* v_root_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
uint8_t v_hasLambdas_198_; 
v_hasLambdas_198_ = lean_ctor_get_uint8(v_root_186_, sizeof(void*)*12 + 3);
if (v_hasLambdas_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
else
{
lean_object* v_self_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_self_201_ = lean_ctor_get(v_root_186_, 0);
v___x_202_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_203_ = lean_box(0);
lean_inc_ref(v_self_201_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_self_201_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v_self_201_, v___x_205_, v_a_187_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_236_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_236_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_236_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_236_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_fst_211_; 
v_fst_211_ = lean_ctor_get(v_a_207_, 0);
if (lean_obj_tag(v_fst_211_) == 0)
{
lean_object* v_snd_212_; lean_object* v_snd_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_del_object(v___x_209_);
v_snd_212_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_snd_212_);
lean_dec(v_a_207_);
v_snd_213_ = lean_ctor_get(v_snd_212_, 1);
lean_inc(v_snd_213_);
lean_dec(v_snd_212_);
v___x_214_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_215_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_214_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v___x_215_, 0);
lean_dec(v_unused_223_);
v___x_217_ = v___x_215_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_dec(v___x_215_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v_snd_213_);
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_snd_213_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v_snd_213_);
v_a_224_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_215_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_215_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; 
lean_inc_ref(v_fst_211_);
lean_dec(v_a_207_);
v_val_232_ = lean_ctor_get(v_fst_211_, 0);
lean_inc(v_val_232_);
lean_dec_ref_known(v_fst_211_, 1);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v_val_232_);
v___x_234_ = v___x_209_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_val_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_a_237_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_206_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_206_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getEqcLambdas_0interp(lean_interpreter_value* stack)
{
lean_object* v_root_186_ = stack[0].m_obj;
lean_object* v_a_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
lean_object* v_a_189_ = stack[3].m_obj;
lean_object* v_a_190_ = stack[4].m_obj;
lean_object* v_a_191_ = stack[5].m_obj;
lean_object* v_a_192_ = stack[6].m_obj;
lean_object* v_a_193_ = stack[7].m_obj;
lean_object* v_a_194_ = stack[8].m_obj;
lean_object* v_a_195_ = stack[9].m_obj;
lean_object* v_a_196_ = stack[10].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_Meta_Grind_getEqcLambdas(v_root_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object* v_root_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Meta_Grind_getEqcLambdas(v_root_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_root_246_);
return v_res_258_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object* v___x_259_, lean_object* v_inst_260_, lean_object* v_a_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_259_, v_a_261_, v___y_262_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_273_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_259_ = stack[0].m_obj;
lean_object* v_a_261_ = stack[2].m_obj;
lean_object* v___y_262_ = stack[3].m_obj;
lean_object* v___y_263_ = stack[4].m_obj;
lean_object* v___y_264_ = stack[5].m_obj;
lean_object* v___y_265_ = stack[6].m_obj;
lean_object* v___y_266_ = stack[7].m_obj;
lean_object* v___y_267_ = stack[8].m_obj;
lean_object* v___y_268_ = stack[9].m_obj;
lean_object* v___y_269_ = stack[10].m_obj;
lean_object* v___y_270_ = stack[11].m_obj;
lean_object* v___y_271_ = stack[12].m_obj;
lean_object* v_res_274_;
v_res_274_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(v___x_259_, lean_box(0), v_a_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
stack->m_obj
 = v_res_274_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object* v___x_275_, lean_object* v_inst_276_, lean_object* v_a_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(v___x_275_, v_inst_276_, v_a_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___x_275_);
return v_res_289_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object* v___y_293_, lean_object* v_as_294_, size_t v_sz_295_, size_t v_i_296_, lean_object* v_b_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_lt(v_i_296_, v_sz_295_);
if (v___x_298_ == 0)
{
lean_inc_ref(v_b_297_);
return v_b_297_;
}
else
{
lean_object* v___x_299_; lean_object* v_a_300_; size_t v___x_301_; size_t v___x_302_; uint8_t v___x_303_; 
v___x_299_ = lean_box(0);
v_a_300_ = lean_array_uget_borrowed(v_as_294_, v_i_296_);
v___x_301_ = lean_ptr_addr(v_a_300_);
v___x_302_ = lean_ptr_addr(v___y_293_);
v___x_303_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; 
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0));
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_296_, v___x_305_);
v_i_296_ = v___x_306_;
v_b_297_ = v___x_304_;
goto _start;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc(v_a_300_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_a_300_);
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_299_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_293_ = stack[0].m_obj;
lean_object* v_as_294_ = stack[1].m_obj;
size_t v_sz_295_ = stack[2].m_num;
size_t v_i_296_ = stack[3].m_num;
lean_object* v_b_297_ = stack[4].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_293_, v_as_294_, v_sz_295_, v_i_296_, v_b_297_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object* v___y_312_, lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_){
_start:
{
size_t v_sz_boxed_317_; size_t v_i_boxed_318_; lean_object* v_res_319_; 
v_sz_boxed_317_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_318_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_312_, v_as_313_, v_sz_boxed_317_, v_i_boxed_318_, v_b_316_);
lean_dec_ref(v_b_316_);
lean_dec_ref(v_as_313_);
lean_dec_ref(v___y_312_);
return v_res_319_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_396_; 
v_snd_331_ = lean_ctor_get(v_a_324_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_a_324_, 0);
lean_dec(v_unused_397_);
v___x_333_ = v_a_324_;
v_isShared_334_ = v_isSharedCheck_396_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_dec(v_a_324_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_396_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_395_; 
v_fst_335_ = lean_ctor_get(v_snd_331_, 0);
v_snd_336_ = lean_ctor_get(v_snd_331_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_snd_331_);
if (v_isSharedCheck_395_ == 0)
{
v___x_338_ = v_snd_331_;
v_isShared_339_ = v_isSharedCheck_395_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snd_336_);
lean_inc(v_fst_335_);
lean_dec(v_snd_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_395_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_box(0);
v___x_341_ = lean_st_ref_get(v___y_325_);
lean_inc(v_fst_335_);
v___x_342_ = l_Lean_Meta_Grind_Goal_getENode(v___x_341_, v_fst_335_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___x_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_386_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_386_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_386_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_386_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_self_347_; lean_object* v_next_348_; lean_object* v_a_350_; lean_object* v_fn_371_; lean_object* v___x_372_; lean_object* v___y_374_; lean_object* v___y_377_; lean_object* v___x_384_; 
v_self_347_ = lean_ctor_get(v_a_343_, 0);
lean_inc_ref(v_self_347_);
v_next_348_ = lean_ctor_get(v_a_343_, 1);
lean_inc_ref(v_next_348_);
lean_dec(v_a_343_);
v_fn_371_ = l_Lean_Expr_getAppFn(v_self_347_);
lean_dec_ref(v_self_347_);
v___x_372_ = lean_st_ref_get(v___y_325_);
v___x_384_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_372_, v_fn_371_);
lean_dec(v___x_372_);
if (lean_obj_tag(v___x_384_) == 0)
{
v___y_377_ = v_fn_371_;
goto v___jp_376_;
}
else
{
lean_object* v_val_385_; 
lean_dec_ref(v_fn_371_);
v_val_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_val_385_);
lean_dec_ref_known(v___x_384_, 1);
v___y_377_ = v_val_385_;
goto v___jp_376_;
}
v___jp_349_:
{
size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_ptr_addr(v_next_348_);
v___x_352_ = lean_ptr_addr(v_e_323_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_355_; 
lean_del_object(v___x_345_);
lean_dec(v_fst_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v_a_350_);
lean_ctor_set(v___x_338_, 0, v_next_348_);
v___x_355_ = v___x_338_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_next_348_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_350_);
v___x_355_ = v_reuseFailAlloc_360_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_355_);
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_357_ = v___x_333_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v_a_324_ = v___x_357_;
goto _start;
}
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_dec_ref(v_next_348_);
lean_inc_ref(v_a_350_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_a_350_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v_a_350_);
v___x_363_ = v___x_338_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_fst_335_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_350_);
v___x_363_ = v_reuseFailAlloc_370_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_363_);
lean_ctor_set(v___x_333_, 0, v___x_361_);
v___x_365_ = v___x_333_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_365_);
v___x_367_ = v___x_345_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
v___jp_373_:
{
lean_object* v___x_375_; 
v___x_375_ = lean_array_push(v_snd_336_, v___y_374_);
v_a_350_ = v___x_375_;
goto v___jp_349_;
}
v___jp_376_:
{
lean_object* v___x_378_; size_t v_sz_379_; size_t v___x_380_; lean_object* v___x_381_; lean_object* v_fst_382_; 
v___x_378_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0));
v_sz_379_ = lean_array_size(v_snd_336_);
v___x_380_ = ((size_t)0ULL);
v___x_381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_377_, v_snd_336_, v_sz_379_, v___x_380_, v___x_378_);
v_fst_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_fst_382_);
lean_dec_ref(v___x_381_);
if (lean_obj_tag(v_fst_382_) == 0)
{
v___y_374_ = v___y_377_;
goto v___jp_373_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v_fst_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_fst_382_, 1);
if (lean_obj_tag(v_val_383_) == 0)
{
v___y_374_ = v___y_377_;
goto v___jp_373_;
}
else
{
lean_dec_ref_known(v_val_383_, 1);
lean_dec_ref(v___y_377_);
v_a_350_ = v_snd_336_;
goto v___jp_349_;
}
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_del_object(v___x_338_);
lean_dec(v_snd_336_);
lean_dec(v_fst_335_);
lean_del_object(v___x_333_);
v_a_387_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_342_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_342_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_323_ = stack[0].m_obj;
lean_object* v_a_324_ = stack[1].m_obj;
lean_object* v___y_325_ = stack[2].m_obj;
lean_object* v___y_326_ = stack[3].m_obj;
lean_object* v___y_327_ = stack[4].m_obj;
lean_object* v___y_328_ = stack[5].m_obj;
lean_object* v___y_329_ = stack[6].m_obj;
lean_object* v_res_398_;
v_res_398_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_323_, v_a_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_399_, v_a_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v_e_399_);
return v_res_407_;
}
}
lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object* v_e_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_421_ = lean_box(0);
lean_inc_ref(v_e_408_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_e_408_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_408_, v___x_423_, v_a_409_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec_ref(v_e_408_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_454_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_454_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_fst_429_; 
v_fst_429_ = lean_ctor_get(v_a_425_, 0);
if (lean_obj_tag(v_fst_429_) == 0)
{
lean_object* v_snd_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_del_object(v___x_427_);
v_snd_430_ = lean_ctor_get(v_a_425_, 1);
lean_inc(v_snd_430_);
lean_dec(v_a_425_);
v_snd_431_ = lean_ctor_get(v_snd_430_, 1);
lean_inc(v_snd_431_);
lean_dec(v_snd_430_);
v___x_432_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_433_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_432_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_433_, 0);
lean_dec(v_unused_441_);
v___x_435_ = v___x_433_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_433_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_snd_431_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_snd_431_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec(v_snd_431_);
v_a_442_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_433_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_433_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_val_450_; lean_object* v___x_452_; 
lean_inc_ref(v_fst_429_);
lean_dec(v_a_425_);
v_val_450_ = lean_ctor_get(v_fst_429_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_fst_429_, 1);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_val_450_);
v___x_452_ = v___x_427_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_val_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_424_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_424_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_getFnRoots_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_408_ = stack[0].m_obj;
lean_object* v_a_409_ = stack[1].m_obj;
lean_object* v_a_410_ = stack[2].m_obj;
lean_object* v_a_411_ = stack[3].m_obj;
lean_object* v_a_412_ = stack[4].m_obj;
lean_object* v_a_413_ = stack[5].m_obj;
lean_object* v_a_414_ = stack[6].m_obj;
lean_object* v_a_415_ = stack[7].m_obj;
lean_object* v_a_416_ = stack[8].m_obj;
lean_object* v_a_417_ = stack[9].m_obj;
lean_object* v_a_418_ = stack[10].m_obj;
lean_object* v_res_463_;
v_res_463_ = l_Lean_Meta_Grind_getFnRoots(v_e_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
stack->m_obj
 = v_res_463_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Grind_getFnRoots(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
return v_res_476_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object* v_e_477_, lean_object* v_inst_478_, lean_object* v_a_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_477_, v_a_479_, v___y_480_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
return v___x_491_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_477_ = stack[0].m_obj;
lean_object* v_a_479_ = stack[2].m_obj;
lean_object* v___y_480_ = stack[3].m_obj;
lean_object* v___y_481_ = stack[4].m_obj;
lean_object* v___y_482_ = stack[5].m_obj;
lean_object* v___y_483_ = stack[6].m_obj;
lean_object* v___y_484_ = stack[7].m_obj;
lean_object* v___y_485_ = stack[8].m_obj;
lean_object* v___y_486_ = stack[9].m_obj;
lean_object* v___y_487_ = stack[10].m_obj;
lean_object* v___y_488_ = stack[11].m_obj;
lean_object* v___y_489_ = stack[12].m_obj;
lean_object* v_res_492_;
v_res_492_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(v_e_477_, lean_box(0), v_a_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
stack->m_obj
 = v_res_492_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object* v_e_493_, lean_object* v_inst_494_, lean_object* v_a_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(v_e_493_, v_inst_494_, v_a_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v_e_493_);
return v_res_507_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_, lean_object* v_b_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_a_515_; lean_object* v___y_520_; uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
v___x_524_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_523_, v___y_512_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; uint8_t v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v___x_526_ = lean_nat_dec_le(v_b_511_, v_a_525_);
if (v___x_526_ == 0)
{
lean_dec_ref_known(v___x_524_, 1);
v_a_515_ = v_b_511_;
goto v___jp_514_;
}
else
{
lean_dec(v_b_511_);
v___y_520_ = v___x_524_;
goto v___jp_519_;
}
}
else
{
lean_dec(v_b_511_);
v___y_520_ = v___x_524_;
goto v___jp_519_;
}
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_b_511_);
return v___x_527_;
}
v___jp_514_:
{
size_t v___x_516_; size_t v___x_517_; 
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_509_, v___x_516_);
v_i_509_ = v___x_517_;
v_b_511_ = v_a_515_;
goto _start;
}
v___jp_519_:
{
if (lean_obj_tag(v___y_520_) == 0)
{
lean_object* v_a_521_; 
v_a_521_ = lean_ctor_get(v___y_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___y_520_, 1);
v_a_515_ = v_a_521_;
goto v___jp_514_;
}
else
{
return v___y_520_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_508_ = stack[0].m_obj;
size_t v_i_509_ = stack[1].m_num;
size_t v_stop_510_ = stack[2].m_num;
lean_object* v_b_511_ = stack[3].m_obj;
lean_object* v___y_512_ = stack[4].m_obj;
lean_object* v_res_528_;
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_508_, v_i_509_, v_stop_510_, v_b_511_, v___y_512_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object* v_as_529_, lean_object* v_i_530_, lean_object* v_stop_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_531_);
lean_dec(v_stop_531_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_529_, v_i_boxed_535_, v_stop_boxed_536_, v_b_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v_as_529_);
return v_res_537_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(lean_object* v_msgData_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v_env_545_; uint8_t v___x_546_; lean_object* v_env_547_; lean_object* v___x_548_; lean_object* v_toCold_549_; lean_object* v_mctx_550_; lean_object* v_lctx_551_; lean_object* v_options_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_544_ = lean_st_ref_get(v___y_542_);
v_env_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_env_545_);
lean_dec(v___x_544_);
v___x_546_ = 0;
v_env_547_ = l_Lean_Environment_setRecordingDeps(v_env_545_, v___x_546_);
v___x_548_ = lean_st_ref_get(v___y_540_);
v_toCold_549_ = lean_ctor_get(v___y_541_, 0);
v_mctx_550_ = lean_ctor_get(v___x_548_, 0);
lean_inc_ref(v_mctx_550_);
lean_dec(v___x_548_);
v_lctx_551_ = lean_ctor_get(v___y_539_, 2);
v_options_552_ = lean_ctor_get(v_toCold_549_, 2);
lean_inc_ref(v_options_552_);
lean_inc_ref(v_lctx_551_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_env_547_);
lean_ctor_set(v___x_553_, 1, v_mctx_550_);
lean_ctor_set(v___x_553_, 2, v_lctx_551_);
lean_ctor_set(v___x_553_, 3, v_options_552_);
v___x_554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_msgData_538_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_538_ = stack[0].m_obj;
lean_object* v___y_539_ = stack[1].m_obj;
lean_object* v___y_540_ = stack[2].m_obj;
lean_object* v___y_541_ = stack[3].m_obj;
lean_object* v___y_542_ = stack[4].m_obj;
lean_object* v_res_556_;
v_res_556_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_564_; double v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_float_of_nat(v___x_564_);
return v___x_565_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object* v_cls_569_, lean_object* v_msg_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_ref_576_; lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_623_; 
v_ref_576_ = lean_ctor_get(v___y_573_, 2);
v___x_577_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_623_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_623_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_623_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v_traceState_583_; lean_object* v_env_584_; lean_object* v_nextMacroScope_585_; lean_object* v_ngen_586_; lean_object* v_auxDeclNGen_587_; lean_object* v_cache_588_; lean_object* v_recordedDeps_589_; lean_object* v_messages_590_; lean_object* v_infoState_591_; lean_object* v_snapshotTasks_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_622_; 
v___x_582_ = lean_st_ref_take(v___y_574_);
v_traceState_583_ = lean_ctor_get(v___x_582_, 4);
v_env_584_ = lean_ctor_get(v___x_582_, 0);
v_nextMacroScope_585_ = lean_ctor_get(v___x_582_, 1);
v_ngen_586_ = lean_ctor_get(v___x_582_, 2);
v_auxDeclNGen_587_ = lean_ctor_get(v___x_582_, 3);
v_cache_588_ = lean_ctor_get(v___x_582_, 5);
v_recordedDeps_589_ = lean_ctor_get(v___x_582_, 6);
v_messages_590_ = lean_ctor_get(v___x_582_, 7);
v_infoState_591_ = lean_ctor_get(v___x_582_, 8);
v_snapshotTasks_592_ = lean_ctor_get(v___x_582_, 9);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_622_ == 0)
{
v___x_594_ = v___x_582_;
v_isShared_595_ = v_isSharedCheck_622_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snapshotTasks_592_);
lean_inc(v_infoState_591_);
lean_inc(v_messages_590_);
lean_inc(v_recordedDeps_589_);
lean_inc(v_cache_588_);
lean_inc(v_traceState_583_);
lean_inc(v_auxDeclNGen_587_);
lean_inc(v_ngen_586_);
lean_inc(v_nextMacroScope_585_);
lean_inc(v_env_584_);
lean_dec(v___x_582_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_622_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint64_t v_tid_596_; lean_object* v_traces_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_621_; 
v_tid_596_ = lean_ctor_get_uint64(v_traceState_583_, sizeof(void*)*1);
v_traces_597_ = lean_ctor_get(v_traceState_583_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_traceState_583_);
if (v_isSharedCheck_621_ == 0)
{
v___x_599_ = v_traceState_583_;
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_traces_597_);
lean_dec(v_traceState_583_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_621_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; double v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_box(0);
v___x_603_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0);
v___x_604_ = 0;
v___x_605_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1));
v___x_606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_606_, 0, v_cls_569_);
lean_ctor_set(v___x_606_, 1, v___x_602_);
lean_ctor_set(v___x_606_, 2, v___x_605_);
lean_ctor_set_float(v___x_606_, sizeof(void*)*3, v___x_603_);
lean_ctor_set_float(v___x_606_, sizeof(void*)*3 + 8, v___x_603_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*3 + 16, v___x_604_);
v___x_607_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2));
v___x_608_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v_a_578_);
lean_ctor_set(v___x_608_, 2, v___x_607_);
lean_inc(v_ref_576_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v_ref_576_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_PersistentArray_push___redArg(v_traces_597_, v___x_609_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_610_);
v___x_612_ = v___x_599_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_610_);
lean_ctor_set_uint64(v_reuseFailAlloc_620_, sizeof(void*)*1, v_tid_596_);
v___x_612_ = v_reuseFailAlloc_620_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___x_612_);
v___x_614_ = v___x_594_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_env_584_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_nextMacroScope_585_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_ngen_586_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_auxDeclNGen_587_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_cache_588_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_recordedDeps_589_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v_messages_590_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v_infoState_591_);
lean_ctor_set(v_reuseFailAlloc_619_, 9, v_snapshotTasks_592_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_st_ref_put(v___y_574_, v___x_614_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_601_);
v___x_617_ = v___x_580_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_601_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_569_ = stack[0].m_obj;
lean_object* v_msg_570_ = stack[1].m_obj;
lean_object* v___y_571_ = stack[2].m_obj;
lean_object* v___y_572_ = stack[3].m_obj;
lean_object* v___y_573_ = stack[4].m_obj;
lean_object* v___y_574_ = stack[5].m_obj;
lean_object* v_res_624_;
v_res_624_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_569_, v_msg_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object* v_cls_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_625_, v_msg_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_632_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v_b_636_);
return v___x_643_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
lean_inc(v_a_644_);
v___x_645_ = l_Lean_Meta_mkCongrFun(v_b_636_, v_a_644_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; size_t v___x_647_; size_t v___x_648_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_645_, 1);
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_635_, v___x_647_);
v_i_635_ = v___x_648_;
v_b_636_ = v_a_646_;
goto _start;
}
else
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_633_ = stack[0].m_obj;
size_t v_sz_634_ = stack[1].m_num;
size_t v_i_635_ = stack[2].m_num;
lean_object* v_b_636_ = stack[3].m_obj;
lean_object* v___y_637_ = stack[4].m_obj;
lean_object* v___y_638_ = stack[5].m_obj;
lean_object* v___y_639_ = stack[6].m_obj;
lean_object* v___y_640_ = stack[7].m_obj;
lean_object* v_res_650_;
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_633_, v_sz_634_, v_i_635_, v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
stack->m_obj
 = v_res_650_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object* v_as_651_, lean_object* v_sz_652_, lean_object* v_i_653_, lean_object* v_b_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
size_t v_sz_boxed_660_; size_t v_i_boxed_661_; lean_object* v_res_662_; 
v_sz_boxed_660_ = lean_unbox_usize(v_sz_652_);
lean_dec(v_sz_652_);
v_i_boxed_661_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_651_, v_sz_boxed_660_, v_i_boxed_661_, v_b_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v_as_651_);
return v_res_662_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5));
v___x_676_ = l_Lean_Name_append(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object* v_args_685_, lean_object* v_f_686_, lean_object* v_as_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_b_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_a_703_; uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_b_690_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; lean_object* v_a_710_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___x_736_; lean_object* v_a_738_; lean_object* v___y_836_; uint8_t v___x_846_; 
lean_dec_ref(v_b_690_);
v___x_709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_a_710_ = lean_array_uget_borrowed(v_as_687_, v_i_689_);
lean_inc_ref(v_args_685_);
lean_inc(v_a_710_);
v___x_736_ = l_Lean_Expr_beta(v_a_710_, v_args_685_);
v___x_846_ = l_Lean_Expr_isLambda(v___x_736_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_710_, v___y_691_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = l_Lean_Meta_Grind_getGeneration___redArg(v_f_686_, v___y_691_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___y_852_; uint8_t v___x_863_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_863_ = lean_nat_dec_le(v_a_848_, v_a_850_);
if (v___x_863_ == 0)
{
lean_dec(v_a_850_);
v___y_852_ = v_a_848_;
goto v___jp_851_;
}
else
{
lean_dec(v_a_848_);
v___y_852_ = v_a_850_;
goto v___jp_851_;
}
v___jp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_array_get_size(v_args_685_);
v___x_855_ = lean_nat_dec_lt(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
v_a_738_ = v___y_852_;
goto v___jp_737_;
}
else
{
uint8_t v___x_856_; 
v___x_856_ = lean_nat_dec_le(v___x_854_, v___x_854_);
if (v___x_856_ == 0)
{
if (v___x_855_ == 0)
{
v_a_738_ = v___y_852_;
goto v___jp_737_;
}
else
{
size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; 
v___x_857_ = ((size_t)0ULL);
v___x_858_ = lean_usize_of_nat(v___x_854_);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_685_, v___x_857_, v___x_858_, v___y_852_, v___y_691_);
v___y_836_ = v___x_859_;
goto v___jp_835_;
}
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_854_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_685_, v___x_860_, v___x_861_, v___y_852_, v___y_691_);
v___y_836_ = v___x_862_;
goto v___jp_835_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_848_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_864_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_849_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_849_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_872_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_847_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_847_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_dec_ref(v___x_736_);
v_a_703_ = v___x_709_;
goto v___jp_702_;
}
v___jp_711_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc(v_a_710_);
v___x_725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_725_, 0, v_a_710_);
v___x_726_ = lean_box(1);
v___x_727_ = l_Lean_Meta_Grind_addNewRawFact(v___y_712_, v___y_713_, v___y_714_, v___x_725_, v___x_726_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_dec_ref_known(v___x_727_, 1);
v_a_703_ = v___x_709_;
goto v___jp_702_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_add(v_a_738_, v___x_739_);
lean_dec(v_a_738_);
v___x_741_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_693_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_826_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_826_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_826_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_826_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_le(v_a_742_, v___x_740_);
lean_dec(v_a_742_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_del_object(v___x_744_);
lean_inc_ref_n(v_f_686_, 2);
v___x_747_ = l_Lean_mkAppN(v_f_686_, v_args_685_);
lean_inc(v_a_710_);
v___x_748_ = l_Lean_Meta_Grind_hasSameType(v_f_686_, v_a_710_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; uint8_t v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = lean_unbox(v_a_749_);
lean_dec(v_a_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
v_a_703_ = v___x_709_;
goto v___jp_702_;
}
else
{
lean_object* v___x_751_; 
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc(v___y_691_);
lean_inc(v_a_710_);
lean_inc_ref(v_f_686_);
v___x_751_ = lean_grind_mk_eq_proof(v_f_686_, v_a_710_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_sz_753_ = lean_array_size(v_args_685_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_685_, v_sz_753_, v___x_754_, v_a_752_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = l_Lean_Meta_mkEq(v___x_747_, v___x_736_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_toCold_758_; lean_object* v_options_759_; uint8_t v_hasTrace_760_; 
v_toCold_758_ = lean_ctor_get(v___y_699_, 0);
v_options_759_ = lean_ctor_get(v_toCold_758_, 2);
v_hasTrace_760_ = lean_ctor_get_uint8(v_options_759_, sizeof(void*)*1);
if (v_hasTrace_760_ == 0)
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_757_, 1);
v___y_712_ = v_a_756_;
v___y_713_ = v_a_761_;
v___y_714_ = v___x_740_;
v___y_715_ = v___y_691_;
v___y_716_ = v___y_692_;
v___y_717_ = v___y_693_;
v___y_718_ = v___y_694_;
v___y_719_ = v___y_695_;
v___y_720_ = v___y_696_;
v___y_721_ = v___y_697_;
v___y_722_ = v___y_698_;
v___y_723_ = v___y_699_;
v___y_724_ = v___y_700_;
goto v___jp_711_;
}
else
{
lean_object* v_a_762_; lean_object* v_inheritedTraceOptions_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_a_762_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_757_, 1);
v_inheritedTraceOptions_763_ = lean_ctor_get(v_toCold_758_, 11);
v___x_764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6);
v___x_766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_763_, v_options_759_, v___x_765_);
if (v___x_766_ == 0)
{
v___y_712_ = v_a_756_;
v___y_713_ = v_a_762_;
v___y_714_ = v___x_740_;
v___y_715_ = v___y_691_;
v___y_716_ = v___y_692_;
v___y_717_ = v___y_693_;
v___y_718_ = v___y_694_;
v___y_719_ = v___y_695_;
v___y_720_ = v___y_696_;
v___y_721_ = v___y_697_;
v___y_722_ = v___y_698_;
v___y_723_ = v___y_699_;
v___y_724_ = v___y_700_;
goto v___jp_711_;
}
else
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Grind_updateLastTag(v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref_known(v___x_767_, 1);
lean_inc(v_a_762_);
v___x_768_ = l_Lean_MessageData_ofExpr(v_a_762_);
v___x_769_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_inc(v_a_710_);
v___x_771_ = l_Lean_MessageData_ofExpr(v_a_710_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_764_, v___x_772_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec_ref_known(v___x_773_, 1);
v___y_712_ = v_a_756_;
v___y_713_ = v_a_762_;
v___y_714_ = v___x_740_;
v___y_715_ = v___y_691_;
v___y_716_ = v___y_692_;
v___y_717_ = v___y_693_;
v___y_718_ = v___y_694_;
v___y_719_ = v___y_695_;
v___y_720_ = v___y_696_;
v___y_721_ = v___y_697_;
v___y_722_ = v___y_698_;
v___y_723_ = v___y_699_;
v___y_724_ = v___y_700_;
goto v___jp_711_;
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_762_);
lean_dec(v_a_756_);
lean_dec(v___x_740_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_762_);
lean_dec(v_a_756_);
lean_dec(v___x_740_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_782_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_767_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_767_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v_a_756_);
lean_dec(v___x_740_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_790_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_757_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_757_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_798_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_755_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_755_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_806_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_751_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_751_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v___x_747_);
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_814_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_748_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_748_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v___x_822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10));
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_822_);
v___x_824_ = v___x_744_;
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
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___x_740_);
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_827_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_741_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_741_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
v___jp_835_:
{
if (lean_obj_tag(v___y_836_) == 0)
{
lean_object* v_a_837_; 
v_a_837_ = lean_ctor_get(v___y_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___y_836_, 1);
v_a_738_ = v_a_837_;
goto v___jp_737_;
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v___x_736_);
lean_dec_ref(v_f_686_);
lean_dec_ref(v_args_685_);
v_a_838_ = lean_ctor_get(v___y_836_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___y_836_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___y_836_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___y_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
v___jp_702_:
{
size_t v___x_704_; size_t v___x_705_; 
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_689_, v___x_704_);
lean_inc_ref(v_a_703_);
v_i_689_ = v___x_705_;
v_b_690_ = v_a_703_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_685_ = stack[0].m_obj;
lean_object* v_f_686_ = stack[1].m_obj;
lean_object* v_as_687_ = stack[2].m_obj;
size_t v_sz_688_ = stack[3].m_num;
size_t v_i_689_ = stack[4].m_num;
lean_object* v_b_690_ = stack[5].m_obj;
lean_object* v___y_691_ = stack[6].m_obj;
lean_object* v___y_692_ = stack[7].m_obj;
lean_object* v___y_693_ = stack[8].m_obj;
lean_object* v___y_694_ = stack[9].m_obj;
lean_object* v___y_695_ = stack[10].m_obj;
lean_object* v___y_696_ = stack[11].m_obj;
lean_object* v___y_697_ = stack[12].m_obj;
lean_object* v___y_698_ = stack[13].m_obj;
lean_object* v___y_699_ = stack[14].m_obj;
lean_object* v___y_700_ = stack[15].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_685_, v_f_686_, v_as_687_, v_sz_688_, v_i_689_, v_b_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object** _args){
lean_object* v_args_881_ = _args[0];
lean_object* v_f_882_ = _args[1];
lean_object* v_as_883_ = _args[2];
lean_object* v_sz_884_ = _args[3];
lean_object* v_i_885_ = _args[4];
lean_object* v_b_886_ = _args[5];
lean_object* v___y_887_ = _args[6];
lean_object* v___y_888_ = _args[7];
lean_object* v___y_889_ = _args[8];
lean_object* v___y_890_ = _args[9];
lean_object* v___y_891_ = _args[10];
lean_object* v___y_892_ = _args[11];
lean_object* v___y_893_ = _args[12];
lean_object* v___y_894_ = _args[13];
lean_object* v___y_895_ = _args[14];
lean_object* v___y_896_ = _args[15];
lean_object* v___y_897_ = _args[16];
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_884_);
lean_dec(v_sz_884_);
v_i_boxed_899_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_881_, v_f_882_, v_as_883_, v_sz_boxed_898_, v_i_boxed_899_, v_b_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v_as_883_);
return v_res_900_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object* v_lams_901_, lean_object* v_f_902_, lean_object* v_args_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_array_get_size(v_args_903_);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_nat_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v___x_922_; 
v___x_918_ = lean_box(0);
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_sz_920_ = lean_array_size(v_lams_901_);
v___x_921_ = ((size_t)0ULL);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_903_, v_f_902_, v_lams_901_, v_sz_920_, v___x_921_, v___x_919_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v_fst_927_; 
v_fst_927_ = lean_ctor_get(v_a_923_, 0);
lean_inc(v_fst_927_);
lean_dec(v_a_923_);
if (lean_obj_tag(v_fst_927_) == 0)
{
lean_object* v___x_929_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_918_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_918_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
else
{
lean_object* v_val_931_; lean_object* v___x_933_; 
v_val_931_ = lean_ctor_get(v_fst_927_, 0);
lean_inc(v_val_931_);
lean_dec_ref_known(v_fst_927_, 1);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v_val_931_);
v___x_933_ = v___x_925_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_val_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_922_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_922_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec_ref(v_args_903_);
lean_dec_ref(v_f_902_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBetaEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_lams_901_ = stack[0].m_obj;
lean_object* v_f_902_ = stack[1].m_obj;
lean_object* v_args_903_ = stack[2].m_obj;
lean_object* v_a_904_ = stack[3].m_obj;
lean_object* v_a_905_ = stack[4].m_obj;
lean_object* v_a_906_ = stack[5].m_obj;
lean_object* v_a_907_ = stack[6].m_obj;
lean_object* v_a_908_ = stack[7].m_obj;
lean_object* v_a_909_ = stack[8].m_obj;
lean_object* v_a_910_ = stack[9].m_obj;
lean_object* v_a_911_ = stack[10].m_obj;
lean_object* v_a_912_ = stack[11].m_obj;
lean_object* v_a_913_ = stack[12].m_obj;
lean_object* v_res_946_;
v_res_946_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_901_, v_f_902_, v_args_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object* v_lams_947_, lean_object* v_f_948_, lean_object* v_args_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_947_, v_f_948_, v_args_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_lams_947_);
return v_res_961_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object* v_as_962_, size_t v_sz_963_, size_t v_i_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_962_, v_sz_963_, v_i_964_, v_b_965_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_962_ = stack[0].m_obj;
size_t v_sz_963_ = stack[1].m_num;
size_t v_i_964_ = stack[2].m_num;
lean_object* v_b_965_ = stack[3].m_obj;
lean_object* v___y_966_ = stack[4].m_obj;
lean_object* v___y_967_ = stack[5].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v___y_969_ = stack[7].m_obj;
lean_object* v___y_970_ = stack[8].m_obj;
lean_object* v___y_971_ = stack[9].m_obj;
lean_object* v___y_972_ = stack[10].m_obj;
lean_object* v___y_973_ = stack[11].m_obj;
lean_object* v___y_974_ = stack[12].m_obj;
lean_object* v___y_975_ = stack[13].m_obj;
lean_object* v_res_978_;
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_962_, v_sz_963_, v_i_964_, v_b_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object* v_as_979_, lean_object* v_sz_980_, lean_object* v_i_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
size_t v_sz_boxed_994_; size_t v_i_boxed_995_; lean_object* v_res_996_; 
v_sz_boxed_994_ = lean_unbox_usize(v_sz_980_);
lean_dec(v_sz_980_);
v_i_boxed_995_ = lean_unbox_usize(v_i_981_);
lean_dec(v_i_981_);
v_res_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_979_, v_sz_boxed_994_, v_i_boxed_995_, v_b_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
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
lean_dec_ref(v_as_979_);
return v_res_996_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object* v_cls_997_, lean_object* v_msg_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_997_, v_msg_998_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_997_ = stack[0].m_obj;
lean_object* v_msg_998_ = stack[1].m_obj;
lean_object* v___y_999_ = stack[2].m_obj;
lean_object* v___y_1000_ = stack[3].m_obj;
lean_object* v___y_1001_ = stack[4].m_obj;
lean_object* v___y_1002_ = stack[5].m_obj;
lean_object* v___y_1003_ = stack[6].m_obj;
lean_object* v___y_1004_ = stack[7].m_obj;
lean_object* v___y_1005_ = stack[8].m_obj;
lean_object* v___y_1006_ = stack[9].m_obj;
lean_object* v___y_1007_ = stack[10].m_obj;
lean_object* v___y_1008_ = stack[11].m_obj;
lean_object* v_res_1011_;
v_res_1011_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_997_, v_msg_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
stack->m_obj
 = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object* v_cls_1012_, lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_1012_, v_msg_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
return v_res_1025_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object* v_as_1026_, size_t v_i_1027_, size_t v_stop_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_1026_, v_i_1027_, v_stop_1028_, v_b_1029_, v___y_1030_);
return v___x_1041_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1026_ = stack[0].m_obj;
size_t v_i_1027_ = stack[1].m_num;
size_t v_stop_1028_ = stack[2].m_num;
lean_object* v_b_1029_ = stack[3].m_obj;
lean_object* v___y_1030_ = stack[4].m_obj;
lean_object* v___y_1031_ = stack[5].m_obj;
lean_object* v___y_1032_ = stack[6].m_obj;
lean_object* v___y_1033_ = stack[7].m_obj;
lean_object* v___y_1034_ = stack[8].m_obj;
lean_object* v___y_1035_ = stack[9].m_obj;
lean_object* v___y_1036_ = stack[10].m_obj;
lean_object* v___y_1037_ = stack[11].m_obj;
lean_object* v___y_1038_ = stack[12].m_obj;
lean_object* v___y_1039_ = stack[13].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_as_1026_, v_i_1027_, v_stop_1028_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object* v_as_1043_, lean_object* v_i_1044_, lean_object* v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
size_t v_i_boxed_1058_; size_t v_stop_boxed_1059_; lean_object* v_res_1060_; 
v_i_boxed_1058_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_stop_boxed_1059_ = lean_unbox_usize(v_stop_1045_);
lean_dec(v_stop_1045_);
v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_as_1043_, v_i_boxed_1058_, v_stop_boxed_1059_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v_as_1043_);
return v_res_1060_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object* v_f_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
if (lean_obj_tag(v_a_1090_) == 1)
{
lean_object* v_val_1094_; uint8_t v_hasLambdas_1095_; 
v_val_1094_ = lean_ctor_get(v_a_1090_, 0);
lean_inc(v_val_1094_);
lean_dec_ref_known(v_a_1090_, 1);
v_hasLambdas_1095_ = lean_ctor_get_uint8(v_val_1094_, sizeof(void*)*12 + 3);
lean_dec(v_val_1094_);
if (v_hasLambdas_1095_ == 0)
{
lean_del_object(v___x_1092_);
v___y_1074_ = v_a_1062_;
v___y_1075_ = v_a_1063_;
v___y_1076_ = v_a_1064_;
v___y_1077_ = v_a_1065_;
v___y_1078_ = v_a_1066_;
v___y_1079_ = v_a_1067_;
v___y_1080_ = v_a_1068_;
v___y_1081_ = v_a_1069_;
v___y_1082_ = v_a_1070_;
v___y_1083_ = v_a_1071_;
goto v___jp_1073_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_box(v_hasLambdas_1095_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1096_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_del_object(v___x_1092_);
lean_dec(v_a_1090_);
v___y_1074_ = v_a_1062_;
v___y_1075_ = v_a_1063_;
v___y_1076_ = v_a_1064_;
v___y_1077_ = v_a_1065_;
v___y_1078_ = v_a_1066_;
v___y_1079_ = v_a_1067_;
v___y_1080_ = v_a_1068_;
v___y_1081_ = v_a_1069_;
v___y_1082_ = v_a_1070_;
v___y_1083_ = v_a_1071_;
goto v___jp_1073_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1089_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1089_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
v___jp_1073_:
{
if (lean_obj_tag(v_f_1061_) == 5)
{
lean_object* v_fn_1084_; 
v_fn_1084_ = lean_ctor_get(v_f_1061_, 0);
v_f_1061_ = v_fn_1084_;
v_a_1062_ = v___y_1074_;
v_a_1063_ = v___y_1075_;
v_a_1064_ = v___y_1076_;
v_a_1065_ = v___y_1077_;
v_a_1066_ = v___y_1078_;
v_a_1067_ = v___y_1079_;
v_a_1068_ = v___y_1080_;
v_a_1069_ = v___y_1081_;
v_a_1070_ = v___y_1082_;
v_a_1071_ = v___y_1083_;
goto _start;
}
else
{
uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = 0;
v___x_1087_ = lean_box(v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1061_ = stack[0].m_obj;
lean_object* v_a_1062_ = stack[1].m_obj;
lean_object* v_a_1063_ = stack[2].m_obj;
lean_object* v_a_1064_ = stack[3].m_obj;
lean_object* v_a_1065_ = stack[4].m_obj;
lean_object* v_a_1066_ = stack[5].m_obj;
lean_object* v_a_1067_ = stack[6].m_obj;
lean_object* v_a_1068_ = stack[7].m_obj;
lean_object* v_a_1069_ = stack[8].m_obj;
lean_object* v_a_1070_ = stack[9].m_obj;
lean_object* v_a_1071_ = stack[10].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_f_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go___boxed(lean_object* v_f_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_f_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_f_1110_);
return v_res_1122_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(lean_object* v_e_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
if (lean_obj_tag(v_e_1123_) == 5)
{
lean_object* v_fn_1135_; lean_object* v___x_1136_; 
v_fn_1135_ = lean_ctor_get(v_e_1123_, 0);
v___x_1136_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(v_fn_1135_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1136_;
}
else
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = 0;
v___x_1138_ = lean_box(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1123_ = stack[0].m_obj;
lean_object* v_a_1124_ = stack[1].m_obj;
lean_object* v_a_1125_ = stack[2].m_obj;
lean_object* v_a_1126_ = stack[3].m_obj;
lean_object* v_a_1127_ = stack[4].m_obj;
lean_object* v_a_1128_ = stack[5].m_obj;
lean_object* v_a_1129_ = stack[6].m_obj;
lean_object* v_a_1130_ = stack[7].m_obj;
lean_object* v_a_1131_ = stack[8].m_obj;
lean_object* v_a_1132_ = stack[9].m_obj;
lean_object* v_a_1133_ = stack[10].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget___boxed(lean_object* v_e_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_e_1141_);
return v_res_1153_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(lean_object* v_fst_1154_, lean_object* v_snd_1155_, lean_object* v___x_1156_, lean_object* v_____r_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
if (lean_obj_tag(v_fst_1154_) == 5)
{
lean_object* v_fn_1169_; lean_object* v_arg_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_fn_1169_ = lean_ctor_get(v_fst_1154_, 0);
lean_inc_ref(v_fn_1169_);
v_arg_1170_ = lean_ctor_get(v_fst_1154_, 1);
lean_inc_ref(v_arg_1170_);
lean_dec_ref_known(v_fst_1154_, 2);
v___x_1171_ = lean_array_push(v_snd_1155_, v_arg_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_fn_1169_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1156_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v___x_1156_);
v___x_1176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9));
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_fst_1154_);
lean_ctor_set(v___x_1177_, 1, v_snd_1155_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1154_ = stack[0].m_obj;
lean_object* v_snd_1155_ = stack[1].m_obj;
lean_object* v___x_1156_ = stack[2].m_obj;
lean_object* v_____r_1157_ = stack[3].m_obj;
lean_object* v___y_1158_ = stack[4].m_obj;
lean_object* v___y_1159_ = stack[5].m_obj;
lean_object* v___y_1160_ = stack[6].m_obj;
lean_object* v___y_1161_ = stack[7].m_obj;
lean_object* v___y_1162_ = stack[8].m_obj;
lean_object* v___y_1163_ = stack[9].m_obj;
lean_object* v___y_1164_ = stack[10].m_obj;
lean_object* v___y_1165_ = stack[11].m_obj;
lean_object* v___y_1166_ = stack[12].m_obj;
lean_object* v___y_1167_ = stack[13].m_obj;
lean_object* v_res_1181_;
v_res_1181_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1154_, v_snd_1155_, v___x_1156_, v_____r_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
stack->m_obj
 = v_res_1181_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0___boxed(lean_object* v_fst_1182_, lean_object* v_snd_1183_, lean_object* v___x_1184_, lean_object* v_____r_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1182_, v_snd_1183_, v___x_1184_, v_____r_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1197_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(lean_object* v_a_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___y_1211_; lean_object* v_snd_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_snd_1231_ = lean_ctor_get(v_a_1198_, 1);
lean_inc(v_snd_1231_);
lean_dec_ref(v_a_1198_);
v_fst_1232_ = lean_ctor_get(v_snd_1231_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v_snd_1231_, 1);
lean_inc(v_snd_1233_);
lean_dec(v_snd_1231_);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_array_get_size(v_snd_1233_);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_nat_dec_eq(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_1232_, v___y_1199_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
if (lean_obj_tag(v_a_1239_) == 1)
{
lean_object* v_val_1240_; uint8_t v_hasLambdas_1241_; 
v_val_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_a_1239_, 1);
v_hasLambdas_1241_ = lean_ctor_get_uint8(v_val_1240_, sizeof(void*)*12 + 3);
if (v_hasLambdas_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec(v_val_1240_);
v___x_1242_ = lean_box(0);
v___x_1243_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1232_, v_snd_1233_, v___x_1234_, v___x_1242_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1211_ = v___x_1243_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Meta_Grind_getEqcLambdas(v_val_1240_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v_val_1240_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
lean_inc(v_snd_1233_);
v___x_1246_ = l_Array_reverse___redArg(v_snd_1233_);
lean_inc(v_fst_1232_);
v___x_1247_ = l_Lean_Meta_Grind_propagateBetaEqs(v_a_1245_, v_fst_1232_, v___x_1246_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v_a_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1232_, v_snd_1233_, v___x_1234_, v_a_1248_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1211_ = v___x_1249_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v_snd_1233_);
lean_dec(v_fst_1232_);
v_a_1250_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1247_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_snd_1233_);
lean_dec(v_fst_1232_);
v_a_1258_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1244_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1244_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_dec(v_a_1239_);
v___x_1266_ = lean_box(0);
v___x_1267_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1232_, v_snd_1233_, v___x_1234_, v___x_1266_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1211_ = v___x_1267_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_snd_1233_);
lean_dec(v_fst_1232_);
v_a_1268_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1238_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1238_);
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
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_box(0);
v___x_1277_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1232_, v_snd_1233_, v___x_1234_, v___x_1276_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
v___y_1211_ = v___x_1277_;
goto v___jp_1210_;
}
v___jp_1210_:
{
if (lean_obj_tag(v___y_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v_a_1212_ = lean_ctor_get(v___y_1211_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___y_1211_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1214_ = v___y_1211_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___y_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
if (lean_obj_tag(v_a_1212_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v_a_1212_, 1);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_a_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
else
{
lean_object* v_a_1220_; 
lean_del_object(v___x_1214_);
v_a_1220_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v_a_1212_, 1);
v_a_1198_ = v_a_1220_;
goto _start;
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___y_1211_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___y_1211_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___y_1211_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___y_1211_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1198_ = stack[0].m_obj;
lean_object* v___y_1199_ = stack[1].m_obj;
lean_object* v___y_1200_ = stack[2].m_obj;
lean_object* v___y_1201_ = stack[3].m_obj;
lean_object* v___y_1202_ = stack[4].m_obj;
lean_object* v___y_1203_ = stack[5].m_obj;
lean_object* v___y_1204_ = stack[6].m_obj;
lean_object* v___y_1205_ = stack[7].m_obj;
lean_object* v___y_1206_ = stack[8].m_obj;
lean_object* v___y_1207_ = stack[9].m_obj;
lean_object* v___y_1208_ = stack[10].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___boxed(lean_object* v_a_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
return v_res_1291_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1341_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1341_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1341_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_dec_ref(v_e_1292_);
v___x_1310_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1307_);
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_e_1292_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v___x_1317_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1332_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1332_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1332_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; 
v_fst_1323_ = lean_ctor_get(v_a_1319_, 0);
lean_inc(v_fst_1323_);
lean_dec(v_a_1319_);
if (lean_obj_tag(v_fst_1323_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_box(0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1324_);
v___x_1326_ = v___x_1321_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1330_; 
v_val_1328_ = lean_ctor_get(v_fst_1323_, 0);
lean_inc(v_val_1328_);
lean_dec_ref_known(v_fst_1323_, 1);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v_val_1328_);
v___x_1330_ = v___x_1321_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_val_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1318_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1318_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v_e_1292_);
v_a_1342_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1304_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1304_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBetaForNewApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1292_ = stack[0].m_obj;
lean_object* v_a_1293_ = stack[1].m_obj;
lean_object* v_a_1294_ = stack[2].m_obj;
lean_object* v_a_1295_ = stack[3].m_obj;
lean_object* v_a_1296_ = stack[4].m_obj;
lean_object* v_a_1297_ = stack[5].m_obj;
lean_object* v_a_1298_ = stack[6].m_obj;
lean_object* v_a_1299_ = stack[7].m_obj;
lean_object* v_a_1300_ = stack[8].m_obj;
lean_object* v_a_1301_ = stack[9].m_obj;
lean_object* v_a_1302_ = stack[10].m_obj;
lean_object* v_res_1350_;
v_res_1350_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
stack->m_obj
 = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object* v_e_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec(v_a_1352_);
return v_res_1363_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object* v_inst_1364_, lean_object* v_a_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1365_ = stack[1].m_obj;
lean_object* v___y_1366_ = stack[2].m_obj;
lean_object* v___y_1367_ = stack[3].m_obj;
lean_object* v___y_1368_ = stack[4].m_obj;
lean_object* v___y_1369_ = stack[5].m_obj;
lean_object* v___y_1370_ = stack[6].m_obj;
lean_object* v___y_1371_ = stack[7].m_obj;
lean_object* v___y_1372_ = stack[8].m_obj;
lean_object* v___y_1373_ = stack[9].m_obj;
lean_object* v___y_1374_ = stack[10].m_obj;
lean_object* v___y_1375_ = stack[11].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_box(0), v_a_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object* v_inst_1379_, lean_object* v_a_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_inst_1379_, v_a_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
return v_res_1392_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
