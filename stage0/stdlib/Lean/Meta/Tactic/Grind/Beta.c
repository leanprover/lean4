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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(lean_object* v___x_102_, lean_object* v_a_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_snd_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_162_; 
v_snd_110_ = lean_ctor_get(v_a_103_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_103_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v_a_103_, 0);
lean_dec(v_unused_163_);
v___x_112_ = v_a_103_;
v_isShared_113_ = v_isSharedCheck_162_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_snd_110_);
lean_dec(v_a_103_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_162_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_fst_114_; lean_object* v_snd_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_161_; 
v_fst_114_ = lean_ctor_get(v_snd_110_, 0);
v_snd_115_ = lean_ctor_get(v_snd_110_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_snd_110_);
if (v_isSharedCheck_161_ == 0)
{
v___x_117_ = v_snd_110_;
v_isShared_118_ = v_isSharedCheck_161_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_snd_115_);
lean_inc(v_fst_114_);
lean_dec(v_snd_110_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_161_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_box(0);
v___x_120_ = lean_st_ref_get(v___y_104_);
lean_inc(v_fst_114_);
v___x_121_ = l_Lean_Meta_Grind_Goal_getENode(v___x_120_, v_fst_114_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___x_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_152_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_152_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_152_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_152_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_self_126_; lean_object* v_next_127_; lean_object* v_a_129_; uint8_t v___x_150_; 
v_self_126_ = lean_ctor_get(v_a_122_, 0);
lean_inc_ref(v_self_126_);
v_next_127_ = lean_ctor_get(v_a_122_, 1);
lean_inc_ref(v_next_127_);
lean_dec(v_a_122_);
v___x_150_ = l_Lean_Expr_isLambda(v_self_126_);
if (v___x_150_ == 0)
{
lean_dec_ref(v_self_126_);
v_a_129_ = v_snd_115_;
goto v___jp_128_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = lean_array_push(v_snd_115_, v_self_126_);
v_a_129_ = v___x_151_;
goto v___jp_128_;
}
v___jp_128_:
{
size_t v___x_130_; size_t v___x_131_; uint8_t v___x_132_; 
v___x_130_ = lean_ptr_addr(v_next_127_);
v___x_131_ = lean_ptr_addr(v___x_102_);
v___x_132_ = lean_usize_dec_eq(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_134_; 
lean_del_object(v___x_124_);
lean_dec(v_fst_114_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_a_129_);
lean_ctor_set(v___x_117_, 0, v_next_127_);
v___x_134_ = v___x_117_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_next_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_a_129_);
v___x_134_ = v_reuseFailAlloc_139_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___x_134_);
lean_ctor_set(v___x_112_, 0, v___x_119_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_a_103_ = v___x_136_;
goto _start;
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_142_; 
lean_dec_ref(v_next_127_);
lean_inc_ref(v_a_129_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_a_129_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v_a_129_);
v___x_142_ = v___x_117_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_114_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_a_129_);
v___x_142_ = v_reuseFailAlloc_149_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 1, v___x_142_);
lean_ctor_set(v___x_112_, 0, v___x_140_);
v___x_144_ = v___x_112_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_144_);
v___x_146_ = v___x_124_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_del_object(v___x_117_);
lean_dec(v_snd_115_);
lean_dec(v_fst_114_);
lean_del_object(v___x_112_);
v_a_153_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_121_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_121_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg___boxed(lean_object* v___x_164_, lean_object* v_a_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_164_, v_a_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___x_164_);
return v_res_172_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_178_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__3));
v___x_179_ = lean_unsigned_to_nat(2u);
v___x_180_ = lean_unsigned_to_nat(1652u);
v___x_181_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__2));
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__1));
v___x_183_ = l_mkPanicMessageWithDecl(v___x_182_, v___x_181_, v___x_180_, v___x_179_, v___x_178_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas(lean_object* v_root_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
uint8_t v_hasLambdas_196_; 
v_hasLambdas_196_ = lean_ctor_get_uint8(v_root_184_, sizeof(void*)*12 + 3);
if (v_hasLambdas_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_self_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_self_199_ = lean_ctor_get(v_root_184_, 0);
v___x_200_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_201_ = lean_box(0);
lean_inc_ref(v_self_199_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_self_199_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v_self_199_, v___x_203_, v_a_185_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_234_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_234_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_234_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_234_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_fst_209_; 
v_fst_209_ = lean_ctor_get(v_a_205_, 0);
if (lean_obj_tag(v_fst_209_) == 0)
{
lean_object* v_snd_210_; lean_object* v_snd_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_del_object(v___x_207_);
v_snd_210_ = lean_ctor_get(v_a_205_, 1);
lean_inc(v_snd_210_);
lean_dec(v_a_205_);
v_snd_211_ = lean_ctor_get(v_snd_210_, 1);
lean_inc(v_snd_211_);
lean_dec(v_snd_210_);
v___x_212_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_213_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_212_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_220_ == 0)
{
lean_object* v_unused_221_; 
v_unused_221_ = lean_ctor_get(v___x_213_, 0);
lean_dec(v_unused_221_);
v___x_215_ = v___x_213_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_dec(v___x_213_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v_snd_211_);
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_snd_211_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec(v_snd_211_);
v_a_222_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_213_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_213_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_val_230_; lean_object* v___x_232_; 
lean_inc_ref(v_fst_209_);
lean_dec(v_a_205_);
v_val_230_ = lean_ctor_get(v_fst_209_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v_fst_209_, 1);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v_val_230_);
v___x_232_ = v___x_207_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_val_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
v_a_235_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_204_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_204_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEqcLambdas___boxed(lean_object* v_root_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Grind_getEqcLambdas(v_root_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec(v_a_251_);
lean_dec_ref(v_a_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_a_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_root_243_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(lean_object* v___x_256_, lean_object* v_inst_257_, lean_object* v_a_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___redArg(v___x_256_, v_a_258_, v___y_259_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0___boxed(lean_object* v___x_271_, lean_object* v_inst_272_, lean_object* v_a_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getEqcLambdas_spec__0(v___x_271_, v_inst_272_, v_a_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___x_271_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(lean_object* v___y_289_, lean_object* v_as_290_, size_t v_sz_291_, size_t v_i_292_, lean_object* v_b_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_lt(v_i_292_, v_sz_291_);
if (v___x_294_ == 0)
{
lean_inc_ref(v_b_293_);
return v_b_293_;
}
else
{
lean_object* v___x_295_; lean_object* v_a_296_; size_t v___x_297_; size_t v___x_298_; uint8_t v___x_299_; 
v___x_295_ = lean_box(0);
v_a_296_ = lean_array_uget_borrowed(v_as_290_, v_i_292_);
v___x_297_ = lean_ptr_addr(v_a_296_);
v___x_298_ = lean_ptr_addr(v___y_289_);
v___x_299_ = lean_usize_dec_eq(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; size_t v___x_301_; size_t v___x_302_; 
v___x_300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___closed__0));
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_add(v_i_292_, v___x_301_);
v_i_292_ = v___x_302_;
v_b_293_ = v___x_300_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc(v_a_296_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_a_296_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_295_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0___boxed(lean_object* v___y_307_, lean_object* v_as_308_, lean_object* v_sz_309_, lean_object* v_i_310_, lean_object* v_b_311_){
_start:
{
size_t v_sz_boxed_312_; size_t v_i_boxed_313_; lean_object* v_res_314_; 
v_sz_boxed_312_ = lean_unbox_usize(v_sz_309_);
lean_dec(v_sz_309_);
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_307_, v_as_308_, v_sz_boxed_312_, v_i_boxed_313_, v_b_311_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_as_308_);
lean_dec_ref(v___y_307_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(lean_object* v_e_318_, lean_object* v_a_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_snd_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_391_; 
v_snd_326_ = lean_ctor_get(v_a_319_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_a_319_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_a_319_, 0);
lean_dec(v_unused_392_);
v___x_328_ = v_a_319_;
v_isShared_329_ = v_isSharedCheck_391_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_snd_326_);
lean_dec(v_a_319_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_391_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_390_; 
v_fst_330_ = lean_ctor_get(v_snd_326_, 0);
v_snd_331_ = lean_ctor_get(v_snd_326_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_390_ == 0)
{
v___x_333_ = v_snd_326_;
v_isShared_334_ = v_isSharedCheck_390_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_330_);
lean_dec(v_snd_326_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_390_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_st_ref_get(v___y_320_);
lean_inc(v_fst_330_);
v___x_337_ = l_Lean_Meta_Grind_Goal_getENode(v___x_336_, v_fst_330_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_381_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_381_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_381_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_381_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_self_342_; lean_object* v_next_343_; lean_object* v_a_345_; lean_object* v_fn_366_; lean_object* v___x_367_; lean_object* v___y_369_; lean_object* v___y_372_; lean_object* v___x_379_; 
v_self_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc_ref(v_self_342_);
v_next_343_ = lean_ctor_get(v_a_338_, 1);
lean_inc_ref(v_next_343_);
lean_dec(v_a_338_);
v_fn_366_ = l_Lean_Expr_getAppFn(v_self_342_);
lean_dec_ref(v_self_342_);
v___x_367_ = lean_st_ref_get(v___y_320_);
v___x_379_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_367_, v_fn_366_);
lean_dec(v___x_367_);
if (lean_obj_tag(v___x_379_) == 0)
{
v___y_372_ = v_fn_366_;
goto v___jp_371_;
}
else
{
lean_object* v_val_380_; 
lean_dec_ref(v_fn_366_);
v_val_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_379_, 1);
v___y_372_ = v_val_380_;
goto v___jp_371_;
}
v___jp_344_:
{
size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_ptr_addr(v_next_343_);
v___x_347_ = lean_ptr_addr(v_e_318_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_350_; 
lean_del_object(v___x_340_);
lean_dec(v_fst_330_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_a_345_);
lean_ctor_set(v___x_333_, 0, v_next_343_);
v___x_350_ = v___x_333_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_next_343_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_a_345_);
v___x_350_ = v_reuseFailAlloc_355_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_350_);
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_352_ = v___x_328_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
v_a_319_ = v___x_352_;
goto _start;
}
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec_ref(v_next_343_);
lean_inc_ref(v_a_345_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_a_345_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_a_345_);
v___x_358_ = v___x_333_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_345_);
v___x_358_ = v_reuseFailAlloc_365_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v___x_358_);
lean_ctor_set(v___x_328_, 0, v___x_356_);
v___x_360_ = v___x_328_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_362_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_360_);
v___x_362_ = v___x_340_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
v___jp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_array_push(v_snd_331_, v___y_369_);
v_a_345_ = v___x_370_;
goto v___jp_344_;
}
v___jp_371_:
{
lean_object* v___x_373_; size_t v_sz_374_; size_t v___x_375_; lean_object* v___x_376_; lean_object* v_fst_377_; 
v___x_373_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___closed__0));
v_sz_374_ = lean_array_size(v_snd_331_);
v___x_375_ = ((size_t)0ULL);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_getFnRoots_spec__0(v___y_372_, v_snd_331_, v_sz_374_, v___x_375_, v___x_373_);
v_fst_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_fst_377_);
lean_dec_ref(v___x_376_);
if (lean_obj_tag(v_fst_377_) == 0)
{
v___y_369_ = v___y_372_;
goto v___jp_368_;
}
else
{
lean_object* v_val_378_; 
v_val_378_ = lean_ctor_get(v_fst_377_, 0);
lean_inc(v_val_378_);
lean_dec_ref_known(v_fst_377_, 1);
if (lean_obj_tag(v_val_378_) == 0)
{
v___y_369_ = v___y_372_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_val_378_, 1);
lean_dec_ref(v___y_372_);
v_a_345_ = v_snd_331_;
goto v___jp_344_;
}
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_del_object(v___x_333_);
lean_dec(v_snd_331_);
lean_dec(v_fst_330_);
lean_del_object(v___x_328_);
v_a_382_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_337_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_337_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg___boxed(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_393_, v_a_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v_e_393_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots(lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_415_ = lean_box(0);
lean_inc_ref(v_e_402_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_e_402_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_402_, v___x_417_, v_a_403_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec_ref(v_e_402_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_448_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_448_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_fst_423_; 
v_fst_423_ = lean_ctor_get(v_a_419_, 0);
if (lean_obj_tag(v_fst_423_) == 0)
{
lean_object* v_snd_424_; lean_object* v_snd_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_421_);
v_snd_424_ = lean_ctor_get(v_a_419_, 1);
lean_inc(v_snd_424_);
lean_dec(v_a_419_);
v_snd_425_ = lean_ctor_get(v_snd_424_, 1);
lean_inc(v_snd_425_);
lean_dec(v_snd_424_);
v___x_426_ = lean_obj_once(&l_Lean_Meta_Grind_getEqcLambdas___closed__4, &l_Lean_Meta_Grind_getEqcLambdas___closed__4_once, _init_l_Lean_Meta_Grind_getEqcLambdas___closed__4);
v___x_427_ = l_panic___at___00Lean_Meta_Grind_getEqcLambdas_spec__1(v___x_426_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_427_, 0);
lean_dec(v_unused_435_);
v___x_429_ = v___x_427_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_dec(v___x_427_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v_snd_425_);
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_snd_425_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_snd_425_);
v_a_436_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_427_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_427_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_val_444_; lean_object* v___x_446_; 
lean_inc_ref(v_fst_423_);
lean_dec(v_a_419_);
v_val_444_ = lean_ctor_get(v_fst_423_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_fst_423_, 1);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_val_444_);
v___x_446_ = v___x_421_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_val_444_);
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
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_418_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_418_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getFnRoots___boxed(lean_object* v_e_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Grind_getFnRoots(v_e_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec(v_a_458_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(lean_object* v_e_470_, lean_object* v_inst_471_, lean_object* v_a_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___redArg(v_e_470_, v_a_472_, v___y_473_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1___boxed(lean_object* v_e_485_, lean_object* v_inst_486_, lean_object* v_a_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_getFnRoots_spec__1(v_e_485_, v_inst_486_, v_a_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v_e_485_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(lean_object* v_as_500_, size_t v_i_501_, size_t v_stop_502_, lean_object* v_b_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_a_507_; uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_501_, v_stop_502_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_500_, v_i_501_);
v___x_513_ = l_Lean_Meta_Grind_getGeneration___redArg(v___x_512_, v___y_504_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; uint8_t v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_nat_dec_le(v_b_503_, v_a_514_);
if (v___x_515_ == 0)
{
lean_dec(v_a_514_);
v_a_507_ = v_b_503_;
goto v___jp_506_;
}
else
{
lean_dec(v_b_503_);
v_a_507_ = v_a_514_;
goto v___jp_506_;
}
}
else
{
lean_dec(v_b_503_);
return v___x_513_;
}
}
else
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_503_);
return v___x_516_;
}
v___jp_506_:
{
size_t v___x_508_; size_t v___x_509_; 
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_501_, v___x_508_);
v_i_501_ = v___x_509_;
v_b_503_ = v_a_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg___boxed(lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_stop_519_, lean_object* v_b_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
size_t v_i_boxed_523_; size_t v_stop_boxed_524_; lean_object* v_res_525_; 
v_i_boxed_523_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_stop_boxed_524_ = lean_unbox_usize(v_stop_519_);
lean_dec(v_stop_519_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_517_, v_i_boxed_523_, v_stop_boxed_524_, v_b_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v_as_517_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(lean_object* v_msgData_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; lean_object* v_env_533_; uint8_t v___x_534_; lean_object* v_env_535_; lean_object* v___x_536_; lean_object* v_toCold_537_; lean_object* v_mctx_538_; lean_object* v_lctx_539_; lean_object* v_options_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_532_ = lean_st_ref_get(v___y_530_);
v_env_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_env_533_);
lean_dec(v___x_532_);
v___x_534_ = 0;
v_env_535_ = l_Lean_Environment_setRecordingDeps(v_env_533_, v___x_534_);
v___x_536_ = lean_st_ref_get(v___y_528_);
v_toCold_537_ = lean_ctor_get(v___y_529_, 0);
v_mctx_538_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_mctx_538_);
lean_dec(v___x_536_);
v_lctx_539_ = lean_ctor_get(v___y_527_, 2);
v_options_540_ = lean_ctor_get(v_toCold_537_, 2);
lean_inc_ref(v_options_540_);
lean_inc_ref(v_lctx_539_);
v___x_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_541_, 0, v_env_535_);
lean_ctor_set(v___x_541_, 1, v_mctx_538_);
lean_ctor_set(v___x_541_, 2, v_lctx_539_);
lean_ctor_set(v___x_541_, 3, v_options_540_);
v___x_542_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_msgData_526_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1___boxed(lean_object* v_msgData_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msgData_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_551_; double v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_float_of_nat(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(lean_object* v_cls_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_610_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 2);
v___x_564_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1_spec__1(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_610_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_610_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_610_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v_traceState_570_; lean_object* v_env_571_; lean_object* v_nextMacroScope_572_; lean_object* v_ngen_573_; lean_object* v_auxDeclNGen_574_; lean_object* v_cache_575_; lean_object* v_recordedDeps_576_; lean_object* v_messages_577_; lean_object* v_infoState_578_; lean_object* v_snapshotTasks_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_609_; 
v___x_569_ = lean_st_ref_take(v___y_561_);
v_traceState_570_ = lean_ctor_get(v___x_569_, 4);
v_env_571_ = lean_ctor_get(v___x_569_, 0);
v_nextMacroScope_572_ = lean_ctor_get(v___x_569_, 1);
v_ngen_573_ = lean_ctor_get(v___x_569_, 2);
v_auxDeclNGen_574_ = lean_ctor_get(v___x_569_, 3);
v_cache_575_ = lean_ctor_get(v___x_569_, 5);
v_recordedDeps_576_ = lean_ctor_get(v___x_569_, 6);
v_messages_577_ = lean_ctor_get(v___x_569_, 7);
v_infoState_578_ = lean_ctor_get(v___x_569_, 8);
v_snapshotTasks_579_ = lean_ctor_get(v___x_569_, 9);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_609_ == 0)
{
v___x_581_ = v___x_569_;
v_isShared_582_ = v_isSharedCheck_609_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snapshotTasks_579_);
lean_inc(v_infoState_578_);
lean_inc(v_messages_577_);
lean_inc(v_recordedDeps_576_);
lean_inc(v_cache_575_);
lean_inc(v_traceState_570_);
lean_inc(v_auxDeclNGen_574_);
lean_inc(v_ngen_573_);
lean_inc(v_nextMacroScope_572_);
lean_inc(v_env_571_);
lean_dec(v___x_569_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_609_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
uint64_t v_tid_583_; lean_object* v_traces_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_608_; 
v_tid_583_ = lean_ctor_get_uint64(v_traceState_570_, sizeof(void*)*1);
v_traces_584_ = lean_ctor_get(v_traceState_570_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v_traceState_570_);
if (v_isSharedCheck_608_ == 0)
{
v___x_586_ = v_traceState_570_;
v_isShared_587_ = v_isSharedCheck_608_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_traces_584_);
lean_dec(v_traceState_570_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_608_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; double v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_588_ = lean_box(0);
v___x_589_ = lean_box(0);
v___x_590_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__0);
v___x_591_ = 0;
v___x_592_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__1));
v___x_593_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_593_, 0, v_cls_556_);
lean_ctor_set(v___x_593_, 1, v___x_589_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_ctor_set_float(v___x_593_, sizeof(void*)*3, v___x_590_);
lean_ctor_set_float(v___x_593_, sizeof(void*)*3 + 8, v___x_590_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*3 + 16, v___x_591_);
v___x_594_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___closed__2));
v___x_595_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v_a_565_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
lean_inc(v_ref_563_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_ref_563_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_PersistentArray_push___redArg(v_traces_584_, v___x_596_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_597_);
v___x_599_ = v___x_586_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_597_);
lean_ctor_set_uint64(v_reuseFailAlloc_607_, sizeof(void*)*1, v_tid_583_);
v___x_599_ = v_reuseFailAlloc_607_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 4, v___x_599_);
v___x_601_ = v___x_581_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_env_571_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_nextMacroScope_572_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_ngen_573_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_auxDeclNGen_574_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v_cache_575_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v_recordedDeps_576_);
lean_ctor_set(v_reuseFailAlloc_606_, 7, v_messages_577_);
lean_ctor_set(v_reuseFailAlloc_606_, 8, v_infoState_578_);
lean_ctor_set(v_reuseFailAlloc_606_, 9, v_snapshotTasks_579_);
v___x_601_ = v_reuseFailAlloc_606_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_st_ref_put(v___y_561_, v___x_601_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_588_);
v___x_604_ = v___x_567_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_588_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg___boxed(lean_object* v_cls_611_, lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_611_, v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(lean_object* v_as_619_, size_t v_sz_620_, size_t v_i_621_, lean_object* v_b_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_lt(v_i_621_, v_sz_620_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v_b_622_);
return v___x_629_;
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_array_uget_borrowed(v_as_619_, v_i_621_);
lean_inc(v_a_630_);
v___x_631_ = l_Lean_Meta_mkCongrFun(v_b_622_, v_a_630_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; size_t v___x_633_; size_t v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = ((size_t)1ULL);
v___x_634_ = lean_usize_add(v_i_621_, v___x_633_);
v_i_621_ = v___x_634_;
v_b_622_ = v_a_632_;
goto _start;
}
else
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg___boxed(lean_object* v_as_636_, lean_object* v_sz_637_, lean_object* v_i_638_, lean_object* v_b_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_637_);
lean_dec(v_sz_637_);
v_i_boxed_646_ = lean_unbox_usize(v_i_638_);
lean_dec(v_i_638_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_636_, v_sz_boxed_645_, v_i_boxed_646_, v_b_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v_as_636_);
return v_res_647_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__5));
v___x_661_ = l_Lean_Name_append(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__7));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(lean_object* v_args_670_, lean_object* v_f_671_, lean_object* v_as_672_, size_t v_sz_673_, size_t v_i_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_a_688_; uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_lt(v_i_674_, v_sz_673_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_675_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v_a_695_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___x_721_; lean_object* v_a_723_; uint8_t v___x_820_; 
lean_dec_ref(v_b_675_);
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_a_695_ = lean_array_uget_borrowed(v_as_672_, v_i_674_);
lean_inc_ref(v_args_670_);
lean_inc(v_a_695_);
v___x_721_ = l_Lean_Expr_beta(v_a_695_, v_args_670_);
v___x_820_ = l_Lean_Expr_isLambda(v___x_721_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_695_, v___y_676_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = l_Lean_Meta_Grind_getGeneration___redArg(v_f_671_, v___y_676_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___y_826_; uint8_t v___x_842_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_842_ = lean_nat_dec_le(v_a_822_, v_a_824_);
if (v___x_842_ == 0)
{
lean_dec(v_a_824_);
v___y_826_ = v_a_822_;
goto v___jp_825_;
}
else
{
lean_dec(v_a_822_);
v___y_826_ = v_a_824_;
goto v___jp_825_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get_size(v_args_670_);
v___x_829_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
v_a_723_ = v___y_826_;
goto v___jp_722_;
}
else
{
size_t v___x_830_; size_t v___x_831_; lean_object* v___x_832_; 
v___x_830_ = ((size_t)0ULL);
v___x_831_ = lean_usize_of_nat(v___x_828_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_args_670_, v___x_830_, v___x_831_, v___y_826_, v___y_676_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v_a_723_ = v_a_833_;
goto v___jp_722_;
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_834_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_832_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_822_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_843_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_823_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_823_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_851_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_821_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_821_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_dec_ref(v___x_721_);
v_a_688_ = v___x_694_;
goto v___jp_687_;
}
v___jp_696_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc(v_a_695_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v_a_695_);
v___x_711_ = lean_box(1);
v___x_712_ = l_Lean_Meta_Grind_addNewRawFact(v___y_699_, v___y_698_, v___y_697_, v___x_710_, v___x_711_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_dec_ref_known(v___x_712_, 1);
v_a_688_ = v___x_694_;
goto v___jp_687_;
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_a_723_, v___x_724_);
lean_dec(v_a_723_);
v___x_726_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_678_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_811_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_811_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_811_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_811_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_le(v_a_727_, v___x_725_);
lean_dec(v_a_727_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_del_object(v___x_729_);
lean_inc_ref_n(v_f_671_, 2);
v___x_732_ = l_Lean_mkAppN(v_f_671_, v_args_670_);
lean_inc(v_a_695_);
v___x_733_ = l_Lean_Meta_Grind_hasSameType(v_f_671_, v_a_695_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; uint8_t v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_735_ == 0)
{
lean_dec_ref(v___x_732_);
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
v_a_688_ = v___x_694_;
goto v___jp_687_;
}
else
{
lean_object* v___x_736_; 
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc(v___y_676_);
lean_inc(v_a_695_);
lean_inc_ref(v_f_671_);
v___x_736_ = lean_grind_mk_eq_proof(v_f_671_, v_a_695_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; size_t v_sz_738_; size_t v___x_739_; lean_object* v___x_740_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v_sz_738_ = lean_array_size(v_args_670_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_args_670_, v_sz_738_, v___x_739_, v_a_737_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = l_Lean_Meta_mkEq(v___x_732_, v___x_721_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_toCold_743_; lean_object* v_options_744_; uint8_t v_hasTrace_745_; 
v_toCold_743_ = lean_ctor_get(v___y_684_, 0);
v_options_744_ = lean_ctor_get(v_toCold_743_, 2);
v_hasTrace_745_ = lean_ctor_get_uint8(v_options_744_, sizeof(void*)*1);
if (v_hasTrace_745_ == 0)
{
lean_object* v_a_746_; 
v_a_746_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_742_, 1);
v___y_697_ = v___x_725_;
v___y_698_ = v_a_746_;
v___y_699_ = v_a_741_;
v___y_700_ = v___y_676_;
v___y_701_ = v___y_677_;
v___y_702_ = v___y_678_;
v___y_703_ = v___y_679_;
v___y_704_ = v___y_680_;
v___y_705_ = v___y_681_;
v___y_706_ = v___y_682_;
v___y_707_ = v___y_683_;
v___y_708_ = v___y_684_;
v___y_709_ = v___y_685_;
goto v___jp_696_;
}
else
{
lean_object* v_a_747_; lean_object* v_inheritedTraceOptions_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_a_747_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_742_, 1);
v_inheritedTraceOptions_748_ = lean_ctor_get(v_toCold_743_, 11);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__3));
v___x_750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__6);
v___x_751_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_748_, v_options_744_, v___x_750_);
if (v___x_751_ == 0)
{
v___y_697_ = v___x_725_;
v___y_698_ = v_a_747_;
v___y_699_ = v_a_741_;
v___y_700_ = v___y_676_;
v___y_701_ = v___y_677_;
v___y_702_ = v___y_678_;
v___y_703_ = v___y_679_;
v___y_704_ = v___y_680_;
v___y_705_ = v___y_681_;
v___y_706_ = v___y_682_;
v___y_707_ = v___y_683_;
v___y_708_ = v___y_684_;
v___y_709_ = v___y_685_;
goto v___jp_696_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_updateLastTag(v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref_known(v___x_752_, 1);
lean_inc(v_a_747_);
v___x_753_ = l_Lean_MessageData_ofExpr(v_a_747_);
v___x_754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__8);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_inc(v_a_695_);
v___x_756_ = l_Lean_MessageData_ofExpr(v_a_695_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v___x_749_, v___x_757_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_dec_ref_known(v___x_758_, 1);
v___y_697_ = v___x_725_;
v___y_698_ = v_a_747_;
v___y_699_ = v_a_741_;
v___y_700_ = v___y_676_;
v___y_701_ = v___y_677_;
v___y_702_ = v___y_678_;
v___y_703_ = v___y_679_;
v___y_704_ = v___y_680_;
v___y_705_ = v___y_681_;
v___y_706_ = v___y_682_;
v___y_707_ = v___y_683_;
v___y_708_ = v___y_684_;
v___y_709_ = v___y_685_;
goto v___jp_696_;
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_747_);
lean_dec(v_a_741_);
lean_dec(v___x_725_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
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
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_747_);
lean_dec(v_a_741_);
lean_dec(v___x_725_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_767_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_752_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_752_);
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
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_741_);
lean_dec(v___x_725_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_775_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_742_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_742_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___x_732_);
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_783_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_740_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_740_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
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
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___x_732_);
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_791_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_736_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_736_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_732_);
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_799_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_733_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_733_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_809_; 
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v___x_807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__10));
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_807_);
v___x_809_ = v___x_729_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_725_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v_f_671_);
lean_dec_ref(v_args_670_);
v_a_812_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_726_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_726_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
v___jp_687_:
{
size_t v___x_689_; size_t v___x_690_; 
v___x_689_ = ((size_t)1ULL);
v___x_690_ = lean_usize_add(v_i_674_, v___x_689_);
lean_inc_ref(v_a_688_);
v_i_674_ = v___x_690_;
v_b_675_ = v_a_688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___boxed(lean_object** _args){
lean_object* v_args_859_ = _args[0];
lean_object* v_f_860_ = _args[1];
lean_object* v_as_861_ = _args[2];
lean_object* v_sz_862_ = _args[3];
lean_object* v_i_863_ = _args[4];
lean_object* v_b_864_ = _args[5];
lean_object* v___y_865_ = _args[6];
lean_object* v___y_866_ = _args[7];
lean_object* v___y_867_ = _args[8];
lean_object* v___y_868_ = _args[9];
lean_object* v___y_869_ = _args[10];
lean_object* v___y_870_ = _args[11];
lean_object* v___y_871_ = _args[12];
lean_object* v___y_872_ = _args[13];
lean_object* v___y_873_ = _args[14];
lean_object* v___y_874_ = _args[15];
lean_object* v___y_875_ = _args[16];
_start:
{
size_t v_sz_boxed_876_; size_t v_i_boxed_877_; lean_object* v_res_878_; 
v_sz_boxed_876_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_877_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_859_, v_f_860_, v_as_861_, v_sz_boxed_876_, v_i_boxed_877_, v_b_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v_as_861_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs(lean_object* v_lams_879_, lean_object* v_f_880_, lean_object* v_args_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_array_get_size(v_args_881_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_eq(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; size_t v_sz_898_; size_t v___x_899_; lean_object* v___x_900_; 
v___x_896_ = lean_box(0);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__0));
v_sz_898_ = lean_array_size(v_lams_879_);
v___x_899_ = ((size_t)0ULL);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3(v_args_881_, v_f_880_, v_lams_879_, v_sz_898_, v___x_899_, v___x_897_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_fst_905_; 
v_fst_905_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_fst_905_);
lean_dec(v_a_901_);
if (lean_obj_tag(v_fst_905_) == 0)
{
lean_object* v___x_907_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_896_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_896_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
lean_object* v_val_909_; lean_object* v___x_911_; 
v_val_909_ = lean_ctor_get(v_fst_905_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v_fst_905_, 1);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v_val_909_);
v___x_911_ = v___x_903_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_900_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_900_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v_args_881_);
lean_dec_ref(v_f_880_);
v___x_922_ = lean_box(0);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaEqs___boxed(lean_object* v_lams_924_, lean_object* v_f_925_, lean_object* v_args_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_924_, v_f_925_, v_args_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_lams_924_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(lean_object* v_as_939_, size_t v_sz_940_, size_t v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___redArg(v_as_939_, v_sz_940_, v_i_941_, v_b_942_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0___boxed(lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_971_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__0(v_as_955_, v_sz_boxed_970_, v_i_boxed_971_, v_b_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v_as_955_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(lean_object* v_cls_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___redArg(v_cls_973_, v_msg_974_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1___boxed(lean_object* v_cls_987_, lean_object* v_msg_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateBetaEqs_spec__1(v_cls_987_, v_msg_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_, lean_object* v_b_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___redArg(v_as_1001_, v_i_1002_, v_stop_1003_, v_b_1004_, v___y_1005_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2___boxed(lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_stop_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_i_boxed_1032_; size_t v_stop_boxed_1033_; lean_object* v_res_1034_; 
v_i_boxed_1032_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_stop_boxed_1033_ = lean_unbox_usize(v_stop_1019_);
lean_dec(v_stop_1019_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_propagateBetaEqs_spec__2(v_as_1017_, v_i_boxed_1032_, v_stop_boxed_1033_, v_b_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v_as_1017_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget_go(lean_object* v_f_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_f_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1074_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1074_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
if (lean_obj_tag(v_a_1064_) == 1)
{
lean_object* v_val_1068_; uint8_t v_hasLambdas_1069_; 
v_val_1068_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_a_1064_, 1);
v_hasLambdas_1069_ = lean_ctor_get_uint8(v_val_1068_, sizeof(void*)*12 + 3);
lean_dec(v_val_1068_);
if (v_hasLambdas_1069_ == 0)
{
lean_del_object(v___x_1066_);
v___y_1048_ = v_a_1036_;
v___y_1049_ = v_a_1037_;
v___y_1050_ = v_a_1038_;
v___y_1051_ = v_a_1039_;
v___y_1052_ = v_a_1040_;
v___y_1053_ = v_a_1041_;
v___y_1054_ = v_a_1042_;
v___y_1055_ = v_a_1043_;
v___y_1056_ = v_a_1044_;
v___y_1057_ = v_a_1045_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_box(v_hasLambdas_1069_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
else
{
lean_del_object(v___x_1066_);
lean_dec(v_a_1064_);
v___y_1048_ = v_a_1036_;
v___y_1049_ = v_a_1037_;
v___y_1050_ = v_a_1038_;
v___y_1051_ = v_a_1039_;
v___y_1052_ = v_a_1040_;
v___y_1053_ = v_a_1041_;
v___y_1054_ = v_a_1042_;
v___y_1055_ = v_a_1043_;
v___y_1056_ = v_a_1044_;
v___y_1057_ = v_a_1045_;
goto v___jp_1047_;
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1063_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1063_);
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
v___jp_1047_:
{
if (lean_obj_tag(v_f_1035_) == 5)
{
lean_object* v_fn_1058_; 
v_fn_1058_ = lean_ctor_get(v_f_1035_, 0);
v_f_1035_ = v_fn_1058_;
v_a_1036_ = v___y_1048_;
v_a_1037_ = v___y_1049_;
v_a_1038_ = v___y_1050_;
v_a_1039_ = v___y_1051_;
v_a_1040_ = v___y_1052_;
v_a_1041_ = v___y_1053_;
v_a_1042_ = v___y_1054_;
v_a_1043_ = v___y_1055_;
v_a_1044_ = v___y_1056_;
v_a_1045_ = v___y_1057_;
goto _start;
}
else
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = 0;
v___x_1061_ = lean_box(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(lean_object* v_fst_1126_, lean_object* v_snd_1127_, lean_object* v___x_1128_, lean_object* v_____r_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
if (lean_obj_tag(v_fst_1126_) == 5)
{
lean_object* v_fn_1141_; lean_object* v_arg_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_fn_1141_ = lean_ctor_get(v_fst_1126_, 0);
lean_inc_ref(v_fn_1141_);
v_arg_1142_ = lean_ctor_get(v_fst_1126_, 1);
lean_inc_ref(v_arg_1142_);
lean_dec_ref_known(v_fst_1126_, 2);
v___x_1143_ = lean_array_push(v_snd_1127_, v_arg_1142_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_fn_1141_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1128_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec(v___x_1128_);
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBetaEqs_spec__3___closed__9));
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_fst_1126_);
lean_ctor_set(v___x_1149_, 1, v_snd_1127_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0___boxed(lean_object* v_fst_1153_, lean_object* v_snd_1154_, lean_object* v___x_1155_, lean_object* v_____r_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1153_, v_snd_1154_, v___x_1155_, v_____r_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(lean_object* v_a_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___y_1182_; lean_object* v_snd_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_snd_1202_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1202_);
lean_dec_ref(v_a_1169_);
v_fst_1203_ = lean_ctor_get(v_snd_1202_, 0);
lean_inc(v_fst_1203_);
v_snd_1204_ = lean_ctor_get(v_snd_1202_, 1);
lean_inc(v_snd_1204_);
lean_dec(v_snd_1202_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_array_get_size(v_snd_1204_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_nat_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_fst_1203_, v___y_1170_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_object* v_val_1211_; uint8_t v_hasLambdas_1212_; 
v_val_1211_ = lean_ctor_get(v_a_1210_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_a_1210_, 1);
v_hasLambdas_1212_ = lean_ctor_get_uint8(v_val_1211_, sizeof(void*)*12 + 3);
if (v_hasLambdas_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
lean_dec(v_val_1211_);
v___x_1213_ = lean_box(0);
v___x_1214_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1203_, v_snd_1204_, v___x_1205_, v___x_1213_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v___y_1182_ = v___x_1214_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Meta_Grind_getEqcLambdas(v_val_1211_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v_val_1211_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
lean_inc(v_snd_1204_);
v___x_1217_ = l_Array_reverse___redArg(v_snd_1204_);
lean_inc(v_fst_1203_);
v___x_1218_ = l_Lean_Meta_Grind_propagateBetaEqs(v_a_1216_, v_fst_1203_, v___x_1217_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v_a_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1203_, v_snd_1204_, v___x_1205_, v_a_1219_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v___y_1182_ = v___x_1220_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_snd_1204_);
lean_dec(v_fst_1203_);
v_a_1221_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1218_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1218_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_snd_1204_);
lean_dec(v_fst_1203_);
v_a_1229_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1215_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1215_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_a_1210_);
v___x_1237_ = lean_box(0);
v___x_1238_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1203_, v_snd_1204_, v___x_1205_, v___x_1237_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v___y_1182_ = v___x_1238_;
goto v___jp_1181_;
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec(v_snd_1204_);
lean_dec(v_fst_1203_);
v_a_1239_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1209_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1209_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___lam__0(v_fst_1203_, v_snd_1204_, v___x_1205_, v___x_1247_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
v___y_1182_ = v___x_1248_;
goto v___jp_1181_;
}
v___jp_1181_:
{
if (lean_obj_tag(v___y_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_a_1183_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v___y_1182_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___y_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
if (lean_obj_tag(v_a_1183_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v_a_1183_, 1);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_a_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
else
{
lean_object* v_a_1191_; 
lean_del_object(v___x_1185_);
v_a_1191_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v_a_1183_, 1);
v_a_1169_ = v_a_1191_;
goto _start;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___y_1182_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___y_1182_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg___boxed(lean_object* v_a_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object* v_e_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Lean_Meta_Tactic_Grind_Beta_0__Lean_Meta_Grind_isPropagateBetaTarget(v_e_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1311_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1311_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1311_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec_ref(v_e_1262_);
v___x_1280_ = lean_box(0);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1280_);
v___x_1282_ = v___x_1277_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_del_object(v___x_1277_);
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Grind_getEqcLambdas___closed__0));
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_e_1262_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v___x_1287_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1302_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1302_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1302_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_fst_1293_; 
v_fst_1293_ = lean_ctor_get(v_a_1289_, 0);
lean_inc(v_fst_1293_);
lean_dec(v_a_1289_);
if (lean_obj_tag(v_fst_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(0);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1300_; 
v_val_1298_ = lean_ctor_get(v_fst_1293_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_fst_1293_, 1);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_val_1298_);
v___x_1300_ = v___x_1291_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1288_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1288_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_e_1262_);
v_a_1312_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1274_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1274_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp___boxed(lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_Grind_propagateBetaForNewApp(v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec(v_a_1321_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(lean_object* v_inst_1333_, lean_object* v_a_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___redArg(v_a_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0___boxed(lean_object* v_inst_1347_, lean_object* v_a_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBetaForNewApp_spec__0(v_inst_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
return v_res_1360_;
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
