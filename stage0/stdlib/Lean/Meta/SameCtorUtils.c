// Lean compiler output
// Module: Lean.Meta.SameCtorUtils
// Imports: public import Lean.Meta.Basic import Lean.Meta.Transform
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
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursOrInType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_occursInCtorTypeMask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_occursInCtorTypeMask___closed__0 = (const lean_object*)&l_Lean_Meta_occursInCtorTypeMask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assertion violation: t.isForall\n        "};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Meta.SameCtorUtils.0.Lean.Meta.withSharedCtorIndices.go"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.SameCtorUtils"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0;
static const lean_array_object l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(lean_object* v_lctx_1_, lean_object* v_e_2_, lean_object* v_s_3_){
_start:
{
if (lean_obj_tag(v_s_3_) == 1)
{
lean_object* v_fvarId_4_; lean_object* v___x_5_; 
v_fvarId_4_ = lean_ctor_get(v_s_3_, 0);
lean_inc(v_fvarId_4_);
v___x_5_ = lean_local_ctx_find(v_lctx_1_, v_fvarId_4_);
if (lean_obj_tag(v___x_5_) == 1)
{
lean_object* v_val_6_; uint8_t v___x_7_; 
v_val_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_val_6_);
lean_dec_ref_known(v___x_5_, 1);
v___x_7_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref_known(v_s_3_, 1);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = l_Lean_LocalDecl_type(v_val_6_);
lean_dec(v_val_6_);
v___x_9_ = l_Lean_Expr_occurs(v_e_2_, v___x_8_);
lean_dec_ref(v___x_8_);
return v___x_9_;
}
else
{
lean_dec(v_val_6_);
lean_dec_ref(v_e_2_);
return v___x_7_;
}
}
else
{
uint8_t v___x_10_; 
lean_dec(v___x_5_);
v___x_10_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref(v_e_2_);
lean_dec_ref_known(v_s_3_, 1);
return v___x_10_;
}
}
else
{
uint8_t v___x_11_; 
lean_dec_ref(v_lctx_1_);
v___x_11_ = lean_expr_eqv(v_s_3_, v_e_2_);
lean_dec_ref(v_e_2_);
lean_dec_ref(v_s_3_);
return v___x_11_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1_ = stack[0].m_obj;
lean_object* v_e_2_ = stack[1].m_obj;
lean_object* v_s_3_ = stack[2].m_obj;
uint8_t v_res_12_;
v_res_12_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(v_lctx_1_, v_e_2_, v_s_3_);
stack->m_num = v_res_12_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed(lean_object* v_lctx_13_, lean_object* v_e_14_, lean_object* v_s_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go(v_lctx_13_, v_e_14_, v_s_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
uint8_t l_Lean_Meta_occursOrInType(lean_object* v_lctx_18_, lean_object* v_e_19_, lean_object* v_t_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_occursOrInType_go___boxed), 3, 2);
lean_closure_set(v___x_21_, 0, v_lctx_18_);
lean_closure_set(v___x_21_, 1, v_e_19_);
v___x_22_ = lean_find_expr(v___x_21_, v_t_20_);
lean_dec_ref(v___x_21_);
if (lean_obj_tag(v___x_22_) == 0)
{
uint8_t v___x_23_; 
v___x_23_ = 0;
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
lean_dec_ref_known(v___x_22_, 1);
v___x_24_ = 1;
return v___x_24_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_occursOrInType_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_18_ = stack[0].m_obj;
lean_object* v_e_19_ = stack[1].m_obj;
lean_object* v_t_20_ = stack[2].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_Lean_Meta_occursOrInType(v_lctx_18_, v_e_19_, v_t_20_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursOrInType___boxed(lean_object* v_lctx_26_, lean_object* v_e_27_, lean_object* v_t_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Lean_Meta_occursOrInType(v_lctx_26_, v_e_27_, v_t_28_);
lean_dec_ref(v_t_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(lean_object* v_k_31_, lean_object* v_b_32_, lean_object* v_c_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
v___x_39_ = lean_apply_7(v_k_31_, v_b_32_, v_c_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, lean_box(0));
return v___x_39_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_31_ = stack[0].m_obj;
lean_object* v_b_32_ = stack[1].m_obj;
lean_object* v_c_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v_res_40_;
v_res_40_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_31_, v_b_32_, v_c_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed(lean_object* v_k_41_, lean_object* v_b_42_, lean_object* v_c_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0(v_k_41_, v_b_42_, v_c_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(lean_object* v_type_50_, lean_object* v_maxFVars_x3f_51_, lean_object* v_k_52_, uint8_t v_cleanupAnnotations_53_, uint8_t v_whnfType_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___f_60_; lean_object* v___x_61_; 
v___f_60_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_60_, 0, v_k_52_);
v___x_61_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_50_, v_maxFVars_x3f_51_, v___f_60_, v_cleanupAnnotations_53_, v_whnfType_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
v_a_70_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_61_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_61_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_50_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_51_ = stack[1].m_obj;
lean_object* v_k_52_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_53_ = stack[3].m_num;
uint8_t v_whnfType_54_ = stack[4].m_num;
lean_object* v___y_55_ = stack[5].m_obj;
lean_object* v___y_56_ = stack[6].m_obj;
lean_object* v___y_57_ = stack[7].m_obj;
lean_object* v___y_58_ = stack[8].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_50_, v_maxFVars_x3f_51_, v_k_52_, v_cleanupAnnotations_53_, v_whnfType_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___boxed(lean_object* v_type_79_, lean_object* v_maxFVars_x3f_80_, lean_object* v_k_81_, lean_object* v_cleanupAnnotations_82_, lean_object* v_whnfType_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_89_; uint8_t v_whnfType_boxed_90_; lean_object* v_res_91_; 
v_cleanupAnnotations_boxed_89_ = lean_unbox(v_cleanupAnnotations_82_);
v_whnfType_boxed_90_ = lean_unbox(v_whnfType_83_);
v_res_91_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_79_, v_maxFVars_x3f_80_, v_k_81_, v_cleanupAnnotations_boxed_89_, v_whnfType_boxed_90_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_91_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(lean_object* v_00_u03b1_92_, lean_object* v_type_93_, lean_object* v_maxFVars_x3f_94_, lean_object* v_k_95_, uint8_t v_cleanupAnnotations_96_, uint8_t v_whnfType_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_93_, v_maxFVars_x3f_94_, v_k_95_, v_cleanupAnnotations_96_, v_whnfType_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_93_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_94_ = stack[2].m_obj;
lean_object* v_k_95_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_96_ = stack[4].m_num;
uint8_t v_whnfType_97_ = stack[5].m_num;
lean_object* v___y_98_ = stack[6].m_obj;
lean_object* v___y_99_ = stack[7].m_obj;
lean_object* v___y_100_ = stack[8].m_obj;
lean_object* v___y_101_ = stack[9].m_obj;
lean_object* v_res_104_;
v_res_104_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(lean_box(0), v_type_93_, v_maxFVars_x3f_94_, v_k_95_, v_cleanupAnnotations_96_, v_whnfType_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___boxed(lean_object* v_00_u03b1_105_, lean_object* v_type_106_, lean_object* v_maxFVars_x3f_107_, lean_object* v_k_108_, lean_object* v_cleanupAnnotations_109_, lean_object* v_whnfType_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_116_; uint8_t v_whnfType_boxed_117_; lean_object* v_res_118_; 
v_cleanupAnnotations_boxed_116_ = lean_unbox(v_cleanupAnnotations_109_);
v_whnfType_boxed_117_ = lean_unbox(v_whnfType_110_);
v_res_118_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2(v_00_u03b1_105_, v_type_106_, v_maxFVars_x3f_107_, v_k_108_, v_cleanupAnnotations_boxed_116_, v_whnfType_boxed_117_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_118_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(lean_object* v___x_119_, lean_object* v_a_120_, size_t v_sz_121_, size_t v_i_122_, lean_object* v_bs_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_lt(v_i_122_, v_sz_121_);
if (v___x_124_ == 0)
{
lean_dec_ref(v___x_119_);
return v_bs_123_;
}
else
{
lean_object* v_v_125_; lean_object* v___x_126_; lean_object* v_bs_x27_127_; uint8_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_v_125_ = lean_array_uget(v_bs_123_, v_i_122_);
v___x_126_ = lean_unsigned_to_nat(0u);
v_bs_x27_127_ = lean_array_uset(v_bs_123_, v_i_122_, v___x_126_);
lean_inc_ref(v___x_119_);
v___x_128_ = l_Lean_Meta_occursOrInType(v___x_119_, v_v_125_, v_a_120_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_i_122_, v___x_129_);
v___x_131_ = lean_box(v___x_128_);
v___x_132_ = lean_array_uset(v_bs_x27_127_, v_i_122_, v___x_131_);
v_i_122_ = v___x_130_;
v_bs_123_ = v___x_132_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_119_ = stack[0].m_obj;
lean_object* v_a_120_ = stack[1].m_obj;
size_t v_sz_121_ = stack[2].m_num;
size_t v_i_122_ = stack[3].m_num;
lean_object* v_bs_123_ = stack[4].m_obj;
lean_object* v_res_134_;
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_119_, v_a_120_, v_sz_121_, v_i_122_, v_bs_123_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0___boxed(lean_object* v___x_135_, lean_object* v_a_136_, lean_object* v_sz_137_, lean_object* v_i_138_, lean_object* v_bs_139_){
_start:
{
size_t v_sz_boxed_140_; size_t v_i_boxed_141_; lean_object* v_res_142_; 
v_sz_boxed_140_ = lean_unbox_usize(v_sz_137_);
lean_dec(v_sz_137_);
v_i_boxed_141_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_res_142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v___x_135_, v_a_136_, v_sz_boxed_140_, v_i_boxed_141_, v_bs_139_);
lean_dec_ref(v_a_136_);
return v_res_142_;
}
}
lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0(lean_object* v_ys_143_, lean_object* v_ctorRet_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
v___x_150_ = lean_whnf(v_ctorRet_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = l_Lean_Core_betaReduce(v_a_151_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_164_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_lctx_157_; size_t v_sz_158_; size_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v_lctx_157_ = lean_ctor_get(v___y_145_, 2);
v_sz_158_ = lean_array_size(v_ys_143_);
v___x_159_ = ((size_t)0ULL);
lean_inc_ref(v_lctx_157_);
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_occursInCtorTypeMask_spec__0(v_lctx_157_, v_a_153_, v_sz_158_, v___x_159_, v_ys_143_);
lean_dec(v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_160_);
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec_ref(v_ys_143_);
v_a_165_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_152_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_152_);
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
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v_ys_143_);
v_a_173_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_150_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_150_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_occursInCtorTypeMask___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_143_ = stack[0].m_obj;
lean_object* v_ctorRet_144_ = stack[1].m_obj;
lean_object* v___y_145_ = stack[2].m_obj;
lean_object* v___y_146_ = stack[3].m_obj;
lean_object* v___y_147_ = stack[4].m_obj;
lean_object* v___y_148_ = stack[5].m_obj;
lean_object* v_res_181_;
v_res_181_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(v_ys_143_, v_ctorRet_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__0___boxed(lean_object* v_ys_182_, lean_object* v_ctorRet_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Meta_occursInCtorTypeMask___lam__0(v_ys_182_, v_ctorRet_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1(lean_object* v_numFields_190_, lean_object* v___f_191_, lean_object* v_x_192_, lean_object* v_ctorRet_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_numFields_190_);
v___x_200_ = 0;
v___x_201_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_ctorRet_193_, v___x_199_, v___f_191_, v___x_200_, v___x_200_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lean_Meta_occursInCtorTypeMask___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numFields_190_ = stack[0].m_obj;
lean_object* v___f_191_ = stack[1].m_obj;
lean_object* v_x_192_ = stack[2].m_obj;
lean_object* v_ctorRet_193_ = stack[3].m_obj;
lean_object* v___y_194_ = stack[4].m_obj;
lean_object* v___y_195_ = stack[5].m_obj;
lean_object* v___y_196_ = stack[6].m_obj;
lean_object* v___y_197_ = stack[7].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_Meta_occursInCtorTypeMask___lam__1(v_numFields_190_, v___f_191_, v_x_192_, v_ctorRet_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed(lean_object* v_numFields_203_, lean_object* v___f_204_, lean_object* v_x_205_, lean_object* v_ctorRet_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_occursInCtorTypeMask___lam__1(v_numFields_203_, v___f_204_, v_x_205_, v_ctorRet_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec_ref(v_x_205_);
return v_res_212_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_instMonadEIO___redArg();
return v___x_213_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(lean_object* v_msg_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_toApplicative_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_287_; 
v___x_224_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__0);
v___x_225_ = l_StateRefT_x27_instMonad___redArg(v___x_224_);
v_toApplicative_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_225_, 1);
lean_dec(v_unused_288_);
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_287_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_toApplicative_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_287_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_toFunctor_230_; lean_object* v_toSeq_231_; lean_object* v_toSeqLeft_232_; lean_object* v_toSeqRight_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_285_; 
v_toFunctor_230_ = lean_ctor_get(v_toApplicative_226_, 0);
v_toSeq_231_ = lean_ctor_get(v_toApplicative_226_, 2);
v_toSeqLeft_232_ = lean_ctor_get(v_toApplicative_226_, 3);
v_toSeqRight_233_ = lean_ctor_get(v_toApplicative_226_, 4);
v_isSharedCheck_285_ = !lean_is_exclusive(v_toApplicative_226_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_toApplicative_226_, 1);
lean_dec(v_unused_286_);
v___x_235_ = v_toApplicative_226_;
v_isShared_236_ = v_isSharedCheck_285_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_toSeqRight_233_);
lean_inc(v_toSeqLeft_232_);
lean_inc(v_toSeq_231_);
lean_inc(v_toFunctor_230_);
lean_dec(v_toApplicative_226_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_285_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___f_242_; lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_246_; 
v___f_237_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__1));
v___f_238_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__2));
lean_inc_ref(v_toFunctor_230_);
v___f_239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_239_, 0, v_toFunctor_230_);
v___f_240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_240_, 0, v_toFunctor_230_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___f_239_);
lean_ctor_set(v___x_241_, 1, v___f_240_);
v___f_242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_242_, 0, v_toSeqRight_233_);
v___f_243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_243_, 0, v_toSeqLeft_232_);
v___f_244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_244_, 0, v_toSeq_231_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 4, v___f_242_);
lean_ctor_set(v___x_235_, 3, v___f_243_);
lean_ctor_set(v___x_235_, 2, v___f_244_);
lean_ctor_set(v___x_235_, 1, v___f_237_);
lean_ctor_set(v___x_235_, 0, v___x_241_);
v___x_246_ = v___x_235_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___f_237_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v___f_244_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v___f_243_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v___f_242_);
v___x_246_ = v_reuseFailAlloc_284_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_248_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___f_238_);
lean_ctor_set(v___x_228_, 0, v___x_246_);
v___x_248_ = v___x_228_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___f_238_);
v___x_248_ = v_reuseFailAlloc_283_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v_toApplicative_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_281_; 
v___x_249_ = l_StateRefT_x27_instMonad___redArg(v___x_248_);
v_toApplicative_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_249_, 1);
lean_dec(v_unused_282_);
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_281_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_toApplicative_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_281_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_toFunctor_254_; lean_object* v_toSeq_255_; lean_object* v_toSeqLeft_256_; lean_object* v_toSeqRight_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_279_; 
v_toFunctor_254_ = lean_ctor_get(v_toApplicative_250_, 0);
v_toSeq_255_ = lean_ctor_get(v_toApplicative_250_, 2);
v_toSeqLeft_256_ = lean_ctor_get(v_toApplicative_250_, 3);
v_toSeqRight_257_ = lean_ctor_get(v_toApplicative_250_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v_toApplicative_250_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_toApplicative_250_, 1);
lean_dec(v_unused_280_);
v___x_259_ = v_toApplicative_250_;
v_isShared_260_ = v_isSharedCheck_279_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_toSeqRight_257_);
lean_inc(v_toSeqLeft_256_);
lean_inc(v_toSeq_255_);
lean_inc(v_toFunctor_254_);
lean_dec(v_toApplicative_250_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_279_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___f_266_; lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___x_270_; 
v___f_261_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__3));
v___f_262_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___closed__4));
lean_inc_ref(v_toFunctor_254_);
v___f_263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_263_, 0, v_toFunctor_254_);
v___f_264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_264_, 0, v_toFunctor_254_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___f_263_);
lean_ctor_set(v___x_265_, 1, v___f_264_);
v___f_266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_266_, 0, v_toSeqRight_257_);
v___f_267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_267_, 0, v_toSeqLeft_256_);
v___f_268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_268_, 0, v_toSeq_255_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 4, v___f_266_);
lean_ctor_set(v___x_259_, 3, v___f_267_);
lean_ctor_set(v___x_259_, 2, v___f_268_);
lean_ctor_set(v___x_259_, 1, v___f_261_);
lean_ctor_set(v___x_259_, 0, v___x_265_);
v___x_270_ = v___x_259_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___f_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v___f_268_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v___f_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v___f_266_);
v___x_270_ = v_reuseFailAlloc_278_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v___f_262_);
lean_ctor_set(v___x_252_, 0, v___x_270_);
v___x_272_ = v___x_252_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___f_262_);
v___x_272_ = v_reuseFailAlloc_277_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_2056__overap_275_; lean_object* v___x_276_; 
v___x_273_ = lean_box(0);
v___x_274_ = l_instInhabitedOfMonad___redArg(v___x_272_, v___x_273_);
v___x_2056__overap_275_ = lean_panic_fn_borrowed(v___x_274_, v_msg_218_);
lean_dec(v___x_274_);
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_276_ = lean_apply_5(v___x_2056__overap_275_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, lean_box(0));
return v___x_276_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_218_ = stack[0].m_obj;
lean_object* v___y_219_ = stack[1].m_obj;
lean_object* v___y_220_ = stack[2].m_obj;
lean_object* v___y_221_ = stack[3].m_obj;
lean_object* v___y_222_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2___boxed(lean_object* v_msg_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v_msg_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v_env_304_; uint8_t v___x_305_; lean_object* v_env_306_; lean_object* v___x_307_; lean_object* v_toCold_308_; lean_object* v_mctx_309_; lean_object* v_lctx_310_; lean_object* v_options_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_303_ = lean_st_ref_get(v___y_301_);
v_env_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref(v_env_304_);
lean_dec(v___x_303_);
v___x_305_ = 0;
v_env_306_ = l_Lean_Environment_setRecordingDeps(v_env_304_, v___x_305_);
v___x_307_ = lean_st_ref_get(v___y_299_);
v_toCold_308_ = lean_ctor_get(v___y_300_, 0);
v_mctx_309_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_mctx_309_);
lean_dec(v___x_307_);
v_lctx_310_ = lean_ctor_get(v___y_298_, 2);
v_options_311_ = lean_ctor_get(v_toCold_308_, 2);
lean_inc_ref(v_options_311_);
lean_inc_ref(v_lctx_310_);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_env_306_);
lean_ctor_set(v___x_312_, 1, v_mctx_309_);
lean_ctor_set(v___x_312_, 2, v_lctx_310_);
lean_ctor_set(v___x_312_, 3, v_options_311_);
v___x_313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_msgData_297_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_297_ = stack[0].m_obj;
lean_object* v___y_298_ = stack[1].m_obj;
lean_object* v___y_299_ = stack[2].m_obj;
lean_object* v___y_300_ = stack[3].m_obj;
lean_object* v___y_301_ = stack[4].m_obj;
lean_object* v_res_315_;
v_res_315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3___boxed(lean_object* v_msgData_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msgData_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(lean_object* v_msg_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_ref_329_; lean_object* v___x_330_; lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
v_ref_329_ = lean_ctor_get(v___y_326_, 2);
v___x_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_spec__3(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_inc(v_ref_329_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_ref_329_);
lean_ctor_set(v___x_335_, 1, v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 1);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_323_ = stack[0].m_obj;
lean_object* v___y_324_ = stack[1].m_obj;
lean_object* v___y_325_ = stack[2].m_obj;
lean_object* v___y_326_ = stack[3].m_obj;
lean_object* v___y_327_ = stack[4].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg___boxed(lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__0));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__2));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_357_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__6));
v___x_358_ = lean_unsigned_to_nat(11u);
v___x_359_ = lean_unsigned_to_nat(122u);
v___x_360_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__5));
v___x_361_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__4));
v___x_362_ = l_mkPanicMessageWithDecl(v___x_361_, v___x_360_, v___x_359_, v___x_358_, v___x_357_);
return v___x_362_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(lean_object* v_constName_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_377_; lean_object* v_env_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_st_ref_get(v___y_367_);
v_env_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_env_378_);
lean_dec(v___x_377_);
v___x_379_ = 0;
lean_inc(v_constName_363_);
v___x_380_ = l_Lean_Environment_findAsync_x3f(v_env_378_, v_constName_363_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 1)
{
lean_object* v_val_381_; uint8_t v_kind_382_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v___x_380_, 1);
v_kind_382_ = lean_ctor_get_uint8(v_val_381_, sizeof(void*)*3);
if (v_kind_382_ == 6)
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_381_);
if (lean_obj_tag(v___x_383_) == 6)
{
lean_object* v_val_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_constName_363_);
v_val_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_val_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 0);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_val_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec_ref(v___x_383_);
v___x_392_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__7);
v___x_393_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__2(v___x_392_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_del_object(v___x_396_);
goto v___jp_369_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_400_; 
lean_dec(v_constName_363_);
v_val_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_val_398_);
lean_dec_ref_known(v_a_394_, 1);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_val_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_val_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_constName_363_);
v_a_403_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_dec(v_val_381_);
goto v___jp_369_;
}
}
else
{
lean_dec(v___x_380_);
goto v___jp_369_;
}
v___jp_369_:
{
lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_371_ = 0;
v___x_372_ = l_Lean_MessageData_ofConstName(v_constName_363_, v___x_371_);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_370_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__3);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_375_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
return v___x_376_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_363_ = stack[0].m_obj;
lean_object* v___y_364_ = stack[1].m_obj;
lean_object* v___y_365_ = stack[2].m_obj;
lean_object* v___y_366_ = stack[3].m_obj;
lean_object* v___y_367_ = stack[4].m_obj;
lean_object* v_res_411_;
v_res_411_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_constName_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___boxed(lean_object* v_constName_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_constName_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
return v_res_418_;
}
}
lean_object* l_Lean_Meta_occursInCtorTypeMask(lean_object* v_ctorName_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___f_426_; lean_object* v___x_427_; 
v___f_426_ = ((lean_object*)(l_Lean_Meta_occursInCtorTypeMask___closed__0));
v___x_427_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1(v_ctorName_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v_toConstantVal_429_; lean_object* v_numParams_430_; lean_object* v_numFields_431_; lean_object* v_type_432_; lean_object* v___f_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v_toConstantVal_429_ = lean_ctor_get(v_a_428_, 0);
lean_inc_ref(v_toConstantVal_429_);
v_numParams_430_ = lean_ctor_get(v_a_428_, 3);
lean_inc(v_numParams_430_);
v_numFields_431_ = lean_ctor_get(v_a_428_, 4);
lean_inc(v_numFields_431_);
lean_dec(v_a_428_);
v_type_432_ = lean_ctor_get(v_toConstantVal_429_, 2);
lean_inc_ref(v_type_432_);
lean_dec_ref(v_toConstantVal_429_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_Meta_occursInCtorTypeMask___lam__1___boxed), 9, 2);
lean_closure_set(v___f_433_, 0, v_numFields_431_);
lean_closure_set(v___f_433_, 1, v___f_426_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v_numParams_430_);
v___x_435_ = 0;
v___x_436_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg(v_type_432_, v___x_434_, v___f_433_, v___x_435_, v___x_435_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_427_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_occursInCtorTypeMask_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorName_420_ = stack[0].m_obj;
lean_object* v_a_421_ = stack[1].m_obj;
lean_object* v_a_422_ = stack[2].m_obj;
lean_object* v_a_423_ = stack[3].m_obj;
lean_object* v_a_424_ = stack[4].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Meta_occursInCtorTypeMask(v_ctorName_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_occursInCtorTypeMask___boxed(lean_object* v_ctorName_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_occursInCtorTypeMask(v_ctorName_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
return v_res_452_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_object* v_00_u03b1_453_, lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v_msg_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_460_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_454_ = stack[1].m_obj;
lean_object* v___y_455_ = stack[2].m_obj;
lean_object* v___y_456_ = stack[3].m_obj;
lean_object* v___y_457_ = stack[4].m_obj;
lean_object* v___y_458_ = stack[5].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(lean_box(0), v_msg_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___boxed(lean_object* v_00_u03b1_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1(v_00_u03b1_462_, v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_427__overap_478_; lean_object* v___x_479_; 
v___f_477_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___closed__0));
v___x_427__overap_478_ = lean_panic_fn_borrowed(v___f_477_, v_msg_471_);
lean_inc(v___y_475_);
lean_inc_ref(v___y_474_);
lean_inc(v___y_473_);
lean_inc_ref(v___y_472_);
v___x_479_ = lean_apply_5(v___x_427__overap_478_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, lean_box(0));
return v___x_479_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_471_ = stack[0].m_obj;
lean_object* v___y_472_ = stack[1].m_obj;
lean_object* v___y_473_ = stack[2].m_obj;
lean_object* v___y_474_ = stack[3].m_obj;
lean_object* v___y_475_ = stack[4].m_obj;
lean_object* v_res_480_;
v_res_480_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg___boxed(lean_object* v_msg_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_object* v_00_u03b1_488_, lean_object* v_msg_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v_msg_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
return v___x_495_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_489_ = stack[1].m_obj;
lean_object* v___y_490_ = stack[2].m_obj;
lean_object* v___y_491_ = stack[3].m_obj;
lean_object* v___y_492_ = stack[4].m_obj;
lean_object* v___y_493_ = stack[5].m_obj;
lean_object* v_res_496_;
v_res_496_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(lean_box(0), v_msg_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
stack->m_obj
 = v_res_496_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___boxed(lean_object* v_00_u03b1_497_, lean_object* v_msg_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0(v_00_u03b1_497_, v_msg_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_504_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(lean_object* v_k_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; 
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
v___x_512_ = lean_apply_6(v_k_505_, v_b_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
return v___x_512_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_505_ = stack[0].m_obj;
lean_object* v_b_506_ = stack[1].m_obj;
lean_object* v___y_507_ = stack[2].m_obj;
lean_object* v___y_508_ = stack[3].m_obj;
lean_object* v___y_509_ = stack[4].m_obj;
lean_object* v___y_510_ = stack[5].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_505_, v_b_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0(v_k_514_, v_b_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_521_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(lean_object* v_name_522_, uint8_t v_bi_523_, lean_object* v_type_524_, lean_object* v_k_525_, uint8_t v_kind_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___f_532_; lean_object* v___x_533_; 
v___f_532_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_532_, 0, v_k_525_);
v___x_533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_522_, v_bi_523_, v_type_524_, v___f_532_, v_kind_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_533_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_533_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_522_ = stack[0].m_obj;
uint8_t v_bi_523_ = stack[1].m_num;
lean_object* v_type_524_ = stack[2].m_obj;
lean_object* v_k_525_ = stack[3].m_obj;
uint8_t v_kind_526_ = stack[4].m_num;
lean_object* v___y_527_ = stack[5].m_obj;
lean_object* v___y_528_ = stack[6].m_obj;
lean_object* v___y_529_ = stack[7].m_obj;
lean_object* v___y_530_ = stack[8].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_522_, v_bi_523_, v_type_524_, v_k_525_, v_kind_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg___boxed(lean_object* v_name_551_, lean_object* v_bi_552_, lean_object* v_type_553_, lean_object* v_k_554_, lean_object* v_kind_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_bi_boxed_561_; uint8_t v_kind_boxed_562_; lean_object* v_res_563_; 
v_bi_boxed_561_ = lean_unbox(v_bi_552_);
v_kind_boxed_562_ = lean_unbox(v_kind_555_);
v_res_563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_551_, v_bi_boxed_561_, v_type_553_, v_k_554_, v_kind_boxed_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_563_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(lean_object* v_name_564_, lean_object* v_type_565_, lean_object* v_k_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; 
v___x_572_ = 0;
v___x_573_ = 0;
v___x_574_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_564_, v___x_572_, v_type_565_, v_k_566_, v___x_573_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_574_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_564_ = stack[0].m_obj;
lean_object* v_type_565_ = stack[1].m_obj;
lean_object* v_k_566_ = stack[2].m_obj;
lean_object* v___y_567_ = stack[3].m_obj;
lean_object* v___y_568_ = stack[4].m_obj;
lean_object* v___y_569_ = stack[5].m_obj;
lean_object* v___y_570_ = stack[6].m_obj;
lean_object* v_res_575_;
v_res_575_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_564_, v_type_565_, v_k_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
stack->m_obj
 = v_res_575_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg___boxed(lean_object* v_name_576_, lean_object* v_type_577_, lean_object* v_k_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_576_, v_type_577_, v_k_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed(lean_object* v_zs2_585_, lean_object* v_acc_586_, lean_object* v_ctor_587_, lean_object* v_k_588_, lean_object* v_zs_589_, lean_object* v_indices_590_, lean_object* v_tail_591_, lean_object* v_tail_592_, lean_object* v_z_x27_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(v_zs2_585_, v_acc_586_, v_ctor_587_, v_k_588_, v_zs_589_, v_indices_590_, v_tail_591_, v_tail_592_, v_z_x27_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
static lean_object* _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__2));
v___x_604_ = lean_unsigned_to_nat(8u);
v___x_605_ = lean_unsigned_to_nat(91u);
v___x_606_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__1));
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__0));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(lean_object* v_ctor_610_, lean_object* v_k_611_, lean_object* v_zs_612_, lean_object* v_indices_613_, lean_object* v_zs2_614_, lean_object* v_mask_615_, lean_object* v_todo_616_, lean_object* v_acc_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
if (lean_obj_tag(v_mask_615_) == 1)
{
lean_object* v_head_623_; uint8_t v___x_624_; 
v_head_623_ = lean_ctor_get(v_mask_615_, 0);
v___x_624_ = lean_unbox(v_head_623_);
if (v___x_624_ == 0)
{
if (lean_obj_tag(v_todo_616_) == 1)
{
lean_object* v_tail_625_; lean_object* v_tail_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_tail_625_ = lean_ctor_get(v_mask_615_, 1);
lean_inc(v_tail_625_);
lean_dec_ref_known(v_mask_615_, 2);
v_tail_626_ = lean_ctor_get(v_todo_616_, 1);
lean_inc(v_tail_626_);
lean_dec_ref_known(v_todo_616_, 2);
lean_inc_ref(v_ctor_610_);
lean_inc_ref(v_zs2_614_);
v___f_627_ = lean_alloc_closure((void*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_627_, 0, v_zs2_614_);
lean_closure_set(v___f_627_, 1, v_acc_617_);
lean_closure_set(v___f_627_, 2, v_ctor_610_);
lean_closure_set(v___f_627_, 3, v_k_611_);
lean_closure_set(v___f_627_, 4, v_zs_612_);
lean_closure_set(v___f_627_, 5, v_indices_613_);
lean_closure_set(v___f_627_, 6, v_tail_625_);
lean_closure_set(v___f_627_, 7, v_tail_626_);
v___x_628_ = l_Lean_mkAppN(v_ctor_610_, v_zs2_614_);
lean_dec_ref(v_zs2_614_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
v___x_629_ = lean_infer_type(v___x_628_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_Meta_whnfForall(v_a_630_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; uint8_t v___x_633_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = l_Lean_Expr_isForall(v_a_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v_a_632_);
lean_dec_ref(v___f_627_);
v___x_634_ = lean_obj_once(&l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3, &l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3_once, _init_l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__3);
v___x_635_ = l_panic___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__0___redArg(v___x_634_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = l_Lean_Expr_bindingName_x21(v_a_632_);
v___x_637_ = ((lean_object*)(l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___closed__4));
v___x_638_ = lean_name_append_after(v___x_636_, v___x_637_);
v___x_639_ = l_Lean_Expr_bindingDomain_x21(v_a_632_);
lean_dec(v_a_632_);
v___x_640_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v___x_638_, v___x_639_, v___f_627_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_640_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec_ref(v___f_627_);
v_a_641_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_631_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_631_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v___f_627_);
v_a_649_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_629_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_629_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v___x_657_; 
lean_dec_ref_known(v_mask_615_, 2);
lean_dec(v_todo_616_);
lean_dec_ref(v_ctor_610_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
v___x_657_ = lean_apply_9(v_k_611_, v_acc_617_, v_indices_613_, v_zs_612_, v_zs2_614_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, lean_box(0));
return v___x_657_;
}
}
else
{
if (lean_obj_tag(v_todo_616_) == 1)
{
lean_object* v_tail_658_; lean_object* v_head_659_; lean_object* v_tail_660_; lean_object* v___x_661_; 
v_tail_658_ = lean_ctor_get(v_mask_615_, 1);
lean_inc(v_tail_658_);
lean_dec_ref_known(v_mask_615_, 2);
v_head_659_ = lean_ctor_get(v_todo_616_, 0);
lean_inc(v_head_659_);
v_tail_660_ = lean_ctor_get(v_todo_616_, 1);
lean_inc(v_tail_660_);
lean_dec_ref_known(v_todo_616_, 2);
v___x_661_ = lean_array_push(v_zs2_614_, v_head_659_);
v_zs2_614_ = v___x_661_;
v_mask_615_ = v_tail_658_;
v_todo_616_ = v_tail_660_;
goto _start;
}
else
{
lean_object* v___x_663_; 
lean_dec_ref_known(v_mask_615_, 2);
lean_dec(v_todo_616_);
lean_dec_ref(v_ctor_610_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
v___x_663_ = lean_apply_9(v_k_611_, v_acc_617_, v_indices_613_, v_zs_612_, v_zs2_614_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, lean_box(0));
return v___x_663_;
}
}
}
else
{
lean_object* v___x_664_; 
lean_dec(v_todo_616_);
lean_dec(v_mask_615_);
lean_dec_ref(v_ctor_610_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
v___x_664_ = lean_apply_9(v_k_611_, v_acc_617_, v_indices_613_, v_zs_612_, v_zs2_614_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, lean_box(0));
return v___x_664_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_610_ = stack[0].m_obj;
lean_object* v_k_611_ = stack[1].m_obj;
lean_object* v_zs_612_ = stack[2].m_obj;
lean_object* v_indices_613_ = stack[3].m_obj;
lean_object* v_zs2_614_ = stack[4].m_obj;
lean_object* v_mask_615_ = stack[5].m_obj;
lean_object* v_todo_616_ = stack[6].m_obj;
lean_object* v_acc_617_ = stack[7].m_obj;
lean_object* v_a_618_ = stack[8].m_obj;
lean_object* v_a_619_ = stack[9].m_obj;
lean_object* v_a_620_ = stack[10].m_obj;
lean_object* v_a_621_ = stack[11].m_obj;
lean_object* v_res_665_;
v_res_665_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_610_, v_k_611_, v_zs_612_, v_indices_613_, v_zs2_614_, v_mask_615_, v_todo_616_, v_acc_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
stack->m_obj
 = v_res_665_;
}
lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(lean_object* v_zs2_666_, lean_object* v_acc_667_, lean_object* v_ctor_668_, lean_object* v_k_669_, lean_object* v_zs_670_, lean_object* v_indices_671_, lean_object* v_tail_672_, lean_object* v_tail_673_, lean_object* v_z_x27_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_inc_ref(v_z_x27_674_);
v___x_680_ = lean_array_push(v_zs2_666_, v_z_x27_674_);
v___x_681_ = lean_array_push(v_acc_667_, v_z_x27_674_);
v___x_682_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_668_, v_k_669_, v_zs_670_, v_indices_671_, v___x_680_, v_tail_672_, v_tail_673_, v___x_681_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_682_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_zs2_666_ = stack[0].m_obj;
lean_object* v_acc_667_ = stack[1].m_obj;
lean_object* v_ctor_668_ = stack[2].m_obj;
lean_object* v_k_669_ = stack[3].m_obj;
lean_object* v_zs_670_ = stack[4].m_obj;
lean_object* v_indices_671_ = stack[5].m_obj;
lean_object* v_tail_672_ = stack[6].m_obj;
lean_object* v_tail_673_ = stack[7].m_obj;
lean_object* v_z_x27_674_ = stack[8].m_obj;
lean_object* v___y_675_ = stack[9].m_obj;
lean_object* v___y_676_ = stack[10].m_obj;
lean_object* v___y_677_ = stack[11].m_obj;
lean_object* v___y_678_ = stack[12].m_obj;
lean_object* v_res_683_;
v_res_683_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___lam__0(v_zs2_666_, v_acc_667_, v_ctor_668_, v_k_669_, v_zs_670_, v_indices_671_, v_tail_672_, v_tail_673_, v_z_x27_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg___boxed(lean_object* v_ctor_684_, lean_object* v_k_685_, lean_object* v_zs_686_, lean_object* v_indices_687_, lean_object* v_zs2_688_, lean_object* v_mask_689_, lean_object* v_todo_690_, lean_object* v_acc_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_684_, v_k_685_, v_zs_686_, v_indices_687_, v_zs2_688_, v_mask_689_, v_todo_690_, v_acc_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_object* v_00_u03b1_698_, lean_object* v_ctor_699_, lean_object* v_k_700_, lean_object* v_zs_701_, lean_object* v_indices_702_, lean_object* v_zs2_703_, lean_object* v_mask_704_, lean_object* v_todo_705_, lean_object* v_acc_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_699_, v_k_700_, v_zs_701_, v_indices_702_, v_zs2_703_, v_mask_704_, v_todo_705_, v_acc_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_712_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_699_ = stack[1].m_obj;
lean_object* v_k_700_ = stack[2].m_obj;
lean_object* v_zs_701_ = stack[3].m_obj;
lean_object* v_indices_702_ = stack[4].m_obj;
lean_object* v_zs2_703_ = stack[5].m_obj;
lean_object* v_mask_704_ = stack[6].m_obj;
lean_object* v_todo_705_ = stack[7].m_obj;
lean_object* v_acc_706_ = stack[8].m_obj;
lean_object* v_a_707_ = stack[9].m_obj;
lean_object* v_a_708_ = stack[10].m_obj;
lean_object* v_a_709_ = stack[11].m_obj;
lean_object* v_a_710_ = stack[12].m_obj;
lean_object* v_res_713_;
v_res_713_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(lean_box(0), v_ctor_699_, v_k_700_, v_zs_701_, v_indices_702_, v_zs2_703_, v_mask_704_, v_todo_705_, v_acc_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
stack->m_obj
 = v_res_713_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___boxed(lean_object* v_00_u03b1_714_, lean_object* v_ctor_715_, lean_object* v_k_716_, lean_object* v_zs_717_, lean_object* v_indices_718_, lean_object* v_zs2_719_, lean_object* v_mask_720_, lean_object* v_todo_721_, lean_object* v_acc_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go(v_00_u03b1_714_, v_ctor_715_, v_k_716_, v_zs_717_, v_indices_718_, v_zs2_719_, v_mask_720_, v_todo_721_, v_acc_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
return v_res_728_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_object* v_00_u03b1_729_, lean_object* v_name_730_, uint8_t v_bi_731_, lean_object* v_type_732_, lean_object* v_k_733_, uint8_t v_kind_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___redArg(v_name_730_, v_bi_731_, v_type_732_, v_k_733_, v_kind_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_730_ = stack[1].m_obj;
uint8_t v_bi_731_ = stack[2].m_num;
lean_object* v_type_732_ = stack[3].m_obj;
lean_object* v_k_733_ = stack[4].m_obj;
uint8_t v_kind_734_ = stack[5].m_num;
lean_object* v___y_735_ = stack[6].m_obj;
lean_object* v___y_736_ = stack[7].m_obj;
lean_object* v___y_737_ = stack[8].m_obj;
lean_object* v___y_738_ = stack[9].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(lean_box(0), v_name_730_, v_bi_731_, v_type_732_, v_k_733_, v_kind_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1___boxed(lean_object* v_00_u03b1_742_, lean_object* v_name_743_, lean_object* v_bi_744_, lean_object* v_type_745_, lean_object* v_k_746_, lean_object* v_kind_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v_bi_boxed_753_; uint8_t v_kind_boxed_754_; lean_object* v_res_755_; 
v_bi_boxed_753_ = lean_unbox(v_bi_744_);
v_kind_boxed_754_ = lean_unbox(v_kind_747_);
v_res_755_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_spec__1(v_00_u03b1_742_, v_name_743_, v_bi_boxed_753_, v_type_745_, v_k_746_, v_kind_boxed_754_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_755_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_object* v_00_u03b1_756_, lean_object* v_name_757_, lean_object* v_type_758_, lean_object* v_k_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___redArg(v_name_757_, v_type_758_, v_k_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_765_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_757_ = stack[1].m_obj;
lean_object* v_type_758_ = stack[2].m_obj;
lean_object* v_k_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(lean_box(0), v_name_757_, v_type_758_, v_k_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1___boxed(lean_object* v_00_u03b1_767_, lean_object* v_name_768_, lean_object* v_type_769_, lean_object* v_k_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go_spec__1(v_00_u03b1_767_, v_name_768_, v_type_769_, v_k_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_776_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(lean_object* v_type_777_, lean_object* v_k_778_, uint8_t v_cleanupAnnotations_779_, uint8_t v_whnfType_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___f_786_; lean_object* v___x_787_; 
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_occursInCtorTypeMask_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_786_, 0, v_k_778_);
v___x_787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_777_, v___f_786_, v_cleanupAnnotations_779_, v_whnfType_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_787_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_787_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_777_ = stack[0].m_obj;
lean_object* v_k_778_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_779_ = stack[2].m_num;
uint8_t v_whnfType_780_ = stack[3].m_num;
lean_object* v___y_781_ = stack[4].m_obj;
lean_object* v___y_782_ = stack[5].m_obj;
lean_object* v___y_783_ = stack[6].m_obj;
lean_object* v___y_784_ = stack[7].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_777_, v_k_778_, v_cleanupAnnotations_779_, v_whnfType_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg___boxed(lean_object* v_type_805_, lean_object* v_k_806_, lean_object* v_cleanupAnnotations_807_, lean_object* v_whnfType_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_814_; uint8_t v_whnfType_boxed_815_; lean_object* v_res_816_; 
v_cleanupAnnotations_boxed_814_ = lean_unbox(v_cleanupAnnotations_807_);
v_whnfType_boxed_815_ = lean_unbox(v_whnfType_808_);
v_res_816_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_805_, v_k_806_, v_cleanupAnnotations_boxed_814_, v_whnfType_boxed_815_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_816_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_object* v_00_u03b1_817_, lean_object* v_type_818_, lean_object* v_k_819_, uint8_t v_cleanupAnnotations_820_, uint8_t v_whnfType_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_type_818_, v_k_819_, v_cleanupAnnotations_820_, v_whnfType_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_818_ = stack[1].m_obj;
lean_object* v_k_819_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_820_ = stack[3].m_num;
uint8_t v_whnfType_821_ = stack[4].m_num;
lean_object* v___y_822_ = stack[5].m_obj;
lean_object* v___y_823_ = stack[6].m_obj;
lean_object* v___y_824_ = stack[7].m_obj;
lean_object* v___y_825_ = stack[8].m_obj;
lean_object* v_res_828_;
v_res_828_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(lean_box(0), v_type_818_, v_k_819_, v_cleanupAnnotations_820_, v_whnfType_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
stack->m_obj
 = v_res_828_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___boxed(lean_object* v_00_u03b1_829_, lean_object* v_type_830_, lean_object* v_k_831_, lean_object* v_cleanupAnnotations_832_, lean_object* v_whnfType_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_839_; uint8_t v_whnfType_boxed_840_; lean_object* v_res_841_; 
v_cleanupAnnotations_boxed_839_ = lean_unbox(v_cleanupAnnotations_832_);
v_whnfType_boxed_840_ = lean_unbox(v_whnfType_833_);
v_res_841_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1(v_00_u03b1_829_, v_type_830_, v_k_831_, v_cleanupAnnotations_boxed_839_, v_whnfType_boxed_840_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_841_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__0));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(lean_object* v_constName_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_env_852_; lean_object* v___x_853_; 
v___x_851_ = lean_st_ref_get(v___y_849_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc_ref(v_env_852_);
lean_dec(v___x_851_);
lean_inc(v_constName_845_);
v___x_853_ = l_Lean_isInductiveCore_x3f(v_env_852_, v_constName_845_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_854_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1___closed__1);
v___x_855_ = 0;
v___x_856_ = l_Lean_MessageData_ofConstName(v_constName_845_, v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_854_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___closed__1);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_occursInCtorTypeMask_spec__1_spec__1___redArg(v___x_859_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_constName_845_);
v_val_861_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_853_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v___x_853_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 0);
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_val_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_845_ = stack[0].m_obj;
lean_object* v___y_846_ = stack[1].m_obj;
lean_object* v___y_847_ = stack[2].m_obj;
lean_object* v___y_848_ = stack[3].m_obj;
lean_object* v___y_849_ = stack[4].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v_constName_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0___boxed(lean_object* v_constName_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v_constName_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
static lean_object* _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_877_; lean_object* v_dummy_878_; 
v___x_877_ = lean_box(0);
v_dummy_878_ = l_Lean_Expr_sort___override(v___x_877_);
return v_dummy_878_;
}
}
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(lean_object* v_ctor_881_, lean_object* v_k_882_, lean_object* v_zs_883_, lean_object* v_ctorRet_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
v___x_890_ = lean_whnf(v_ctorRet_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Lean_Core_betaReduce(v_a_891_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_Expr_getAppFn(v_a_893_);
v___x_895_ = l_Lean_Expr_constName_x21(v___x_894_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_withSharedCtorIndices_spec__0(v___x_895_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_numIndices_898_; lean_object* v_dummy_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v_numIndices_898_ = lean_ctor_get(v_a_897_, 2);
lean_inc_n(v_numIndices_898_, 2);
lean_dec(v_a_897_);
v_dummy_899_ = lean_obj_once(&l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0, &l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__0);
v___x_900_ = lean_mk_array(v_numIndices_898_, v_dummy_899_);
v___x_901_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_898_, v_a_893_, v___x_900_);
v___x_902_ = l_Lean_Expr_getAppFn(v_ctor_881_);
v___x_903_ = l_Lean_Expr_constName_x21(v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_Meta_occursInCtorTypeMask(v___x_903_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = ((lean_object*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___closed__1));
v___x_907_ = lean_array_to_list(v_a_905_);
lean_inc_ref_n(v_zs_883_, 2);
v___x_908_ = lean_array_to_list(v_zs_883_);
v___x_909_ = l___private_Lean_Meta_SameCtorUtils_0__Lean_Meta_withSharedCtorIndices_go___redArg(v_ctor_881_, v_k_882_, v_zs_883_, v___x_901_, v___x_906_, v___x_907_, v___x_908_, v_zs_883_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref(v___x_901_);
lean_dec_ref(v_zs_883_);
lean_dec_ref(v_k_882_);
lean_dec_ref(v_ctor_881_);
v_a_910_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_904_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_904_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_893_);
lean_dec_ref(v_zs_883_);
lean_dec_ref(v_k_882_);
lean_dec_ref(v_ctor_881_);
v_a_918_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_896_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_896_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_zs_883_);
lean_dec_ref(v_k_882_);
lean_dec_ref(v_ctor_881_);
v_a_926_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_892_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_892_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_zs_883_);
lean_dec_ref(v_k_882_);
lean_dec_ref(v_ctor_881_);
v_a_934_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_890_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_890_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withSharedCtorIndices___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_881_ = stack[0].m_obj;
lean_object* v_k_882_ = stack[1].m_obj;
lean_object* v_zs_883_ = stack[2].m_obj;
lean_object* v_ctorRet_884_ = stack[3].m_obj;
lean_object* v___y_885_ = stack[4].m_obj;
lean_object* v___y_886_ = stack[5].m_obj;
lean_object* v___y_887_ = stack[6].m_obj;
lean_object* v___y_888_ = stack[7].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(v_ctor_881_, v_k_882_, v_zs_883_, v_ctorRet_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed(lean_object* v_ctor_943_, lean_object* v_k_944_, lean_object* v_zs_945_, lean_object* v_ctorRet_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Meta_withSharedCtorIndices___redArg___lam__0(v_ctor_943_, v_k_944_, v_zs_945_, v_ctorRet_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
return v_res_952_;
}
}
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object* v_ctor_953_, lean_object* v_k_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___f_960_; lean_object* v___x_961_; 
lean_inc_ref(v_ctor_953_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Meta_withSharedCtorIndices___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_960_, 0, v_ctor_953_);
lean_closure_set(v___f_960_, 1, v_k_954_);
lean_inc(v_a_958_);
lean_inc_ref(v_a_957_);
lean_inc(v_a_956_);
lean_inc_ref(v_a_955_);
v___x_961_ = lean_infer_type(v_ctor_953_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = 0;
v___x_964_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_withSharedCtorIndices_spec__1___redArg(v_a_962_, v___f_960_, v___x_963_, v___x_963_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_964_;
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v___f_960_);
v_a_965_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_961_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withSharedCtorIndices___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_953_ = stack[0].m_obj;
lean_object* v_k_954_ = stack[1].m_obj;
lean_object* v_a_955_ = stack[2].m_obj;
lean_object* v_a_956_ = stack[3].m_obj;
lean_object* v_a_957_ = stack[4].m_obj;
lean_object* v_a_958_ = stack[5].m_obj;
lean_object* v_res_973_;
v_res_973_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_953_, v_k_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___redArg___boxed(lean_object* v_ctor_974_, lean_object* v_k_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_974_, v_k_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_981_;
}
}
lean_object* l_Lean_Meta_withSharedCtorIndices(lean_object* v_00_u03b1_982_, lean_object* v_ctor_983_, lean_object* v_k_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_withSharedCtorIndices___redArg(v_ctor_983_, v_k_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_990_;
}
}
LEAN_EXPORT void l_Lean_Meta_withSharedCtorIndices_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctor_983_ = stack[1].m_obj;
lean_object* v_k_984_ = stack[2].m_obj;
lean_object* v_a_985_ = stack[3].m_obj;
lean_object* v_a_986_ = stack[4].m_obj;
lean_object* v_a_987_ = stack[5].m_obj;
lean_object* v_a_988_ = stack[6].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_Lean_Meta_withSharedCtorIndices(lean_box(0), v_ctor_983_, v_k_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSharedCtorIndices___boxed(lean_object* v_00_u03b1_992_, lean_object* v_ctor_993_, lean_object* v_k_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_withSharedCtorIndices(v_00_u03b1_992_, v_ctor_993_, v_k_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_1000_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_SameCtorUtils(builtin);
}
#ifdef __cplusplus
}
#endif
