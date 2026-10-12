// Lean compiler output
// Module: Lean.Elab.Open
// Imports: public import Lean.Elab.Util public import Lean.Parser.Command meta import Lean.Parser.Command public import Lean.Linter.AmbiguousOpen import Init.Omega
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
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instMonadOptionsOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_bind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instFunctorOption___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__0_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__1_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__7_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__2_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__3_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__4_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__5_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__8_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__6_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9_value;
static const lean_string_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous identifier `"};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10_value;
static lean_once_cell_t l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11;
static const lean_string_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`, possible interpretations: "};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12_value;
static lean_once_cell_t l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13;
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "failed to open"};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__0_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1_value;
static lean_once_cell_t l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0_value;
static const lean_array_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value),((lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "openRenamingItem"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "openOnly"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openHiding"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "openRenaming"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__3_value;
static const lean_array_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__4_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed__const__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__3_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFunctorOption___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_map, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__5_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__4_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__6_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__3_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__7_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_bind, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__7_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__8_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getId___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_____do__lift_2_, lean_object* v___y_3_){
_start:
{
lean_object* v_toApplicative_4_; lean_object* v_currNamespace_5_; lean_object* v_toPure_6_; lean_object* v___x_7_; 
v_toApplicative_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_4_);
lean_dec_ref(v_inst_1_);
v_currNamespace_5_ = lean_ctor_get(v_____do__lift_2_, 1);
lean_inc(v_currNamespace_5_);
lean_dec_ref(v_____do__lift_2_);
v_toPure_6_ = lean_ctor_get(v_toApplicative_4_, 1);
lean_inc(v_toPure_6_);
lean_dec_ref(v_toApplicative_4_);
v___x_7_ = lean_apply_2(v_toPure_6_, lean_box(0), v_currNamespace_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(lean_object* v_inst_8_, lean_object* v_____do__lift_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(v_inst_8_, v_____do__lift_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(lean_object* v_inst_12_, lean_object* v_____do__lift_13_, lean_object* v___y_14_){
_start:
{
lean_object* v_toApplicative_15_; lean_object* v_openDecls_16_; lean_object* v_toPure_17_; lean_object* v___x_18_; 
v_toApplicative_15_ = lean_ctor_get(v_inst_12_, 0);
lean_inc_ref(v_toApplicative_15_);
lean_dec_ref(v_inst_12_);
v_openDecls_16_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_openDecls_16_);
lean_dec_ref(v_____do__lift_13_);
v_toPure_17_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_inc(v_toPure_17_);
lean_dec_ref(v_toApplicative_15_);
v___x_18_ = lean_apply_2(v_toPure_17_, lean_box(0), v_openDecls_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(lean_object* v_inst_19_, lean_object* v_____do__lift_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(v_inst_19_, v_____do__lift_20_, v___y_21_);
lean_dec(v___y_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_inc_ref_n(v_inst_23_, 3);
v___f_25_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_25_, 0, v_inst_23_);
v___f_26_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_26_, 0, v_inst_23_);
v___x_27_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_27_, 0, lean_box(0));
lean_closure_set(v___x_27_, 1, lean_box(0));
lean_closure_set(v___x_27_, 2, lean_box(0));
lean_closure_set(v___x_27_, 3, v_inst_24_);
lean_inc_ref(v___x_27_);
v___x_28_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_28_, 0, lean_box(0));
lean_closure_set(v___x_28_, 1, lean_box(0));
lean_closure_set(v___x_28_, 2, v_inst_23_);
lean_closure_set(v___x_28_, 3, lean_box(0));
lean_closure_set(v___x_28_, 4, lean_box(0));
lean_closure_set(v___x_28_, 5, v___x_27_);
lean_closure_set(v___x_28_, 6, v___f_25_);
v___x_29_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_29_, 0, lean_box(0));
lean_closure_set(v___x_29_, 1, lean_box(0));
lean_closure_set(v___x_29_, 2, v_inst_23_);
lean_closure_set(v___x_29_, 3, lean_box(0));
lean_closure_set(v___x_29_, 4, lean_box(0));
lean_closure_set(v___x_29_, 5, v___x_27_);
lean_closure_set(v___x_29_, 6, v___f_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM(lean_object* v_m_31_, lean_object* v_inst_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_32_, v_inst_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(lean_object* v_idStx_35_, lean_object* v_withRef_36_, lean_object* v___x_37_, lean_object* v_oldRef_38_){
_start:
{
lean_object* v_ref_39_; lean_object* v___x_40_; 
v_ref_39_ = l_Lean_replaceRef(v_idStx_35_, v_oldRef_38_);
v___x_40_ = lean_apply_3(v_withRef_36_, lean_box(0), v_ref_39_, v___x_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(lean_object* v_idStx_41_, lean_object* v_withRef_42_, lean_object* v___x_43_, lean_object* v_oldRef_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(v_idStx_41_, v_withRef_42_, v___x_43_, v_oldRef_44_);
lean_dec(v_oldRef_44_);
lean_dec(v_idStx_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(lean_object* v_declName_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v___x_54_, lean_object* v_idStx_55_, lean_object* v_toBind_56_, lean_object* v_toPure_57_, lean_object* v_____do__lift_58_){
_start:
{
uint8_t v___x_59_; uint8_t v___x_60_; 
v___x_59_ = 1;
lean_inc(v_declName_46_);
v___x_60_ = l_Lean_Environment_contains(v_____do__lift_58_, v_declName_46_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v_getRef_61_; lean_object* v_withRef_62_; lean_object* v___x_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
lean_dec(v_toPure_57_);
v_getRef_61_ = lean_ctor_get(v_inst_47_, 0);
lean_inc(v_getRef_61_);
v_withRef_62_ = lean_ctor_get(v_inst_47_, 1);
lean_inc(v_withRef_62_);
lean_dec_ref(v_inst_47_);
v___x_63_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_48_, v_inst_49_, v_inst_50_, v_inst_51_, v_inst_52_, v_inst_53_, v___x_54_, v_declName_46_);
v___f_64_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_64_, 0, v_idStx_55_);
lean_closure_set(v___f_64_, 1, v_withRef_62_);
lean_closure_set(v___f_64_, 2, v___x_63_);
v___x_65_ = lean_apply_4(v_toBind_56_, lean_box(0), lean_box(0), v_getRef_61_, v___f_64_);
return v___x_65_;
}
else
{
lean_object* v___x_66_; 
lean_dec(v_toBind_56_);
lean_dec(v_idStx_55_);
lean_dec_ref(v___x_54_);
lean_dec(v_inst_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
v___x_66_ = lean_apply_2(v_toPure_57_, lean_box(0), v_declName_46_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_ns_76_, lean_object* v_idStx_77_){
_start:
{
lean_object* v_toApplicative_78_; lean_object* v_toBind_79_; lean_object* v_getEnv_80_; lean_object* v___x_81_; lean_object* v_toPure_82_; lean_object* v___x_83_; lean_object* v_declName_84_; lean_object* v___f_85_; lean_object* v___x_86_; 
v_toApplicative_78_ = lean_ctor_get(v_inst_67_, 0);
v_toBind_79_ = lean_ctor_get(v_inst_67_, 1);
lean_inc_n(v_toBind_79_, 2);
v_getEnv_80_ = lean_ctor_get(v_inst_68_, 0);
lean_inc(v_getEnv_80_);
lean_inc_ref(v_inst_70_);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v_inst_69_);
lean_ctor_set(v___x_81_, 1, v_inst_70_);
lean_ctor_set(v___x_81_, 2, v_inst_71_);
v_toPure_82_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_82_);
v___x_83_ = l_Lean_Syntax_getId(v_idStx_77_);
v_declName_84_ = l_Lean_Name_append(v_ns_76_, v___x_83_);
v___f_85_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1), 13, 12);
lean_closure_set(v___f_85_, 0, v_declName_84_);
lean_closure_set(v___f_85_, 1, v_inst_70_);
lean_closure_set(v___f_85_, 2, v_inst_67_);
lean_closure_set(v___f_85_, 3, v_inst_75_);
lean_closure_set(v___f_85_, 4, v_inst_68_);
lean_closure_set(v___f_85_, 5, v_inst_74_);
lean_closure_set(v___f_85_, 6, v_inst_73_);
lean_closure_set(v___f_85_, 7, v_inst_72_);
lean_closure_set(v___f_85_, 8, v___x_81_);
lean_closure_set(v___f_85_, 9, v_idStx_77_);
lean_closure_set(v___f_85_, 10, v_toBind_79_);
lean_closure_set(v___f_85_, 11, v_toPure_82_);
v___x_86_ = lean_apply_4(v_toBind_79_, lean_box(0), lean_box(0), v_getEnv_80_, v___f_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId(lean_object* v_m_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_ns_97_, lean_object* v_idStx_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v_inst_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_inst_96_, v_ns_97_, v_idStx_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0(lean_object* v_decl_100_, lean_object* v_s_101_){
_start:
{
lean_object* v_openDecls_102_; lean_object* v_currNamespace_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_113_; 
v_openDecls_102_ = lean_ctor_get(v_s_101_, 0);
v_currNamespace_103_ = lean_ctor_get(v_s_101_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_s_101_);
if (v_isSharedCheck_113_ == 0)
{
v___x_105_ = v_s_101_;
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_currNamespace_103_);
lean_inc(v_openDecls_102_);
lean_dec(v_s_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_108_, 0, v_decl_100_);
lean_ctor_set(v___x_108_, 1, v_openDecls_102_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_108_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_currNamespace_103_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; 
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_107_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(lean_object* v_inst_114_, lean_object* v_decl_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___f_117_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_117_, 0, v_decl_115_);
lean_inc(v_a_116_);
v___x_118_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_118_, 0, lean_box(0));
lean_closure_set(v___x_118_, 1, lean_box(0));
lean_closure_set(v___x_118_, 2, lean_box(0));
lean_closure_set(v___x_118_, 3, v_a_116_);
lean_closure_set(v___x_118_, 4, v___f_117_);
v___x_119_ = lean_apply_2(v_inst_114_, lean_box(0), v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(lean_object* v_inst_120_, lean_object* v_decl_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_120_, v_decl_121_, v_a_122_);
lean_dec(v_a_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(lean_object* v_m_124_, lean_object* v_inst_125_, lean_object* v_decl_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_125_, v_decl_126_, v_a_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(lean_object* v_m_129_, lean_object* v_inst_130_, lean_object* v_decl_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(v_m_129_, v_inst_130_, v_decl_131_, v_a_132_);
lean_dec(v_a_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Lean_mkConst(v_x_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(lean_object* v_toPure_137_, lean_object* v_p_138_){
_start:
{
lean_object* v_snd_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_150_; 
v_snd_139_ = lean_ctor_get(v_p_138_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v_p_138_);
v_fst_140_ = lean_ctor_get(v_snd_139_, 0);
v_snd_141_ = lean_ctor_get(v_snd_139_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_snd_139_);
if (v_isSharedCheck_150_ == 0)
{
v___x_143_ = v_snd_139_;
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snd_141_);
lean_inc(v_fst_140_);
lean_dec(v_snd_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_fst_140_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_snd_141_);
v___x_146_ = v_reuseFailAlloc_149_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
v___x_148_ = lean_apply_2(v_toPure_137_, lean_box(0), v___x_147_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(lean_object* v_snd_151_, lean_object* v_fst_152_, lean_object* v_toPure_153_, lean_object* v_declName_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_155_ = lean_array_push(v_snd_151_, v_declName_154_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_fst_152_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_apply_2(v_toPure_153_, lean_box(0), v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(lean_object* v_fst_160_, lean_object* v_snd_161_, lean_object* v_toPure_162_, lean_object* v_ex_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = lean_array_push(v_fst_160_, v_ex_163_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v_snd_161_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_apply_2(v_toPure_162_, lean_box(0), v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(lean_object* v_inst_169_, lean_object* v_toPure_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_idStx_179_, lean_object* v_toBind_180_, lean_object* v___f_181_, lean_object* v_a_182_, lean_object* v_x_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v_tryCatch_187_; lean_object* v___f_188_; lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_fst_185_ = lean_ctor_get(v___y_184_, 0);
lean_inc_n(v_fst_185_, 2);
v_snd_186_ = lean_ctor_get(v___y_184_, 1);
lean_inc_n(v_snd_186_, 2);
lean_dec_ref(v___y_184_);
v_tryCatch_187_ = lean_ctor_get(v_inst_169_, 1);
lean_inc(v_tryCatch_187_);
lean_inc(v_toPure_170_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2), 4, 3);
lean_closure_set(v___f_188_, 0, v_snd_186_);
lean_closure_set(v___f_188_, 1, v_fst_185_);
lean_closure_set(v___f_188_, 2, v_toPure_170_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_189_, 0, v_fst_185_);
lean_closure_set(v___f_189_, 1, v_snd_186_);
lean_closure_set(v___f_189_, 2, v_toPure_170_);
v___x_190_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v_inst_171_, v_inst_172_, v_inst_169_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_, v_inst_177_, v_inst_178_, v_a_182_, v_idStx_179_);
lean_inc(v_toBind_180_);
v___x_191_ = lean_apply_4(v_toBind_180_, lean_box(0), lean_box(0), v___x_190_, v___f_188_);
v___x_192_ = lean_apply_3(v_tryCatch_187_, lean_box(0), v___x_191_, v___f_189_);
v___x_193_ = lean_apply_4(v_toBind_180_, lean_box(0), lean_box(0), v___x_192_, v___f_181_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12));
v___x_218_ = l_Lean_stringToMessageData(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(lean_object* v_snd_220_, lean_object* v_inst_221_, lean_object* v_idStx_222_, lean_object* v___f_223_, lean_object* v_inst_224_, lean_object* v___x_225_, lean_object* v_toBind_226_, lean_object* v___x_227_, lean_object* v_toPure_228_, lean_object* v_____r_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_array_get_size(v_snd_220_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v_getRef_234_; lean_object* v_withRef_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_toPure_228_);
v___x_233_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_getRef_234_ = lean_ctor_get(v_inst_221_, 0);
v_withRef_235_ = lean_ctor_get(v_inst_221_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_inst_221_);
if (v_isSharedCheck_259_ == 0)
{
v___x_237_ = v_inst_221_;
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_withRef_235_);
lean_inc(v_getRef_234_);
lean_dec(v_inst_221_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_259_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
size_t v_sz_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v_sz_239_ = lean_array_size(v_snd_220_);
v___x_240_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
v___x_241_ = l_Lean_Syntax_getId(v_idStx_222_);
v___x_242_ = l_Lean_MessageData_ofName(v___x_241_);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 7);
lean_ctor_set(v___x_237_, 1, v___x_242_);
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_244_ = v___x_237_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_258_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; size_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___f_256_; lean_object* v___x_257_; 
v___x_245_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = ((size_t)0ULL);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_233_, v___f_223_, v_sz_239_, v___x_247_, v_snd_220_);
v___x_249_ = lean_array_to_list(v___x_248_);
v___x_250_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14));
v___x_251_ = lean_box(0);
v___x_252_ = l_List_mapTR_loop___redArg(v___x_250_, v___x_249_, v___x_251_);
v___x_253_ = l_Lean_MessageData_ofList(v___x_252_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_246_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = l_Lean_throwError___redArg(v_inst_224_, v___x_225_, v___x_254_);
v___f_256_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_256_, 0, v_idStx_222_);
lean_closure_set(v___f_256_, 1, v_withRef_235_);
lean_closure_set(v___f_256_, 2, v___x_255_);
v___x_257_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v_getRef_234_, v___f_256_);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_toBind_226_);
lean_dec_ref(v___x_225_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v___f_223_);
lean_dec(v_idStx_222_);
lean_dec_ref(v_inst_221_);
v___x_260_ = lean_array_fget(v_snd_220_, v___x_227_);
lean_dec(v_snd_220_);
v___x_261_ = lean_apply_2(v_toPure_228_, lean_box(0), v___x_260_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(lean_object* v_snd_262_, lean_object* v_inst_263_, lean_object* v_idStx_264_, lean_object* v___f_265_, lean_object* v_inst_266_, lean_object* v___x_267_, lean_object* v_toBind_268_, lean_object* v___x_269_, lean_object* v_toPure_270_, lean_object* v_____r_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_262_, v_inst_263_, v_idStx_264_, v___f_265_, v_inst_266_, v___x_267_, v_toBind_268_, v___x_269_, v_toPure_270_, v_____r_271_);
lean_dec(v___x_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(lean_object* v___f_273_, lean_object* v_____r_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_apply_1(v___f_273_, v_____r_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(lean_object* v_idStx_276_, lean_object* v_withRef_277_, lean_object* v___y_278_, lean_object* v_oldRef_279_){
_start:
{
lean_object* v_ref_280_; lean_object* v___x_281_; 
v_ref_280_ = l_Lean_replaceRef(v_idStx_276_, v_oldRef_279_);
v___x_281_ = lean_apply_3(v_withRef_277_, lean_box(0), v_ref_280_, v___y_278_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(lean_object* v_idStx_282_, lean_object* v_withRef_283_, lean_object* v___y_284_, lean_object* v_oldRef_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(v_idStx_282_, v_withRef_283_, v___y_284_, v_oldRef_285_);
lean_dec(v_oldRef_285_);
lean_dec(v_idStx_282_);
return v_res_286_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1));
v___x_291_ = l_Lean_MessageData_ofFormat(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(lean_object* v_inst_292_, lean_object* v_idStx_293_, lean_object* v___f_294_, lean_object* v_inst_295_, lean_object* v___x_296_, lean_object* v_toBind_297_, lean_object* v___x_298_, lean_object* v_toPure_299_, lean_object* v_nss_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_____s_303_){
_start:
{
lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_fst_304_ = lean_ctor_get(v_____s_303_, 0);
lean_inc(v_fst_304_);
v_snd_305_ = lean_ctor_get(v_____s_303_, 1);
lean_inc_n(v_snd_305_, 2);
lean_dec_ref(v_____s_303_);
lean_inc(v_toPure_299_);
lean_inc(v___x_298_);
lean_inc(v_toBind_297_);
lean_inc_ref(v___x_296_);
lean_inc_ref(v_inst_295_);
lean_inc_ref(v___f_294_);
lean_inc(v_idStx_293_);
lean_inc_ref(v_inst_292_);
v___f_306_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_306_, 0, v_snd_305_);
lean_closure_set(v___f_306_, 1, v_inst_292_);
lean_closure_set(v___f_306_, 2, v_idStx_293_);
lean_closure_set(v___f_306_, 3, v___f_294_);
lean_closure_set(v___f_306_, 4, v_inst_295_);
lean_closure_set(v___f_306_, 5, v___x_296_);
lean_closure_set(v___f_306_, 6, v_toBind_297_);
lean_closure_set(v___f_306_, 7, v___x_298_);
lean_closure_set(v___f_306_, 8, v_toPure_299_);
v___x_307_ = lean_array_get_size(v_fst_304_);
v___x_308_ = l_List_lengthTR___redArg(v_nss_300_);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
lean_dec(v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v___f_306_);
lean_dec(v_fst_304_);
lean_dec_ref(v_inst_302_);
lean_dec_ref(v_inst_301_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_305_, v_inst_292_, v_idStx_293_, v___f_294_, v_inst_295_, v___x_296_, v_toBind_297_, v___x_298_, v_toPure_299_, v___x_310_);
lean_dec(v___x_298_);
return v___x_311_;
}
else
{
lean_object* v___f_312_; lean_object* v___y_314_; lean_object* v___x_320_; uint8_t v___x_321_; 
lean_dec(v_snd_305_);
lean_dec(v_toPure_299_);
lean_dec_ref(v___f_294_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5), 2, 1);
lean_closure_set(v___f_312_, 0, v___f_306_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_dec_eq(v___x_307_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_inst_302_);
lean_dec(v___x_298_);
v___x_322_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
v___x_323_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v___x_296_, v_inst_295_, v_inst_301_, v___x_322_, v_fst_304_);
v___y_314_ = v___x_323_;
goto v___jp_313_;
}
else
{
lean_object* v_throw_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec_ref(v_inst_301_);
lean_dec_ref(v___x_296_);
lean_dec_ref(v_inst_295_);
v_throw_324_ = lean_ctor_get(v_inst_302_, 0);
lean_inc(v_throw_324_);
lean_dec_ref(v_inst_302_);
v___x_325_ = lean_array_fget(v_fst_304_, v___x_298_);
lean_dec(v___x_298_);
lean_dec(v_fst_304_);
v___x_326_ = lean_apply_2(v_throw_324_, lean_box(0), v___x_325_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
v___jp_313_:
{
lean_object* v_getRef_315_; lean_object* v_withRef_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_getRef_315_ = lean_ctor_get(v_inst_292_, 0);
lean_inc(v_getRef_315_);
v_withRef_316_ = lean_ctor_get(v_inst_292_, 1);
lean_inc(v_withRef_316_);
lean_dec_ref(v_inst_292_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_317_, 0, v_idStx_293_);
lean_closure_set(v___f_317_, 1, v_withRef_316_);
lean_closure_set(v___f_317_, 2, v___y_314_);
lean_inc(v_toBind_297_);
v___x_318_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v_getRef_315_, v___f_317_);
v___x_319_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v___x_318_, v___f_312_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed(lean_object* v_inst_327_, lean_object* v_idStx_328_, lean_object* v___f_329_, lean_object* v_inst_330_, lean_object* v___x_331_, lean_object* v_toBind_332_, lean_object* v___x_333_, lean_object* v_toPure_334_, lean_object* v_nss_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_____s_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(v_inst_327_, v_idStx_328_, v___f_329_, v_inst_330_, v___x_331_, v_toBind_332_, v___x_333_, v_toPure_334_, v_nss_335_, v_inst_336_, v_inst_337_, v_____s_338_);
lean_dec(v_nss_335_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_nss_354_, lean_object* v_idStx_355_){
_start:
{
lean_object* v_toApplicative_356_; lean_object* v_toBind_357_; lean_object* v_toPure_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_toApplicative_356_ = lean_ctor_get(v_inst_345_, 0);
v_toBind_357_ = lean_ctor_get(v_inst_345_, 1);
lean_inc_n(v_toBind_357_, 3);
v_toPure_358_ = lean_ctor_get(v_toApplicative_356_, 1);
v___f_359_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0));
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2));
lean_inc_n(v_toPure_358_, 3);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_362_, 0, v_toPure_358_);
lean_inc(v_idStx_355_);
lean_inc_ref(v_inst_351_);
lean_inc(v_inst_349_);
lean_inc_ref_n(v_inst_348_, 2);
lean_inc_ref_n(v_inst_345_, 2);
lean_inc_ref_n(v_inst_347_, 2);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4), 16, 13);
lean_closure_set(v___f_363_, 0, v_inst_347_);
lean_closure_set(v___f_363_, 1, v_toPure_358_);
lean_closure_set(v___f_363_, 2, v_inst_345_);
lean_closure_set(v___f_363_, 3, v_inst_346_);
lean_closure_set(v___f_363_, 4, v_inst_348_);
lean_closure_set(v___f_363_, 5, v_inst_349_);
lean_closure_set(v___f_363_, 6, v_inst_350_);
lean_closure_set(v___f_363_, 7, v_inst_351_);
lean_closure_set(v___f_363_, 8, v_inst_352_);
lean_closure_set(v___f_363_, 9, v_inst_353_);
lean_closure_set(v___f_363_, 10, v_idStx_355_);
lean_closure_set(v___f_363_, 11, v_toBind_357_);
lean_closure_set(v___f_363_, 12, v___f_362_);
v___x_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_364_, 0, v_inst_347_);
lean_ctor_set(v___x_364_, 1, v_inst_348_);
lean_ctor_set(v___x_364_, 2, v_inst_349_);
lean_inc(v_nss_354_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed), 12, 11);
lean_closure_set(v___f_365_, 0, v_inst_348_);
lean_closure_set(v___f_365_, 1, v_idStx_355_);
lean_closure_set(v___f_365_, 2, v___f_359_);
lean_closure_set(v___f_365_, 3, v_inst_345_);
lean_closure_set(v___f_365_, 4, v___x_364_);
lean_closure_set(v___f_365_, 5, v_toBind_357_);
lean_closure_set(v___f_365_, 6, v___x_360_);
lean_closure_set(v___f_365_, 7, v_toPure_358_);
lean_closure_set(v___f_365_, 8, v_nss_354_);
lean_closure_set(v___f_365_, 9, v_inst_351_);
lean_closure_set(v___f_365_, 10, v_inst_347_);
v___x_366_ = l_List_forIn_x27_loop___redArg(v_inst_345_, v___f_363_, v_nss_354_, v___x_361_);
lean_dec(v_nss_354_);
v___x_367_ = lean_apply_4(v_toBind_357_, lean_box(0), lean_box(0), v___x_366_, v___f_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(lean_object* v_m_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_nss_378_, lean_object* v_idStx_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v_inst_369_, v_inst_370_, v_inst_371_, v_inst_372_, v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_inst_377_, v_nss_378_, v_idStx_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0(lean_object* v_toApplicative_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_openDecls_383_; lean_object* v_toPure_384_; lean_object* v___x_385_; 
v_openDecls_383_ = lean_ctor_get(v_a_382_, 0);
lean_inc(v_openDecls_383_);
lean_dec_ref(v_a_382_);
v_toPure_384_ = lean_ctor_get(v_toApplicative_381_, 1);
lean_inc(v_toPure_384_);
lean_dec_ref(v_toApplicative_381_);
v___x_385_ = lean_apply_2(v_toPure_384_, lean_box(0), v_openDecls_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(lean_object* v_inst_386_, lean_object* v_toBind_387_, lean_object* v___f_388_, lean_object* v_____r_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc(v___y_390_);
v___x_391_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, lean_box(0));
lean_closure_set(v___x_391_, 2, v___y_390_);
v___x_392_ = lean_apply_2(v_inst_386_, lean_box(0), v___x_391_);
v___x_393_ = lean_apply_4(v_toBind_387_, lean_box(0), lean_box(0), v___x_392_, v___f_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(lean_object* v_inst_394_, lean_object* v_toBind_395_, lean_object* v___f_396_, lean_object* v_____r_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(v_inst_394_, v_toBind_395_, v___f_396_, v_____r_397_, v___y_398_);
lean_dec(v___y_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(lean_object* v_x_400_){
_start:
{
lean_object* v_fst_401_; 
v_fst_401_ = lean_ctor_get(v_x_400_, 0);
lean_inc(v_fst_401_);
return v_fst_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(lean_object* v_x_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_402_);
lean_dec_ref(v_x_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(lean_object* v_x_404_){
_start:
{
lean_object* v_snd_405_; 
v_snd_405_ = lean_ctor_get(v_x_404_, 1);
lean_inc(v_snd_405_);
return v_snd_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_406_);
lean_dec_ref(v_x_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(lean_object* v_a_408_, lean_object* v_toPure_409_, lean_object* v_s_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_a_408_);
lean_ctor_set(v___x_411_, 1, v_s_410_);
v___x_412_ = lean_apply_2(v_toPure_409_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(lean_object* v_toPure_413_, lean_object* v_ref_414_, lean_object* v_inst_415_, lean_object* v_toBind_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4), 3, 2);
lean_closure_set(v___f_418_, 0, v_a_417_);
lean_closure_set(v___f_418_, 1, v_toPure_413_);
v___x_419_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_419_, 0, lean_box(0));
lean_closure_set(v___x_419_, 1, lean_box(0));
lean_closure_set(v___x_419_, 2, v_ref_414_);
v___x_420_ = lean_apply_2(v_inst_415_, lean_box(0), v___x_419_);
v___x_421_ = lean_apply_4(v_toBind_416_, lean_box(0), lean_box(0), v___x_420_, v___f_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(lean_object* v___f_422_, lean_object* v_ref_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = lean_apply_2(v___f_422_, v_a_424_, v_ref_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(lean_object* v___f_426_, lean_object* v_ref_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_2(v___f_426_, v___x_429_, v_ref_427_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0));
v___x_439_ = l_Lean_Name_mkStr4(v___x_432_, v___x_433_, v___x_434_, v___x_438_);
lean_inc(v_x_437_);
v___x_440_ = l_Lean_Syntax_isOfKind(v_x_437_, v___x_439_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_dec(v_x_437_);
v___x_441_ = lean_box(0);
return v___x_441_;
}
else
{
lean_object* v_froms_442_; lean_object* v_tos_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_froms_442_ = l_Lean_Syntax_getArg(v_x_437_, v___x_435_);
v_tos_443_ = l_Lean_Syntax_getArg(v_x_437_, v___x_436_);
lean_dec(v_x_437_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_froms_442_);
lean_ctor_set(v___x_444_, 1, v_tos_443_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(v___x_446_, v___x_447_, v___x_448_, v___x_449_, v___x_450_, v_x_451_);
lean_dec(v___x_450_);
lean_dec(v___x_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(lean_object* v___x_453_, lean_object* v_toPure_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_453_);
v___x_457_ = lean_apply_2(v_toPure_454_, lean_box(0), v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(lean_object* v_snd_458_, lean_object* v_a_459_, lean_object* v_inst_460_, lean_object* v_toBind_461_, lean_object* v___f_462_, lean_object* v_____r_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_465_ = l_Lean_Syntax_getId(v_snd_458_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_a_459_);
v___x_467_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_460_, v___x_466_, v___y_464_);
v___x_468_ = lean_apply_4(v_toBind_461_, lean_box(0), lean_box(0), v___x_467_, v___f_462_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(lean_object* v_snd_469_, lean_object* v_a_470_, lean_object* v_inst_471_, lean_object* v_toBind_472_, lean_object* v___f_473_, lean_object* v_____r_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(v_snd_469_, v_a_470_, v_inst_471_, v_toBind_472_, v___f_473_, v_____r_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec(v_snd_469_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object* v___f_477_, lean_object* v___y_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; 
lean_inc(v___y_478_);
v___x_480_ = lean_apply_2(v___f_477_, v_a_479_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(lean_object* v___f_481_, lean_object* v___y_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v___f_481_, v___y_482_, v_a_483_);
lean_dec(v___y_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v_snd_489_, lean_object* v_a_490_, lean_object* v___x_491_, lean_object* v___y_492_, lean_object* v_toBind_493_, lean_object* v___f_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_3613__overap_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_3613__overap_496_ = l_Lean_Elab_addConstInfo___redArg(v___x_485_, v___x_486_, v___x_487_, v___x_488_, v_snd_489_, v_a_490_, v___x_491_);
lean_inc(v___y_492_);
v___x_497_ = lean_apply_1(v___x_3613__overap_496_, v___y_492_);
v___x_498_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v___x_497_, v___f_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(lean_object* v___x_499_, lean_object* v___x_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v_snd_503_, lean_object* v_a_504_, lean_object* v___x_505_, lean_object* v___y_506_, lean_object* v_toBind_507_, lean_object* v___f_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(v___x_499_, v___x_500_, v___x_501_, v___x_502_, v_snd_503_, v_a_504_, v___x_505_, v___y_506_, v_toBind_507_, v___f_508_, v_a_509_);
lean_dec(v___y_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object* v___f_511_, lean_object* v___x_512_, lean_object* v___y_513_, lean_object* v___x_514_, lean_object* v___x_515_, lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v_snd_518_, lean_object* v_a_519_, lean_object* v_toBind_520_, lean_object* v___f_521_, lean_object* v_fst_522_, lean_object* v_a_523_){
_start:
{
uint8_t v_enabled_524_; 
v_enabled_524_ = lean_ctor_get_uint8(v_a_523_, sizeof(void*)*3);
if (v_enabled_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v_fst_522_);
lean_dec(v___f_521_);
lean_dec(v_toBind_520_);
lean_dec(v_a_519_);
lean_dec(v_snd_518_);
lean_dec_ref(v___x_517_);
lean_dec_ref(v___x_516_);
lean_dec_ref(v___x_515_);
lean_dec_ref(v___x_514_);
lean_inc(v___y_513_);
v___x_525_ = lean_apply_2(v___f_511_, v___x_512_, v___y_513_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_3628__overap_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___f_511_);
v___x_526_ = lean_box(0);
lean_inc(v_toBind_520_);
lean_inc_n(v___y_513_, 2);
lean_inc(v_a_519_);
lean_inc_ref(v___x_517_);
lean_inc_ref(v___x_516_);
lean_inc_ref(v___x_515_);
lean_inc_ref(v___x_514_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_527_, 0, v___x_514_);
lean_closure_set(v___f_527_, 1, v___x_515_);
lean_closure_set(v___f_527_, 2, v___x_516_);
lean_closure_set(v___f_527_, 3, v___x_517_);
lean_closure_set(v___f_527_, 4, v_snd_518_);
lean_closure_set(v___f_527_, 5, v_a_519_);
lean_closure_set(v___f_527_, 6, v___x_526_);
lean_closure_set(v___f_527_, 7, v___y_513_);
lean_closure_set(v___f_527_, 8, v_toBind_520_);
lean_closure_set(v___f_527_, 9, v___f_521_);
v___x_3628__overap_528_ = l_Lean_Elab_addConstInfo___redArg(v___x_514_, v___x_515_, v___x_516_, v___x_517_, v_fst_522_, v_a_519_, v___x_526_);
v___x_529_ = lean_apply_1(v___x_3628__overap_528_, v___y_513_);
v___x_530_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_529_, v___f_527_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object* v___f_531_, lean_object* v___x_532_, lean_object* v___y_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v_snd_538_, lean_object* v_a_539_, lean_object* v_toBind_540_, lean_object* v___f_541_, lean_object* v_fst_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(v___f_531_, v___x_532_, v___y_533_, v___x_534_, v___x_535_, v___x_536_, v___x_537_, v_snd_538_, v_a_539_, v_toBind_540_, v___f_541_, v_fst_542_, v_a_543_);
lean_dec_ref(v_a_543_);
lean_dec(v___y_533_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object* v_inst_545_, lean_object* v_snd_546_, lean_object* v_inst_547_, lean_object* v_toBind_548_, lean_object* v___f_549_, lean_object* v___y_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v_fst_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_getInfoState_558_; lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v_getInfoState_558_ = lean_ctor_get(v_inst_545_, 0);
lean_inc(v_getInfoState_558_);
lean_dec_ref(v_inst_545_);
lean_inc_n(v_toBind_548_, 2);
lean_inc(v_a_557_);
lean_inc(v_snd_546_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_559_, 0, v_snd_546_);
lean_closure_set(v___f_559_, 1, v_a_557_);
lean_closure_set(v___f_559_, 2, v_inst_547_);
lean_closure_set(v___f_559_, 3, v_toBind_548_);
lean_closure_set(v___f_559_, 4, v___f_549_);
lean_inc_n(v___y_550_, 2);
lean_inc_ref(v___f_559_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_560_, 0, v___f_559_);
lean_closure_set(v___f_560_, 1, v___y_550_);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_561_, 0, v___f_559_);
lean_closure_set(v___f_561_, 1, v___x_551_);
lean_closure_set(v___f_561_, 2, v___y_550_);
lean_closure_set(v___f_561_, 3, v___x_552_);
lean_closure_set(v___f_561_, 4, v___x_553_);
lean_closure_set(v___f_561_, 5, v___x_554_);
lean_closure_set(v___f_561_, 6, v___x_555_);
lean_closure_set(v___f_561_, 7, v_snd_546_);
lean_closure_set(v___f_561_, 8, v_a_557_);
lean_closure_set(v___f_561_, 9, v_toBind_548_);
lean_closure_set(v___f_561_, 10, v___f_560_);
lean_closure_set(v___f_561_, 11, v_fst_556_);
v___x_562_ = lean_apply_4(v_toBind_548_, lean_box(0), lean_box(0), v_getInfoState_558_, v___f_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(lean_object* v_inst_563_, lean_object* v_snd_564_, lean_object* v_inst_565_, lean_object* v_toBind_566_, lean_object* v___f_567_, lean_object* v___y_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v_fst_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(v_inst_563_, v_snd_564_, v_inst_565_, v_toBind_566_, v___f_567_, v___y_568_, v___x_569_, v___x_570_, v___x_571_, v___x_572_, v___x_573_, v_fst_574_, v_a_575_);
lean_dec(v___y_568_);
return v_res_576_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___f_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___f_600_; lean_object* v___x_3666__overap_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_fst_598_ = lean_ctor_get(v_a_594_, 0);
lean_inc_n(v_fst_598_, 2);
v_snd_599_ = lean_ctor_get(v_a_594_, 1);
lean_inc(v_snd_599_);
lean_dec_ref(v_a_594_);
lean_inc_ref(v___x_584_);
lean_inc_ref(v___x_582_);
lean_inc_n(v___y_597_, 2);
lean_inc(v_toBind_579_);
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_600_, 0, v_inst_577_);
lean_closure_set(v___f_600_, 1, v_snd_599_);
lean_closure_set(v___f_600_, 2, v_inst_578_);
lean_closure_set(v___f_600_, 3, v_toBind_579_);
lean_closure_set(v___f_600_, 4, v___f_580_);
lean_closure_set(v___f_600_, 5, v___y_597_);
lean_closure_set(v___f_600_, 6, v___x_581_);
lean_closure_set(v___f_600_, 7, v___x_582_);
lean_closure_set(v___f_600_, 8, v___x_583_);
lean_closure_set(v___f_600_, 9, v___x_584_);
lean_closure_set(v___f_600_, 10, v___x_585_);
lean_closure_set(v___f_600_, 11, v_fst_598_);
v___x_3666__overap_601_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_582_, v___x_584_, v___x_586_, v___x_587_, v___x_588_, v___f_589_, v___x_590_, v___x_591_, v___x_592_, v_a_593_, v_fst_598_);
v___x_602_ = lean_apply_1(v___x_3666__overap_601_, v___y_597_);
v___x_603_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_602_, v___f_600_);
return v___x_603_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_577_ = stack[0].m_obj;
lean_object* v_inst_578_ = stack[1].m_obj;
lean_object* v_toBind_579_ = stack[2].m_obj;
lean_object* v___f_580_ = stack[3].m_obj;
lean_object* v___x_581_ = stack[4].m_obj;
lean_object* v___x_582_ = stack[5].m_obj;
lean_object* v___x_583_ = stack[6].m_obj;
lean_object* v___x_584_ = stack[7].m_obj;
lean_object* v___x_585_ = stack[8].m_obj;
lean_object* v___x_586_ = stack[9].m_obj;
lean_object* v___x_587_ = stack[10].m_obj;
lean_object* v___x_588_ = stack[11].m_obj;
lean_object* v___f_589_ = stack[12].m_obj;
lean_object* v___x_590_ = stack[13].m_obj;
lean_object* v___x_591_ = stack[14].m_obj;
lean_object* v___x_592_ = stack[15].m_obj;
lean_object* v_a_593_ = stack[16].m_obj;
lean_object* v_a_594_ = stack[17].m_obj;
lean_object* v___y_596_ = stack[19].m_obj;
lean_object* v___y_597_ = stack[20].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v_inst_577_, v_inst_578_, v_toBind_579_, v___f_580_, v___x_581_, v___x_582_, v___x_583_, v___x_584_, v___x_585_, v___x_586_, v___x_587_, v___x_588_, v___f_589_, v___x_590_, v___x_591_, v___x_592_, v_a_593_, v_a_594_, lean_box(0), v___y_596_, v___y_597_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_inst_605_ = _args[0];
lean_object* v_inst_606_ = _args[1];
lean_object* v_toBind_607_ = _args[2];
lean_object* v___f_608_ = _args[3];
lean_object* v___x_609_ = _args[4];
lean_object* v___x_610_ = _args[5];
lean_object* v___x_611_ = _args[6];
lean_object* v___x_612_ = _args[7];
lean_object* v___x_613_ = _args[8];
lean_object* v___x_614_ = _args[9];
lean_object* v___x_615_ = _args[10];
lean_object* v___x_616_ = _args[11];
lean_object* v___f_617_ = _args[12];
lean_object* v___x_618_ = _args[13];
lean_object* v___x_619_ = _args[14];
lean_object* v___x_620_ = _args[15];
lean_object* v_a_621_ = _args[16];
lean_object* v_a_622_ = _args[17];
lean_object* v_x_623_ = _args[18];
lean_object* v___y_624_ = _args[19];
lean_object* v___y_625_ = _args[20];
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v_inst_605_, v_inst_606_, v_toBind_607_, v___f_608_, v___x_609_, v___x_610_, v___x_611_, v___x_612_, v___x_613_, v___x_614_, v___x_615_, v___x_616_, v___f_617_, v___x_618_, v___x_619_, v___x_620_, v_a_621_, v_a_622_, v_x_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
return v_res_626_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_froms_627_, lean_object* v_tos_628_, lean_object* v_toPure_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_toBind_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v___f_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v_a_644_, size_t v___x_645_, lean_object* v_ref_646_, lean_object* v___f_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___f_652_; size_t v_sz_653_; lean_object* v___x_3687__overap_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_649_ = l_Array_zip___redArg(v_froms_627_, v_tos_628_);
v___x_650_ = lean_box(0);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_651_, 0, v___x_650_);
lean_closure_set(v___f_651_, 1, v_toPure_629_);
lean_inc_ref(v___x_633_);
lean_inc(v_toBind_632_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 21, 17);
lean_closure_set(v___f_652_, 0, v_inst_630_);
lean_closure_set(v___f_652_, 1, v_inst_631_);
lean_closure_set(v___f_652_, 2, v_toBind_632_);
lean_closure_set(v___f_652_, 3, v___f_651_);
lean_closure_set(v___f_652_, 4, v___x_650_);
lean_closure_set(v___f_652_, 5, v___x_633_);
lean_closure_set(v___f_652_, 6, v___x_634_);
lean_closure_set(v___f_652_, 7, v___x_635_);
lean_closure_set(v___f_652_, 8, v___x_636_);
lean_closure_set(v___f_652_, 9, v___x_637_);
lean_closure_set(v___f_652_, 10, v___x_638_);
lean_closure_set(v___f_652_, 11, v___x_639_);
lean_closure_set(v___f_652_, 12, v___f_640_);
lean_closure_set(v___f_652_, 13, v___x_641_);
lean_closure_set(v___f_652_, 14, v___x_642_);
lean_closure_set(v___f_652_, 15, v___x_643_);
lean_closure_set(v___f_652_, 16, v_a_644_);
v_sz_653_ = lean_array_size(v___x_649_);
v___x_3687__overap_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_633_, v___x_649_, v___f_652_, v_sz_653_, v___x_645_, v___x_650_);
v___x_655_ = lean_apply_1(v___x_3687__overap_654_, v_ref_646_);
v___x_656_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_655_, v___f_647_);
return v___x_656_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_froms_627_ = stack[0].m_obj;
lean_object* v_tos_628_ = stack[1].m_obj;
lean_object* v_toPure_629_ = stack[2].m_obj;
lean_object* v_inst_630_ = stack[3].m_obj;
lean_object* v_inst_631_ = stack[4].m_obj;
lean_object* v_toBind_632_ = stack[5].m_obj;
lean_object* v___x_633_ = stack[6].m_obj;
lean_object* v___x_634_ = stack[7].m_obj;
lean_object* v___x_635_ = stack[8].m_obj;
lean_object* v___x_636_ = stack[9].m_obj;
lean_object* v___x_637_ = stack[10].m_obj;
lean_object* v___x_638_ = stack[11].m_obj;
lean_object* v___x_639_ = stack[12].m_obj;
lean_object* v___f_640_ = stack[13].m_obj;
lean_object* v___x_641_ = stack[14].m_obj;
lean_object* v___x_642_ = stack[15].m_obj;
lean_object* v___x_643_ = stack[16].m_obj;
lean_object* v_a_644_ = stack[17].m_obj;
size_t v___x_645_ = stack[18].m_num;
lean_object* v_ref_646_ = stack[19].m_obj;
lean_object* v___f_647_ = stack[20].m_obj;
lean_object* v_a_648_ = stack[21].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_627_, v_tos_628_, v_toPure_629_, v_inst_630_, v_inst_631_, v_toBind_632_, v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_638_, v___x_639_, v___f_640_, v___x_641_, v___x_642_, v___x_643_, v_a_644_, v___x_645_, v_ref_646_, v___f_647_, v_a_648_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_froms_658_ = _args[0];
lean_object* v_tos_659_ = _args[1];
lean_object* v_toPure_660_ = _args[2];
lean_object* v_inst_661_ = _args[3];
lean_object* v_inst_662_ = _args[4];
lean_object* v_toBind_663_ = _args[5];
lean_object* v___x_664_ = _args[6];
lean_object* v___x_665_ = _args[7];
lean_object* v___x_666_ = _args[8];
lean_object* v___x_667_ = _args[9];
lean_object* v___x_668_ = _args[10];
lean_object* v___x_669_ = _args[11];
lean_object* v___x_670_ = _args[12];
lean_object* v___f_671_ = _args[13];
lean_object* v___x_672_ = _args[14];
lean_object* v___x_673_ = _args[15];
lean_object* v___x_674_ = _args[16];
lean_object* v_a_675_ = _args[17];
lean_object* v___x_676_ = _args[18];
lean_object* v_ref_677_ = _args[19];
lean_object* v___f_678_ = _args[20];
lean_object* v_a_679_ = _args[21];
_start:
{
size_t v___x_4734__boxed_680_; lean_object* v_res_681_; 
v___x_4734__boxed_680_ = lean_unbox_usize(v___x_676_);
lean_dec(v___x_676_);
v_res_681_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_658_, v_tos_659_, v_toPure_660_, v_inst_661_, v_inst_662_, v_toBind_663_, v___x_664_, v___x_665_, v___x_666_, v___x_667_, v___x_668_, v___x_669_, v___x_670_, v___f_671_, v___x_672_, v___x_673_, v___x_674_, v_a_675_, v___x_4734__boxed_680_, v_ref_677_, v___f_678_, v_a_679_);
lean_dec_ref(v_tos_659_);
lean_dec_ref(v_froms_658_);
return v_res_681_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object* v_froms_682_, lean_object* v_tos_683_, lean_object* v_toPure_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_toBind_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v___f_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v___x_698_, size_t v___x_699_, lean_object* v_ref_700_, lean_object* v___f_701_, lean_object* v___x_702_, lean_object* v_nsStx_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_3707__overap_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_705_ = lean_box_usize(v___x_699_);
lean_inc(v_ref_700_);
lean_inc(v_a_704_);
lean_inc_ref(v___x_698_);
lean_inc_ref(v___x_697_);
lean_inc_ref(v___x_696_);
lean_inc(v___f_695_);
lean_inc_ref(v___x_690_);
lean_inc_ref(v___x_688_);
lean_inc(v_toBind_687_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 22, 21);
lean_closure_set(v___f_706_, 0, v_froms_682_);
lean_closure_set(v___f_706_, 1, v_tos_683_);
lean_closure_set(v___f_706_, 2, v_toPure_684_);
lean_closure_set(v___f_706_, 3, v_inst_685_);
lean_closure_set(v___f_706_, 4, v_inst_686_);
lean_closure_set(v___f_706_, 5, v_toBind_687_);
lean_closure_set(v___f_706_, 6, v___x_688_);
lean_closure_set(v___f_706_, 7, v___x_689_);
lean_closure_set(v___f_706_, 8, v___x_690_);
lean_closure_set(v___f_706_, 9, v___x_691_);
lean_closure_set(v___f_706_, 10, v___x_692_);
lean_closure_set(v___f_706_, 11, v___x_693_);
lean_closure_set(v___f_706_, 12, v___x_694_);
lean_closure_set(v___f_706_, 13, v___f_695_);
lean_closure_set(v___f_706_, 14, v___x_696_);
lean_closure_set(v___f_706_, 15, v___x_697_);
lean_closure_set(v___f_706_, 16, v___x_698_);
lean_closure_set(v___f_706_, 17, v_a_704_);
lean_closure_set(v___f_706_, 18, v___x_705_);
lean_closure_set(v___f_706_, 19, v_ref_700_);
lean_closure_set(v___f_706_, 20, v___f_701_);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v_a_704_);
lean_ctor_set(v___x_707_, 1, v___x_702_);
v___x_3707__overap_708_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_688_, v___x_690_, v___x_697_, v___x_696_, v___f_695_, v___x_698_, v_nsStx_703_, v___x_707_);
v___x_709_ = lean_apply_1(v___x_3707__overap_708_, v_ref_700_);
v___x_710_ = lean_apply_4(v_toBind_687_, lean_box(0), lean_box(0), v___x_709_, v___f_706_);
return v___x_710_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_froms_682_ = stack[0].m_obj;
lean_object* v_tos_683_ = stack[1].m_obj;
lean_object* v_toPure_684_ = stack[2].m_obj;
lean_object* v_inst_685_ = stack[3].m_obj;
lean_object* v_inst_686_ = stack[4].m_obj;
lean_object* v_toBind_687_ = stack[5].m_obj;
lean_object* v___x_688_ = stack[6].m_obj;
lean_object* v___x_689_ = stack[7].m_obj;
lean_object* v___x_690_ = stack[8].m_obj;
lean_object* v___x_691_ = stack[9].m_obj;
lean_object* v___x_692_ = stack[10].m_obj;
lean_object* v___x_693_ = stack[11].m_obj;
lean_object* v___x_694_ = stack[12].m_obj;
lean_object* v___f_695_ = stack[13].m_obj;
lean_object* v___x_696_ = stack[14].m_obj;
lean_object* v___x_697_ = stack[15].m_obj;
lean_object* v___x_698_ = stack[16].m_obj;
size_t v___x_699_ = stack[17].m_num;
lean_object* v_ref_700_ = stack[18].m_obj;
lean_object* v___f_701_ = stack[19].m_obj;
lean_object* v___x_702_ = stack[20].m_obj;
lean_object* v_nsStx_703_ = stack[21].m_obj;
lean_object* v_a_704_ = stack[22].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v_froms_682_, v_tos_683_, v_toPure_684_, v_inst_685_, v_inst_686_, v_toBind_687_, v___x_688_, v___x_689_, v___x_690_, v___x_691_, v___x_692_, v___x_693_, v___x_694_, v___f_695_, v___x_696_, v___x_697_, v___x_698_, v___x_699_, v_ref_700_, v___f_701_, v___x_702_, v_nsStx_703_, v_a_704_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_froms_712_ = _args[0];
lean_object* v_tos_713_ = _args[1];
lean_object* v_toPure_714_ = _args[2];
lean_object* v_inst_715_ = _args[3];
lean_object* v_inst_716_ = _args[4];
lean_object* v_toBind_717_ = _args[5];
lean_object* v___x_718_ = _args[6];
lean_object* v___x_719_ = _args[7];
lean_object* v___x_720_ = _args[8];
lean_object* v___x_721_ = _args[9];
lean_object* v___x_722_ = _args[10];
lean_object* v___x_723_ = _args[11];
lean_object* v___x_724_ = _args[12];
lean_object* v___f_725_ = _args[13];
lean_object* v___x_726_ = _args[14];
lean_object* v___x_727_ = _args[15];
lean_object* v___x_728_ = _args[16];
lean_object* v___x_729_ = _args[17];
lean_object* v_ref_730_ = _args[18];
lean_object* v___f_731_ = _args[19];
lean_object* v___x_732_ = _args[20];
lean_object* v_nsStx_733_ = _args[21];
lean_object* v_a_734_ = _args[22];
_start:
{
size_t v___x_4827__boxed_735_; lean_object* v_res_736_; 
v___x_4827__boxed_735_ = lean_unbox_usize(v___x_729_);
lean_dec(v___x_729_);
v_res_736_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v_froms_712_, v_tos_713_, v_toPure_714_, v_inst_715_, v_inst_716_, v_toBind_717_, v___x_718_, v___x_719_, v___x_720_, v___x_721_, v___x_722_, v___x_723_, v___x_724_, v___f_725_, v___x_726_, v___x_727_, v___x_728_, v___x_4827__boxed_735_, v_ref_730_, v___f_731_, v___x_732_, v_nsStx_733_, v_a_734_);
return v_res_736_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(uint8_t v___x_737_, uint8_t v___x_738_, lean_object* v_x1_739_, lean_object* v_x2_740_){
_start:
{
lean_object* v_fst_741_; uint8_t v___x_742_; 
v_fst_741_ = lean_ctor_get(v_x1_739_, 0);
v___x_742_ = lean_unbox(v_fst_741_);
if (v___x_742_ == 0)
{
lean_object* v_snd_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_x2_740_);
v_snd_743_ = lean_ctor_get(v_x1_739_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x1_739_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v_x1_739_, 0);
lean_dec(v_unused_752_);
v___x_745_ = v_x1_739_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_snd_743_);
lean_dec(v_x1_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_box(v___x_737_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_743_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_snd_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_762_; 
v_snd_753_ = lean_ctor_get(v_x1_739_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x1_739_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_x1_739_, 0);
lean_dec(v_unused_763_);
v___x_755_ = v_x1_739_;
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snd_753_);
lean_dec(v_x1_739_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_757_ = lean_array_push(v_snd_753_, v_x2_740_);
v___x_758_ = lean_box(v___x_738_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v___x_757_);
lean_ctor_set(v___x_755_, 0, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v___x_757_);
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
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_737_ = stack[0].m_num;
uint8_t v___x_738_ = stack[1].m_num;
lean_object* v_x1_739_ = stack[2].m_obj;
lean_object* v_x2_740_ = stack[3].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v___x_737_, v___x_738_, v_x1_739_, v_x2_740_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v_x1_767_, lean_object* v_x2_768_){
_start:
{
uint8_t v___x_4909__boxed_769_; uint8_t v___x_4910__boxed_770_; lean_object* v_res_771_; 
v___x_4909__boxed_769_ = lean_unbox(v___x_765_);
v___x_4910__boxed_770_ = lean_unbox(v___x_766_);
v_res_771_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v___x_4909__boxed_769_, v___x_4910__boxed_770_, v_x1_767_, v_x2_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v_ids_772_, lean_object* v___f_773_, lean_object* v_a_774_, lean_object* v_inst_775_, lean_object* v_ref_776_, lean_object* v_toBind_777_, lean_object* v___f_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_780_; size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_780_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_781_ = lean_array_size(v_ids_772_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_780_, v___f_773_, v_sz_781_, v___x_782_, v_ids_772_);
v___x_784_ = lean_array_to_list(v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_a_774_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_775_, v___x_785_, v_ref_776_);
v___x_787_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_786_, v___f_778_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v_ids_788_, lean_object* v___f_789_, lean_object* v_a_790_, lean_object* v_inst_791_, lean_object* v_ref_792_, lean_object* v_toBind_793_, lean_object* v___f_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v_ids_788_, v___f_789_, v_a_790_, v_inst_791_, v_ref_792_, v_toBind_793_, v___f_794_, v_a_795_);
lean_dec(v_ref_792_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v___x_797_, lean_object* v_toPure_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v___x_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v___y_805_, lean_object* v_toBind_806_, lean_object* v___f_807_, lean_object* v_a_808_){
_start:
{
uint8_t v_enabled_809_; 
v_enabled_809_ = lean_ctor_get_uint8(v_a_808_, sizeof(void*)*3);
if (v_enabled_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___f_807_);
lean_dec(v_toBind_806_);
lean_dec(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v___x_802_);
lean_dec_ref(v___x_801_);
lean_dec_ref(v___x_800_);
lean_dec_ref(v___x_799_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_797_);
v___x_811_ = lean_apply_2(v_toPure_798_, lean_box(0), v___x_810_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_3752__overap_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_toPure_798_);
v___x_812_ = lean_box(0);
v___x_3752__overap_813_ = l_Lean_Elab_addConstInfo___redArg(v___x_799_, v___x_800_, v___x_801_, v___x_802_, v_a_803_, v_a_804_, v___x_812_);
lean_inc(v___y_805_);
v___x_814_ = lean_apply_1(v___x_3752__overap_813_, v___y_805_);
v___x_815_ = lean_apply_4(v_toBind_806_, lean_box(0), lean_box(0), v___x_814_, v___f_807_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object* v___x_816_, lean_object* v_toPure_817_, lean_object* v___x_818_, lean_object* v___x_819_, lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v_toBind_825_, lean_object* v___f_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v___x_816_, v_toPure_817_, v___x_818_, v___x_819_, v___x_820_, v___x_821_, v_a_822_, v_a_823_, v___y_824_, v_toBind_825_, v___f_826_, v_a_827_);
lean_dec_ref(v_a_827_);
lean_dec(v___y_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object* v_inst_829_, lean_object* v___x_830_, lean_object* v_toPure_831_, lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v_a_836_, lean_object* v___y_837_, lean_object* v_toBind_838_, lean_object* v___f_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_getInfoState_841_; lean_object* v___f_842_; lean_object* v___x_843_; 
v_getInfoState_841_ = lean_ctor_get(v_inst_829_, 0);
lean_inc(v_getInfoState_841_);
lean_dec_ref(v_inst_829_);
lean_inc(v_toBind_838_);
lean_inc(v___y_837_);
v___f_842_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 12, 11);
lean_closure_set(v___f_842_, 0, v___x_830_);
lean_closure_set(v___f_842_, 1, v_toPure_831_);
lean_closure_set(v___f_842_, 2, v___x_832_);
lean_closure_set(v___f_842_, 3, v___x_833_);
lean_closure_set(v___f_842_, 4, v___x_834_);
lean_closure_set(v___f_842_, 5, v___x_835_);
lean_closure_set(v___f_842_, 6, v_a_836_);
lean_closure_set(v___f_842_, 7, v_a_840_);
lean_closure_set(v___f_842_, 8, v___y_837_);
lean_closure_set(v___f_842_, 9, v_toBind_838_);
lean_closure_set(v___f_842_, 10, v___f_839_);
v___x_843_ = lean_apply_4(v_toBind_838_, lean_box(0), lean_box(0), v_getInfoState_841_, v___f_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object* v_inst_844_, lean_object* v___x_845_, lean_object* v_toPure_846_, lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v_toBind_853_, lean_object* v___f_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(v_inst_844_, v___x_845_, v_toPure_846_, v___x_847_, v___x_848_, v___x_849_, v___x_850_, v_a_851_, v___y_852_, v_toBind_853_, v___f_854_, v_a_855_);
lean_dec(v___y_852_);
return v_res_856_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v_inst_857_, lean_object* v___x_858_, lean_object* v_toPure_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v_toBind_864_, lean_object* v___f_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v___f_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v___f_878_; lean_object* v___x_3782__overap_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc(v_toBind_864_);
lean_inc_n(v___y_877_, 2);
lean_inc(v_a_874_);
lean_inc_ref(v___x_862_);
lean_inc_ref(v___x_860_);
v___f_878_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_878_, 0, v_inst_857_);
lean_closure_set(v___f_878_, 1, v___x_858_);
lean_closure_set(v___f_878_, 2, v_toPure_859_);
lean_closure_set(v___f_878_, 3, v___x_860_);
lean_closure_set(v___f_878_, 4, v___x_861_);
lean_closure_set(v___f_878_, 5, v___x_862_);
lean_closure_set(v___f_878_, 6, v___x_863_);
lean_closure_set(v___f_878_, 7, v_a_874_);
lean_closure_set(v___f_878_, 8, v___y_877_);
lean_closure_set(v___f_878_, 9, v_toBind_864_);
lean_closure_set(v___f_878_, 10, v___f_865_);
v___x_3782__overap_879_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_860_, v___x_862_, v___x_866_, v___x_867_, v___x_868_, v___f_869_, v___x_870_, v___x_871_, v___x_872_, v_a_873_, v_a_874_);
v___x_880_ = lean_apply_1(v___x_3782__overap_879_, v___y_877_);
v___x_881_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v___x_880_, v___f_878_);
return v___x_881_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_857_ = stack[0].m_obj;
lean_object* v___x_858_ = stack[1].m_obj;
lean_object* v_toPure_859_ = stack[2].m_obj;
lean_object* v___x_860_ = stack[3].m_obj;
lean_object* v___x_861_ = stack[4].m_obj;
lean_object* v___x_862_ = stack[5].m_obj;
lean_object* v___x_863_ = stack[6].m_obj;
lean_object* v_toBind_864_ = stack[7].m_obj;
lean_object* v___f_865_ = stack[8].m_obj;
lean_object* v___x_866_ = stack[9].m_obj;
lean_object* v___x_867_ = stack[10].m_obj;
lean_object* v___x_868_ = stack[11].m_obj;
lean_object* v___f_869_ = stack[12].m_obj;
lean_object* v___x_870_ = stack[13].m_obj;
lean_object* v___x_871_ = stack[14].m_obj;
lean_object* v___x_872_ = stack[15].m_obj;
lean_object* v_a_873_ = stack[16].m_obj;
lean_object* v_a_874_ = stack[17].m_obj;
lean_object* v___y_876_ = stack[19].m_obj;
lean_object* v___y_877_ = stack[20].m_obj;
lean_object* v_res_882_;
v_res_882_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v_inst_857_, v___x_858_, v_toPure_859_, v___x_860_, v___x_861_, v___x_862_, v___x_863_, v_toBind_864_, v___f_865_, v___x_866_, v___x_867_, v___x_868_, v___f_869_, v___x_870_, v___x_871_, v___x_872_, v_a_873_, v_a_874_, lean_box(0), v___y_876_, v___y_877_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_inst_883_ = _args[0];
lean_object* v___x_884_ = _args[1];
lean_object* v_toPure_885_ = _args[2];
lean_object* v___x_886_ = _args[3];
lean_object* v___x_887_ = _args[4];
lean_object* v___x_888_ = _args[5];
lean_object* v___x_889_ = _args[6];
lean_object* v_toBind_890_ = _args[7];
lean_object* v___f_891_ = _args[8];
lean_object* v___x_892_ = _args[9];
lean_object* v___x_893_ = _args[10];
lean_object* v___x_894_ = _args[11];
lean_object* v___f_895_ = _args[12];
lean_object* v___x_896_ = _args[13];
lean_object* v___x_897_ = _args[14];
lean_object* v___x_898_ = _args[15];
lean_object* v_a_899_ = _args[16];
lean_object* v_a_900_ = _args[17];
lean_object* v_x_901_ = _args[18];
lean_object* v___y_902_ = _args[19];
lean_object* v___y_903_ = _args[20];
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v_inst_883_, v___x_884_, v_toPure_885_, v___x_886_, v___x_887_, v___x_888_, v___x_889_, v_toBind_890_, v___f_891_, v___x_892_, v___x_893_, v___x_894_, v___f_895_, v___x_896_, v___x_897_, v___x_898_, v_a_899_, v_a_900_, v_x_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
return v_res_904_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_toPure_905_, lean_object* v_inst_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v___x_910_, lean_object* v_toBind_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v___f_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v_a_919_, lean_object* v_ids_920_, lean_object* v_ref_921_, lean_object* v___f_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___f_926_; size_t v_sz_927_; size_t v___x_928_; lean_object* v___x_3801__overap_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_924_ = lean_box(0);
lean_inc(v_toPure_905_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_925_, 0, v___x_924_);
lean_closure_set(v___f_925_, 1, v_toPure_905_);
lean_inc(v_toBind_911_);
lean_inc_ref(v___x_907_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 21, 17);
lean_closure_set(v___f_926_, 0, v_inst_906_);
lean_closure_set(v___f_926_, 1, v___x_924_);
lean_closure_set(v___f_926_, 2, v_toPure_905_);
lean_closure_set(v___f_926_, 3, v___x_907_);
lean_closure_set(v___f_926_, 4, v___x_908_);
lean_closure_set(v___f_926_, 5, v___x_909_);
lean_closure_set(v___f_926_, 6, v___x_910_);
lean_closure_set(v___f_926_, 7, v_toBind_911_);
lean_closure_set(v___f_926_, 8, v___f_925_);
lean_closure_set(v___f_926_, 9, v___x_912_);
lean_closure_set(v___f_926_, 10, v___x_913_);
lean_closure_set(v___f_926_, 11, v___x_914_);
lean_closure_set(v___f_926_, 12, v___f_915_);
lean_closure_set(v___f_926_, 13, v___x_916_);
lean_closure_set(v___f_926_, 14, v___x_917_);
lean_closure_set(v___f_926_, 15, v___x_918_);
lean_closure_set(v___f_926_, 16, v_a_919_);
v_sz_927_ = lean_array_size(v_ids_920_);
v___x_928_ = ((size_t)0ULL);
v___x_3801__overap_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_907_, v_ids_920_, v___f_926_, v_sz_927_, v___x_928_, v___x_924_);
v___x_930_ = lean_apply_1(v___x_3801__overap_929_, v_ref_921_);
v___x_931_ = lean_apply_4(v_toBind_911_, lean_box(0), lean_box(0), v___x_930_, v___f_922_);
return v___x_931_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_905_ = stack[0].m_obj;
lean_object* v_inst_906_ = stack[1].m_obj;
lean_object* v___x_907_ = stack[2].m_obj;
lean_object* v___x_908_ = stack[3].m_obj;
lean_object* v___x_909_ = stack[4].m_obj;
lean_object* v___x_910_ = stack[5].m_obj;
lean_object* v_toBind_911_ = stack[6].m_obj;
lean_object* v___x_912_ = stack[7].m_obj;
lean_object* v___x_913_ = stack[8].m_obj;
lean_object* v___x_914_ = stack[9].m_obj;
lean_object* v___f_915_ = stack[10].m_obj;
lean_object* v___x_916_ = stack[11].m_obj;
lean_object* v___x_917_ = stack[12].m_obj;
lean_object* v___x_918_ = stack[13].m_obj;
lean_object* v_a_919_ = stack[14].m_obj;
lean_object* v_ids_920_ = stack[15].m_obj;
lean_object* v_ref_921_ = stack[16].m_obj;
lean_object* v___f_922_ = stack[17].m_obj;
lean_object* v_a_923_ = stack[18].m_obj;
lean_object* v_res_932_;
v_res_932_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_toPure_905_, v_inst_906_, v___x_907_, v___x_908_, v___x_909_, v___x_910_, v_toBind_911_, v___x_912_, v___x_913_, v___x_914_, v___f_915_, v___x_916_, v___x_917_, v___x_918_, v_a_919_, v_ids_920_, v_ref_921_, v___f_922_, v_a_923_);
stack->m_obj
 = v_res_932_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_toPure_933_ = _args[0];
lean_object* v_inst_934_ = _args[1];
lean_object* v___x_935_ = _args[2];
lean_object* v___x_936_ = _args[3];
lean_object* v___x_937_ = _args[4];
lean_object* v___x_938_ = _args[5];
lean_object* v_toBind_939_ = _args[6];
lean_object* v___x_940_ = _args[7];
lean_object* v___x_941_ = _args[8];
lean_object* v___x_942_ = _args[9];
lean_object* v___f_943_ = _args[10];
lean_object* v___x_944_ = _args[11];
lean_object* v___x_945_ = _args[12];
lean_object* v___x_946_ = _args[13];
lean_object* v_a_947_ = _args[14];
lean_object* v_ids_948_ = _args[15];
lean_object* v_ref_949_ = _args[16];
lean_object* v___f_950_ = _args[17];
lean_object* v_a_951_ = _args[18];
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_toPure_933_, v_inst_934_, v___x_935_, v___x_936_, v___x_937_, v___x_938_, v_toBind_939_, v___x_940_, v___x_941_, v___x_942_, v___f_943_, v___x_944_, v___x_945_, v___x_946_, v_a_947_, v_ids_948_, v_ref_949_, v___f_950_, v_a_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v___x_953_, lean_object* v___x_954_, lean_object* v___f_955_, lean_object* v_a_956_, lean_object* v_ref_957_, lean_object* v_toBind_958_, lean_object* v___f_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_3807__overap_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_3807__overap_961_ = l_Lean_activateScoped___redArg(v___x_953_, v___x_954_, v___f_955_, v_a_956_);
v___x_962_ = lean_apply_1(v___x_3807__overap_961_, v_ref_957_);
v___x_963_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v___x_962_, v___f_959_);
return v___x_963_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v_ids_964_, lean_object* v___f_965_, lean_object* v_inst_966_, lean_object* v_ref_967_, lean_object* v_toBind_968_, lean_object* v___f_969_, lean_object* v_toPure_970_, lean_object* v_inst_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v___f_979_, lean_object* v___x_980_, lean_object* v___x_981_, lean_object* v___x_982_, lean_object* v___f_983_, lean_object* v___x_984_, lean_object* v_nsStx_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___x_3830__overap_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc_n(v_toBind_968_, 3);
lean_inc_n(v_ref_967_, 3);
lean_inc_n(v_a_986_, 3);
lean_inc_ref(v_ids_964_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 8, 7);
lean_closure_set(v___f_987_, 0, v_ids_964_);
lean_closure_set(v___f_987_, 1, v___f_965_);
lean_closure_set(v___f_987_, 2, v_a_986_);
lean_closure_set(v___f_987_, 3, v_inst_966_);
lean_closure_set(v___f_987_, 4, v_ref_967_);
lean_closure_set(v___f_987_, 5, v_toBind_968_);
lean_closure_set(v___f_987_, 6, v___f_969_);
lean_inc_ref(v___x_982_);
lean_inc_ref(v___x_981_);
lean_inc_ref(v___x_980_);
lean_inc(v___f_979_);
lean_inc_ref_n(v___x_974_, 2);
lean_inc_ref_n(v___x_972_, 2);
v___f_988_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 19, 18);
lean_closure_set(v___f_988_, 0, v_toPure_970_);
lean_closure_set(v___f_988_, 1, v_inst_971_);
lean_closure_set(v___f_988_, 2, v___x_972_);
lean_closure_set(v___f_988_, 3, v___x_973_);
lean_closure_set(v___f_988_, 4, v___x_974_);
lean_closure_set(v___f_988_, 5, v___x_975_);
lean_closure_set(v___f_988_, 6, v_toBind_968_);
lean_closure_set(v___f_988_, 7, v___x_976_);
lean_closure_set(v___f_988_, 8, v___x_977_);
lean_closure_set(v___f_988_, 9, v___x_978_);
lean_closure_set(v___f_988_, 10, v___f_979_);
lean_closure_set(v___f_988_, 11, v___x_980_);
lean_closure_set(v___f_988_, 12, v___x_981_);
lean_closure_set(v___f_988_, 13, v___x_982_);
lean_closure_set(v___f_988_, 14, v_a_986_);
lean_closure_set(v___f_988_, 15, v_ids_964_);
lean_closure_set(v___f_988_, 16, v_ref_967_);
lean_closure_set(v___f_988_, 17, v___f_987_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24), 8, 7);
lean_closure_set(v___f_989_, 0, v___x_972_);
lean_closure_set(v___f_989_, 1, v___x_974_);
lean_closure_set(v___f_989_, 2, v___f_983_);
lean_closure_set(v___f_989_, 3, v_a_986_);
lean_closure_set(v___f_989_, 4, v_ref_967_);
lean_closure_set(v___f_989_, 5, v_toBind_968_);
lean_closure_set(v___f_989_, 6, v___f_988_);
v___x_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_990_, 0, v_a_986_);
lean_ctor_set(v___x_990_, 1, v___x_984_);
v___x_3830__overap_991_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_972_, v___x_974_, v___x_981_, v___x_980_, v___f_979_, v___x_982_, v_nsStx_985_, v___x_990_);
v___x_992_ = lean_apply_1(v___x_3830__overap_991_, v_ref_967_);
v___x_993_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_992_, v___f_989_);
return v___x_993_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_ids_964_ = stack[0].m_obj;
lean_object* v___f_965_ = stack[1].m_obj;
lean_object* v_inst_966_ = stack[2].m_obj;
lean_object* v_ref_967_ = stack[3].m_obj;
lean_object* v_toBind_968_ = stack[4].m_obj;
lean_object* v___f_969_ = stack[5].m_obj;
lean_object* v_toPure_970_ = stack[6].m_obj;
lean_object* v_inst_971_ = stack[7].m_obj;
lean_object* v___x_972_ = stack[8].m_obj;
lean_object* v___x_973_ = stack[9].m_obj;
lean_object* v___x_974_ = stack[10].m_obj;
lean_object* v___x_975_ = stack[11].m_obj;
lean_object* v___x_976_ = stack[12].m_obj;
lean_object* v___x_977_ = stack[13].m_obj;
lean_object* v___x_978_ = stack[14].m_obj;
lean_object* v___f_979_ = stack[15].m_obj;
lean_object* v___x_980_ = stack[16].m_obj;
lean_object* v___x_981_ = stack[17].m_obj;
lean_object* v___x_982_ = stack[18].m_obj;
lean_object* v___f_983_ = stack[19].m_obj;
lean_object* v___x_984_ = stack[20].m_obj;
lean_object* v_nsStx_985_ = stack[21].m_obj;
lean_object* v_a_986_ = stack[22].m_obj;
lean_object* v_res_994_;
v_res_994_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v_ids_964_, v___f_965_, v_inst_966_, v_ref_967_, v_toBind_968_, v___f_969_, v_toPure_970_, v_inst_971_, v___x_972_, v___x_973_, v___x_974_, v___x_975_, v___x_976_, v___x_977_, v___x_978_, v___f_979_, v___x_980_, v___x_981_, v___x_982_, v___f_983_, v___x_984_, v_nsStx_985_, v_a_986_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object** _args){
lean_object* v_ids_995_ = _args[0];
lean_object* v___f_996_ = _args[1];
lean_object* v_inst_997_ = _args[2];
lean_object* v_ref_998_ = _args[3];
lean_object* v_toBind_999_ = _args[4];
lean_object* v___f_1000_ = _args[5];
lean_object* v_toPure_1001_ = _args[6];
lean_object* v_inst_1002_ = _args[7];
lean_object* v___x_1003_ = _args[8];
lean_object* v___x_1004_ = _args[9];
lean_object* v___x_1005_ = _args[10];
lean_object* v___x_1006_ = _args[11];
lean_object* v___x_1007_ = _args[12];
lean_object* v___x_1008_ = _args[13];
lean_object* v___x_1009_ = _args[14];
lean_object* v___f_1010_ = _args[15];
lean_object* v___x_1011_ = _args[16];
lean_object* v___x_1012_ = _args[17];
lean_object* v___x_1013_ = _args[18];
lean_object* v___f_1014_ = _args[19];
lean_object* v___x_1015_ = _args[20];
lean_object* v_nsStx_1016_ = _args[21];
lean_object* v_a_1017_ = _args[22];
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v_ids_995_, v___f_996_, v_inst_997_, v_ref_998_, v_toBind_999_, v___f_1000_, v_toPure_1001_, v_inst_1002_, v___x_1003_, v___x_1004_, v___x_1005_, v___x_1006_, v___x_1007_, v___x_1008_, v___x_1009_, v___f_1010_, v___x_1011_, v___x_1012_, v___x_1013_, v___f_1014_, v___x_1015_, v_nsStx_1016_, v_a_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_inst_1021_, lean_object* v_toBind_1022_, lean_object* v___f_1023_, lean_object* v_____r_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = l_Lean_TSyntax_getId(v_a_1019_);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_a_1020_);
v___x_1028_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1021_, v___x_1027_, v___y_1025_);
v___x_1029_ = lean_apply_4(v_toBind_1022_, lean_box(0), lean_box(0), v___x_1028_, v___f_1023_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_inst_1032_, lean_object* v_toBind_1033_, lean_object* v___f_1034_, lean_object* v_____r_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_a_1030_, v_a_1031_, v_inst_1032_, v_toBind_1033_, v___f_1034_, v_____r_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec(v_a_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v___f_1038_, lean_object* v___x_1039_, lean_object* v___y_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v___x_1043_, lean_object* v___x_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_toBind_1047_, lean_object* v___f_1048_, lean_object* v_a_1049_){
_start:
{
uint8_t v_enabled_1050_; 
v_enabled_1050_ = lean_ctor_get_uint8(v_a_1049_, sizeof(void*)*3);
if (v_enabled_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec(v___f_1048_);
lean_dec(v_toBind_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v___x_1043_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1041_);
lean_inc(v___y_1040_);
v___x_1051_ = lean_apply_2(v___f_1038_, v___x_1039_, v___y_1040_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_3859__overap_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v___f_1038_);
v___x_1052_ = lean_box(0);
v___x_3859__overap_1053_ = l_Lean_Elab_addConstInfo___redArg(v___x_1041_, v___x_1042_, v___x_1043_, v___x_1044_, v_a_1045_, v_a_1046_, v___x_1052_);
lean_inc(v___y_1040_);
v___x_1054_ = lean_apply_1(v___x_3859__overap_1053_, v___y_1040_);
v___x_1055_ = lean_apply_4(v_toBind_1047_, lean_box(0), lean_box(0), v___x_1054_, v___f_1048_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object* v___f_1056_, lean_object* v___x_1057_, lean_object* v___y_1058_, lean_object* v___x_1059_, lean_object* v___x_1060_, lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_toBind_1065_, lean_object* v___f_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v___f_1056_, v___x_1057_, v___y_1058_, v___x_1059_, v___x_1060_, v___x_1061_, v___x_1062_, v_a_1063_, v_a_1064_, v_toBind_1065_, v___f_1066_, v_a_1067_);
lean_dec_ref(v_a_1067_);
lean_dec(v___y_1058_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v_inst_1069_, lean_object* v_a_1070_, lean_object* v_inst_1071_, lean_object* v_toBind_1072_, lean_object* v___f_1073_, lean_object* v___y_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_getInfoState_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v_getInfoState_1081_ = lean_ctor_get(v_inst_1069_, 0);
lean_inc(v_getInfoState_1081_);
lean_dec_ref(v_inst_1069_);
lean_inc_n(v_toBind_1072_, 2);
lean_inc(v_a_1080_);
lean_inc(v_a_1070_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 7, 5);
lean_closure_set(v___f_1082_, 0, v_a_1070_);
lean_closure_set(v___f_1082_, 1, v_a_1080_);
lean_closure_set(v___f_1082_, 2, v_inst_1071_);
lean_closure_set(v___f_1082_, 3, v_toBind_1072_);
lean_closure_set(v___f_1082_, 4, v___f_1073_);
lean_inc_n(v___y_1074_, 2);
lean_inc_ref(v___f_1082_);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_1083_, 0, v___f_1082_);
lean_closure_set(v___f_1083_, 1, v___y_1074_);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 12, 11);
lean_closure_set(v___f_1084_, 0, v___f_1082_);
lean_closure_set(v___f_1084_, 1, v___x_1075_);
lean_closure_set(v___f_1084_, 2, v___y_1074_);
lean_closure_set(v___f_1084_, 3, v___x_1076_);
lean_closure_set(v___f_1084_, 4, v___x_1077_);
lean_closure_set(v___f_1084_, 5, v___x_1078_);
lean_closure_set(v___f_1084_, 6, v___x_1079_);
lean_closure_set(v___f_1084_, 7, v_a_1070_);
lean_closure_set(v___f_1084_, 8, v_a_1080_);
lean_closure_set(v___f_1084_, 9, v_toBind_1072_);
lean_closure_set(v___f_1084_, 10, v___f_1083_);
v___x_1085_ = lean_apply_4(v_toBind_1072_, lean_box(0), lean_box(0), v_getInfoState_1081_, v___f_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object* v_inst_1086_, lean_object* v_a_1087_, lean_object* v_inst_1088_, lean_object* v_toBind_1089_, lean_object* v___f_1090_, lean_object* v___y_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___x_1094_, lean_object* v___x_1095_, lean_object* v___x_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v_inst_1086_, v_a_1087_, v_inst_1088_, v_toBind_1089_, v___f_1090_, v___y_1091_, v___x_1092_, v___x_1093_, v___x_1094_, v___x_1095_, v___x_1096_, v_a_1097_);
lean_dec(v___y_1091_);
return v_res_1098_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_toBind_1101_, lean_object* v___f_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v___f_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___f_1120_; lean_object* v___x_3893__overap_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_inc_ref(v___x_1106_);
lean_inc_ref(v___x_1104_);
lean_inc_n(v___y_1119_, 2);
lean_inc(v_toBind_1101_);
lean_inc(v_a_1116_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 12, 11);
lean_closure_set(v___f_1120_, 0, v_inst_1099_);
lean_closure_set(v___f_1120_, 1, v_a_1116_);
lean_closure_set(v___f_1120_, 2, v_inst_1100_);
lean_closure_set(v___f_1120_, 3, v_toBind_1101_);
lean_closure_set(v___f_1120_, 4, v___f_1102_);
lean_closure_set(v___f_1120_, 5, v___y_1119_);
lean_closure_set(v___f_1120_, 6, v___x_1103_);
lean_closure_set(v___f_1120_, 7, v___x_1104_);
lean_closure_set(v___f_1120_, 8, v___x_1105_);
lean_closure_set(v___f_1120_, 9, v___x_1106_);
lean_closure_set(v___f_1120_, 10, v___x_1107_);
v___x_3893__overap_1121_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1104_, v___x_1106_, v___x_1108_, v___x_1109_, v___x_1110_, v___f_1111_, v___x_1112_, v___x_1113_, v___x_1114_, v_a_1115_, v_a_1116_);
v___x_1122_ = lean_apply_1(v___x_3893__overap_1121_, v___y_1119_);
v___x_1123_ = lean_apply_4(v_toBind_1101_, lean_box(0), lean_box(0), v___x_1122_, v___f_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1099_ = stack[0].m_obj;
lean_object* v_inst_1100_ = stack[1].m_obj;
lean_object* v_toBind_1101_ = stack[2].m_obj;
lean_object* v___f_1102_ = stack[3].m_obj;
lean_object* v___x_1103_ = stack[4].m_obj;
lean_object* v___x_1104_ = stack[5].m_obj;
lean_object* v___x_1105_ = stack[6].m_obj;
lean_object* v___x_1106_ = stack[7].m_obj;
lean_object* v___x_1107_ = stack[8].m_obj;
lean_object* v___x_1108_ = stack[9].m_obj;
lean_object* v___x_1109_ = stack[10].m_obj;
lean_object* v___x_1110_ = stack[11].m_obj;
lean_object* v___f_1111_ = stack[12].m_obj;
lean_object* v___x_1112_ = stack[13].m_obj;
lean_object* v___x_1113_ = stack[14].m_obj;
lean_object* v___x_1114_ = stack[15].m_obj;
lean_object* v_a_1115_ = stack[16].m_obj;
lean_object* v_a_1116_ = stack[17].m_obj;
lean_object* v___y_1118_ = stack[19].m_obj;
lean_object* v___y_1119_ = stack[20].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v_inst_1099_, v_inst_1100_, v_toBind_1101_, v___f_1102_, v___x_1103_, v___x_1104_, v___x_1105_, v___x_1106_, v___x_1107_, v___x_1108_, v___x_1109_, v___x_1110_, v___f_1111_, v___x_1112_, v___x_1113_, v___x_1114_, v_a_1115_, v_a_1116_, lean_box(0), v___y_1118_, v___y_1119_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object** _args){
lean_object* v_inst_1125_ = _args[0];
lean_object* v_inst_1126_ = _args[1];
lean_object* v_toBind_1127_ = _args[2];
lean_object* v___f_1128_ = _args[3];
lean_object* v___x_1129_ = _args[4];
lean_object* v___x_1130_ = _args[5];
lean_object* v___x_1131_ = _args[6];
lean_object* v___x_1132_ = _args[7];
lean_object* v___x_1133_ = _args[8];
lean_object* v___x_1134_ = _args[9];
lean_object* v___x_1135_ = _args[10];
lean_object* v___x_1136_ = _args[11];
lean_object* v___f_1137_ = _args[12];
lean_object* v___x_1138_ = _args[13];
lean_object* v___x_1139_ = _args[14];
lean_object* v___x_1140_ = _args[15];
lean_object* v_a_1141_ = _args[16];
lean_object* v_a_1142_ = _args[17];
lean_object* v_x_1143_ = _args[18];
lean_object* v___y_1144_ = _args[19];
lean_object* v___y_1145_ = _args[20];
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v_inst_1125_, v_inst_1126_, v_toBind_1127_, v___f_1128_, v___x_1129_, v___x_1130_, v___x_1131_, v___x_1132_, v___x_1133_, v___x_1134_, v___x_1135_, v___x_1136_, v___f_1137_, v___x_1138_, v___x_1139_, v___x_1140_, v_a_1141_, v_a_1142_, v_x_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
return v_res_1146_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v_toPure_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_toBind_1150_, lean_object* v___x_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___f_1158_, lean_object* v___x_1159_, lean_object* v___x_1160_, lean_object* v___x_1161_, lean_object* v_a_1162_, lean_object* v_ids_1163_, lean_object* v_ref_1164_, lean_object* v___f_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; size_t v_sz_1170_; size_t v___x_1171_; lean_object* v___x_3913__overap_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1167_ = lean_box(0);
v___f_1168_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1168_, 0, v___x_1167_);
lean_closure_set(v___f_1168_, 1, v_toPure_1147_);
lean_inc_ref(v___x_1151_);
lean_inc(v_toBind_1150_);
v___f_1169_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 21, 17);
lean_closure_set(v___f_1169_, 0, v_inst_1148_);
lean_closure_set(v___f_1169_, 1, v_inst_1149_);
lean_closure_set(v___f_1169_, 2, v_toBind_1150_);
lean_closure_set(v___f_1169_, 3, v___f_1168_);
lean_closure_set(v___f_1169_, 4, v___x_1167_);
lean_closure_set(v___f_1169_, 5, v___x_1151_);
lean_closure_set(v___f_1169_, 6, v___x_1152_);
lean_closure_set(v___f_1169_, 7, v___x_1153_);
lean_closure_set(v___f_1169_, 8, v___x_1154_);
lean_closure_set(v___f_1169_, 9, v___x_1155_);
lean_closure_set(v___f_1169_, 10, v___x_1156_);
lean_closure_set(v___f_1169_, 11, v___x_1157_);
lean_closure_set(v___f_1169_, 12, v___f_1158_);
lean_closure_set(v___f_1169_, 13, v___x_1159_);
lean_closure_set(v___f_1169_, 14, v___x_1160_);
lean_closure_set(v___f_1169_, 15, v___x_1161_);
lean_closure_set(v___f_1169_, 16, v_a_1162_);
v_sz_1170_ = lean_array_size(v_ids_1163_);
v___x_1171_ = ((size_t)0ULL);
v___x_3913__overap_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1151_, v_ids_1163_, v___f_1169_, v_sz_1170_, v___x_1171_, v___x_1167_);
v___x_1173_ = lean_apply_1(v___x_3913__overap_1172_, v_ref_1164_);
v___x_1174_ = lean_apply_4(v_toBind_1150_, lean_box(0), lean_box(0), v___x_1173_, v___f_1165_);
return v___x_1174_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1147_ = stack[0].m_obj;
lean_object* v_inst_1148_ = stack[1].m_obj;
lean_object* v_inst_1149_ = stack[2].m_obj;
lean_object* v_toBind_1150_ = stack[3].m_obj;
lean_object* v___x_1151_ = stack[4].m_obj;
lean_object* v___x_1152_ = stack[5].m_obj;
lean_object* v___x_1153_ = stack[6].m_obj;
lean_object* v___x_1154_ = stack[7].m_obj;
lean_object* v___x_1155_ = stack[8].m_obj;
lean_object* v___x_1156_ = stack[9].m_obj;
lean_object* v___x_1157_ = stack[10].m_obj;
lean_object* v___f_1158_ = stack[11].m_obj;
lean_object* v___x_1159_ = stack[12].m_obj;
lean_object* v___x_1160_ = stack[13].m_obj;
lean_object* v___x_1161_ = stack[14].m_obj;
lean_object* v_a_1162_ = stack[15].m_obj;
lean_object* v_ids_1163_ = stack[16].m_obj;
lean_object* v_ref_1164_ = stack[17].m_obj;
lean_object* v___f_1165_ = stack[18].m_obj;
lean_object* v_a_1166_ = stack[19].m_obj;
lean_object* v_res_1175_;
v_res_1175_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v_toPure_1147_, v_inst_1148_, v_inst_1149_, v_toBind_1150_, v___x_1151_, v___x_1152_, v___x_1153_, v___x_1154_, v___x_1155_, v___x_1156_, v___x_1157_, v___f_1158_, v___x_1159_, v___x_1160_, v___x_1161_, v_a_1162_, v_ids_1163_, v_ref_1164_, v___f_1165_, v_a_1166_);
stack->m_obj
 = v_res_1175_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object** _args){
lean_object* v_toPure_1176_ = _args[0];
lean_object* v_inst_1177_ = _args[1];
lean_object* v_inst_1178_ = _args[2];
lean_object* v_toBind_1179_ = _args[3];
lean_object* v___x_1180_ = _args[4];
lean_object* v___x_1181_ = _args[5];
lean_object* v___x_1182_ = _args[6];
lean_object* v___x_1183_ = _args[7];
lean_object* v___x_1184_ = _args[8];
lean_object* v___x_1185_ = _args[9];
lean_object* v___x_1186_ = _args[10];
lean_object* v___f_1187_ = _args[11];
lean_object* v___x_1188_ = _args[12];
lean_object* v___x_1189_ = _args[13];
lean_object* v___x_1190_ = _args[14];
lean_object* v_a_1191_ = _args[15];
lean_object* v_ids_1192_ = _args[16];
lean_object* v_ref_1193_ = _args[17];
lean_object* v___f_1194_ = _args[18];
lean_object* v_a_1195_ = _args[19];
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v_toPure_1176_, v_inst_1177_, v_inst_1178_, v_toBind_1179_, v___x_1180_, v___x_1181_, v___x_1182_, v___x_1183_, v___x_1184_, v___x_1185_, v___x_1186_, v___f_1187_, v___x_1188_, v___x_1189_, v___x_1190_, v_a_1191_, v_ids_1192_, v_ref_1193_, v___f_1194_, v_a_1195_);
return v_res_1196_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_toPure_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_toBind_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v___f_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v_ids_1212_, lean_object* v_ref_1213_, lean_object* v___f_1214_, lean_object* v_ns_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_3930__overap_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_inc(v_ref_1213_);
lean_inc(v_a_1216_);
lean_inc_ref(v___x_1211_);
lean_inc_ref(v___x_1210_);
lean_inc_ref(v___x_1209_);
lean_inc(v___f_1208_);
lean_inc_ref(v___x_1203_);
lean_inc_ref(v___x_1201_);
lean_inc(v_toBind_1200_);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed), 20, 19);
lean_closure_set(v___f_1217_, 0, v_toPure_1197_);
lean_closure_set(v___f_1217_, 1, v_inst_1198_);
lean_closure_set(v___f_1217_, 2, v_inst_1199_);
lean_closure_set(v___f_1217_, 3, v_toBind_1200_);
lean_closure_set(v___f_1217_, 4, v___x_1201_);
lean_closure_set(v___f_1217_, 5, v___x_1202_);
lean_closure_set(v___f_1217_, 6, v___x_1203_);
lean_closure_set(v___f_1217_, 7, v___x_1204_);
lean_closure_set(v___f_1217_, 8, v___x_1205_);
lean_closure_set(v___f_1217_, 9, v___x_1206_);
lean_closure_set(v___f_1217_, 10, v___x_1207_);
lean_closure_set(v___f_1217_, 11, v___f_1208_);
lean_closure_set(v___f_1217_, 12, v___x_1209_);
lean_closure_set(v___f_1217_, 13, v___x_1210_);
lean_closure_set(v___f_1217_, 14, v___x_1211_);
lean_closure_set(v___f_1217_, 15, v_a_1216_);
lean_closure_set(v___f_1217_, 16, v_ids_1212_);
lean_closure_set(v___f_1217_, 17, v_ref_1213_);
lean_closure_set(v___f_1217_, 18, v___f_1214_);
v___x_3930__overap_1218_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1201_, v___x_1203_, v___x_1210_, v___x_1209_, v___f_1208_, v___x_1211_, v_ns_1215_, v_a_1216_);
v___x_1219_ = lean_apply_1(v___x_3930__overap_1218_, v_ref_1213_);
v___x_1220_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v___x_1219_, v___f_1217_);
return v___x_1220_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1197_ = stack[0].m_obj;
lean_object* v_inst_1198_ = stack[1].m_obj;
lean_object* v_inst_1199_ = stack[2].m_obj;
lean_object* v_toBind_1200_ = stack[3].m_obj;
lean_object* v___x_1201_ = stack[4].m_obj;
lean_object* v___x_1202_ = stack[5].m_obj;
lean_object* v___x_1203_ = stack[6].m_obj;
lean_object* v___x_1204_ = stack[7].m_obj;
lean_object* v___x_1205_ = stack[8].m_obj;
lean_object* v___x_1206_ = stack[9].m_obj;
lean_object* v___x_1207_ = stack[10].m_obj;
lean_object* v___f_1208_ = stack[11].m_obj;
lean_object* v___x_1209_ = stack[12].m_obj;
lean_object* v___x_1210_ = stack[13].m_obj;
lean_object* v___x_1211_ = stack[14].m_obj;
lean_object* v_ids_1212_ = stack[15].m_obj;
lean_object* v_ref_1213_ = stack[16].m_obj;
lean_object* v___f_1214_ = stack[17].m_obj;
lean_object* v_ns_1215_ = stack[18].m_obj;
lean_object* v_a_1216_ = stack[19].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_toPure_1197_, v_inst_1198_, v_inst_1199_, v_toBind_1200_, v___x_1201_, v___x_1202_, v___x_1203_, v___x_1204_, v___x_1205_, v___x_1206_, v___x_1207_, v___f_1208_, v___x_1209_, v___x_1210_, v___x_1211_, v_ids_1212_, v_ref_1213_, v___f_1214_, v_ns_1215_, v_a_1216_);
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toPure_1222_ = _args[0];
lean_object* v_inst_1223_ = _args[1];
lean_object* v_inst_1224_ = _args[2];
lean_object* v_toBind_1225_ = _args[3];
lean_object* v___x_1226_ = _args[4];
lean_object* v___x_1227_ = _args[5];
lean_object* v___x_1228_ = _args[6];
lean_object* v___x_1229_ = _args[7];
lean_object* v___x_1230_ = _args[8];
lean_object* v___x_1231_ = _args[9];
lean_object* v___x_1232_ = _args[10];
lean_object* v___f_1233_ = _args[11];
lean_object* v___x_1234_ = _args[12];
lean_object* v___x_1235_ = _args[13];
lean_object* v___x_1236_ = _args[14];
lean_object* v_ids_1237_ = _args[15];
lean_object* v_ref_1238_ = _args[16];
lean_object* v___f_1239_ = _args[17];
lean_object* v_ns_1240_ = _args[18];
lean_object* v_a_1241_ = _args[19];
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_toPure_1222_, v_inst_1223_, v_inst_1224_, v_toBind_1225_, v___x_1226_, v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_, v___x_1231_, v___x_1232_, v___f_1233_, v___x_1234_, v___x_1235_, v___x_1236_, v_ids_1237_, v_ref_1238_, v___f_1239_, v_ns_1240_, v_a_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v___x_1243_, lean_object* v___x_1244_, lean_object* v___f_1245_, lean_object* v_toBind_1246_, lean_object* v___f_1247_, lean_object* v_a_1248_, lean_object* v_x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_3945__overap_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_3945__overap_1252_ = l_Lean_activateScoped___redArg(v___x_1243_, v___x_1244_, v___f_1245_, v_a_1248_);
lean_inc(v___y_1251_);
v___x_1253_ = lean_apply_1(v___x_3945__overap_1252_, v___y_1251_);
v___x_1254_ = lean_apply_4(v_toBind_1246_, lean_box(0), lean_box(0), v___x_1253_, v___f_1247_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object* v___x_1255_, lean_object* v___x_1256_, lean_object* v___f_1257_, lean_object* v_toBind_1258_, lean_object* v___f_1259_, lean_object* v_a_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(v___x_1255_, v___x_1256_, v___f_1257_, v_toBind_1258_, v___f_1259_, v_a_1260_, v_x_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v___x_1265_, lean_object* v___f_1266_, lean_object* v_a_1267_, lean_object* v___x_1268_, lean_object* v___y_1269_, lean_object* v_toBind_1270_, lean_object* v___f_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_3955__overap_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_3955__overap_1273_ = l_List_forIn_x27_loop___redArg(v___x_1265_, v___f_1266_, v_a_1267_, v___x_1268_);
lean_inc(v___y_1269_);
v___x_1274_ = lean_apply_1(v___x_3955__overap_1273_, v___y_1269_);
v___x_1275_ = lean_apply_4(v_toBind_1270_, lean_box(0), lean_box(0), v___x_1274_, v___f_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object* v___x_1276_, lean_object* v___f_1277_, lean_object* v_a_1278_, lean_object* v___x_1279_, lean_object* v___y_1280_, lean_object* v_toBind_1281_, lean_object* v___f_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v___x_1276_, v___f_1277_, v_a_1278_, v___x_1279_, v___y_1280_, v_toBind_1281_, v___f_1282_, v_a_1283_);
lean_dec(v___y_1280_);
lean_dec(v_a_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v___x_1285_, lean_object* v___f_1286_, lean_object* v___x_1287_, lean_object* v___y_1288_, lean_object* v_toBind_1289_, lean_object* v___f_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v___f_1294_, lean_object* v___x_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___f_1298_; lean_object* v___x_3968__overap_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_toBind_1289_);
lean_inc_n(v___y_1288_, 2);
lean_inc(v_a_1297_);
lean_inc_ref(v___x_1285_);
v___f_1298_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 8, 7);
lean_closure_set(v___f_1298_, 0, v___x_1285_);
lean_closure_set(v___f_1298_, 1, v___f_1286_);
lean_closure_set(v___f_1298_, 2, v_a_1297_);
lean_closure_set(v___f_1298_, 3, v___x_1287_);
lean_closure_set(v___f_1298_, 4, v___y_1288_);
lean_closure_set(v___f_1298_, 5, v_toBind_1289_);
lean_closure_set(v___f_1298_, 6, v___f_1290_);
v___x_3968__overap_1299_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1285_, v___x_1291_, v___x_1292_, v___x_1293_, v___f_1294_, v___x_1295_, v_a_1296_, v_a_1297_);
v___x_1300_ = lean_apply_1(v___x_3968__overap_1299_, v___y_1288_);
v___x_1301_ = lean_apply_4(v_toBind_1289_, lean_box(0), lean_box(0), v___x_1300_, v___f_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object* v___x_1302_, lean_object* v___f_1303_, lean_object* v___x_1304_, lean_object* v___y_1305_, lean_object* v_toBind_1306_, lean_object* v___f_1307_, lean_object* v___x_1308_, lean_object* v___x_1309_, lean_object* v___x_1310_, lean_object* v___f_1311_, lean_object* v___x_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(v___x_1302_, v___f_1303_, v___x_1304_, v___y_1305_, v_toBind_1306_, v___f_1307_, v___x_1308_, v___x_1309_, v___x_1310_, v___f_1311_, v___x_1312_, v_a_1313_, v_a_1314_);
lean_dec(v___y_1305_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v___x_1316_, lean_object* v___f_1317_, lean_object* v___x_1318_, lean_object* v_toBind_1319_, lean_object* v___f_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___f_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v_a_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___f_1331_; lean_object* v___x_3984__overap_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_inc(v_a_1327_);
lean_inc_ref(v___x_1325_);
lean_inc_ref(v___x_1321_);
lean_inc(v_toBind_1319_);
lean_inc_n(v___y_1330_, 2);
lean_inc_ref(v___x_1316_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed), 13, 12);
lean_closure_set(v___f_1331_, 0, v___x_1316_);
lean_closure_set(v___f_1331_, 1, v___f_1317_);
lean_closure_set(v___f_1331_, 2, v___x_1318_);
lean_closure_set(v___f_1331_, 3, v___y_1330_);
lean_closure_set(v___f_1331_, 4, v_toBind_1319_);
lean_closure_set(v___f_1331_, 5, v___f_1320_);
lean_closure_set(v___f_1331_, 6, v___x_1321_);
lean_closure_set(v___f_1331_, 7, v___x_1322_);
lean_closure_set(v___f_1331_, 8, v___x_1323_);
lean_closure_set(v___f_1331_, 9, v___f_1324_);
lean_closure_set(v___f_1331_, 10, v___x_1325_);
lean_closure_set(v___f_1331_, 11, v_a_1327_);
v___x_3984__overap_1332_ = l_Lean_resolveNamespace___redArg(v___x_1316_, v___x_1325_, v___x_1321_, v___x_1326_, v_a_1327_);
v___x_1333_ = lean_apply_1(v___x_3984__overap_1332_, v___y_1330_);
v___x_1334_ = lean_apply_4(v_toBind_1319_, lean_box(0), lean_box(0), v___x_1333_, v___f_1331_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object* v___x_1335_, lean_object* v___f_1336_, lean_object* v___x_1337_, lean_object* v_toBind_1338_, lean_object* v___f_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v___f_1343_, lean_object* v___x_1344_, lean_object* v___x_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(v___x_1335_, v___f_1336_, v___x_1337_, v_toBind_1338_, v___f_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v___f_1343_, v___x_1344_, v___x_1345_, v_a_1346_, v_x_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v___f_1353_, lean_object* v_a_1354_, lean_object* v___y_1355_, lean_object* v_toBind_1356_, lean_object* v___f_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_3997__overap_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_3997__overap_1359_ = l_Lean_activateScoped___redArg(v___x_1351_, v___x_1352_, v___f_1353_, v_a_1354_);
lean_inc(v___y_1355_);
v___x_1360_ = lean_apply_1(v___x_3997__overap_1359_, v___y_1355_);
v___x_1361_ = lean_apply_4(v_toBind_1356_, lean_box(0), lean_box(0), v___x_1360_, v___f_1357_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___f_1364_, lean_object* v_a_1365_, lean_object* v___y_1366_, lean_object* v_toBind_1367_, lean_object* v___f_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(v___x_1362_, v___x_1363_, v___f_1364_, v_a_1365_, v___y_1366_, v_toBind_1367_, v___f_1368_, v_a_1369_);
lean_dec(v___y_1366_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v___x_1371_, lean_object* v___x_1372_, lean_object* v___f_1373_, lean_object* v_toBind_1374_, lean_object* v___f_1375_, lean_object* v___x_1376_, lean_object* v_inst_1377_, lean_object* v_a_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_inc(v_toBind_1374_);
lean_inc(v___y_1381_);
lean_inc(v_a_1378_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed), 8, 7);
lean_closure_set(v___f_1382_, 0, v___x_1371_);
lean_closure_set(v___f_1382_, 1, v___x_1372_);
lean_closure_set(v___f_1382_, 2, v___f_1373_);
lean_closure_set(v___f_1382_, 3, v_a_1378_);
lean_closure_set(v___f_1382_, 4, v___y_1381_);
lean_closure_set(v___f_1382_, 5, v_toBind_1374_);
lean_closure_set(v___f_1382_, 6, v___f_1375_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_a_1378_);
lean_ctor_set(v___x_1383_, 1, v___x_1376_);
v___x_1384_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1377_, v___x_1383_, v___y_1381_);
v___x_1385_ = lean_apply_4(v_toBind_1374_, lean_box(0), lean_box(0), v___x_1384_, v___f_1382_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object* v___x_1386_, lean_object* v___x_1387_, lean_object* v___f_1388_, lean_object* v_toBind_1389_, lean_object* v___f_1390_, lean_object* v___x_1391_, lean_object* v_inst_1392_, lean_object* v_a_1393_, lean_object* v_x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(v___x_1386_, v___x_1387_, v___f_1388_, v_toBind_1389_, v___f_1390_, v___x_1391_, v_inst_1392_, v_a_1393_, v_x_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
return v_res_1397_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object* v_toPure_1406_, lean_object* v_inst_1407_, lean_object* v_toBind_1408_, uint8_t v___x_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v_stx_1413_, lean_object* v___f_1414_, lean_object* v___x_1415_, lean_object* v___x_1416_, lean_object* v___f_1417_, lean_object* v___f_1418_, lean_object* v_inst_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___f_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___f_1430_, lean_object* v___f_1431_, lean_object* v_ref_1432_){
_start:
{
lean_object* v___f_1433_; 
lean_inc(v_toBind_1408_);
lean_inc(v_inst_1407_);
lean_inc(v_ref_1432_);
lean_inc(v_toPure_1406_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1433_, 0, v_toPure_1406_);
lean_closure_set(v___f_1433_, 1, v_ref_1432_);
lean_closure_set(v___f_1433_, 2, v_inst_1407_);
lean_closure_set(v___f_1433_, 3, v_toBind_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__0));
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1411_);
lean_inc_ref(v___x_1410_);
v___x_1435_ = l_Lean_Name_mkStr4(v___x_1410_, v___x_1411_, v___x_1412_, v___x_1434_);
lean_inc(v_stx_1413_);
v___x_1436_ = l_Lean_Syntax_isOfKind(v_stx_1413_, v___x_1435_);
lean_dec(v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__1));
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1411_);
lean_inc_ref(v___x_1410_);
v___x_1438_ = l_Lean_Name_mkStr4(v___x_1410_, v___x_1411_, v___x_1412_, v___x_1437_);
lean_inc(v_stx_1413_);
v___x_1439_ = l_Lean_Syntax_isOfKind(v_stx_1413_, v___x_1438_);
lean_dec(v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__2));
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1411_);
lean_inc_ref(v___x_1410_);
v___x_1441_ = l_Lean_Name_mkStr4(v___x_1410_, v___x_1411_, v___x_1412_, v___x_1440_);
lean_inc(v_stx_1413_);
v___x_1442_ = l_Lean_Syntax_isOfKind(v_stx_1413_, v___x_1441_);
lean_dec(v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
lean_dec(v___f_1431_);
lean_dec_ref(v___f_1430_);
v___x_1443_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__3));
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1411_);
lean_inc_ref(v___x_1410_);
v___x_1444_ = l_Lean_Name_mkStr4(v___x_1410_, v___x_1411_, v___x_1412_, v___x_1443_);
lean_inc(v_stx_1413_);
v___x_1445_ = l_Lean_Syntax_isOfKind(v_stx_1413_, v___x_1444_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___f_1446_; lean_object* v___x_4088__overap_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v___f_1426_);
lean_dec(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v___x_1416_);
lean_dec(v_stx_1413_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec(v_inst_1407_);
lean_dec(v_toPure_1406_);
lean_inc(v_ref_1432_);
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1446_, 0, v___f_1414_);
lean_closure_set(v___f_1446_, 1, v_ref_1432_);
v___x_4088__overap_1447_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1415_);
v___x_1448_ = lean_apply_1(v___x_4088__overap_1447_, v_ref_1432_);
lean_inc(v_toBind_1408_);
v___x_1449_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1448_, v___f_1446_);
v___x_1450_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1449_, v___f_1433_);
return v___x_1450_;
}
else
{
lean_object* v___f_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v_nsStx_1454_; lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___y_1458_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
lean_inc_n(v_ref_1432_, 2);
lean_inc(v___f_1414_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1451_, 0, v___f_1414_);
lean_closure_set(v___f_1451_, 1, v_ref_1432_);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1452_, 0, v___f_1414_);
lean_closure_set(v___f_1452_, 1, v_ref_1432_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v_nsStx_1454_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1453_);
v___x_1455_ = lean_unsigned_to_nat(2u);
v___f_1456_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1456_, 0, v___x_1410_);
lean_closure_set(v___f_1456_, 1, v___x_1411_);
lean_closure_set(v___f_1456_, 2, v___x_1412_);
lean_closure_set(v___f_1456_, 3, v___x_1453_);
lean_closure_set(v___f_1456_, 4, v___x_1455_);
v___x_1478_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1455_);
lean_dec(v_stx_1413_);
v___x_1479_ = l_Lean_Syntax_getArgs(v___x_1478_);
lean_dec(v___x_1478_);
v___x_1480_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__4));
v___x_1481_ = lean_array_get_size(v___x_1479_);
v___x_1482_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1483_ = lean_nat_dec_lt(v___x_1453_, v___x_1481_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v___x_1479_);
v___y_1458_ = v___x_1480_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v_snd_1492_; 
v___x_1484_ = lean_box(v___x_1445_);
v___x_1485_ = lean_box(v___x_1442_);
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1486_, 0, v___x_1484_);
lean_closure_set(v___f_1486_, 1, v___x_1485_);
v___x_1487_ = lean_box(v___x_1483_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1480_);
v___x_1489_ = ((size_t)0ULL);
v___x_1490_ = lean_usize_of_nat(v___x_1481_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1482_, v___f_1486_, v___x_1479_, v___x_1489_, v___x_1490_, v___x_1488_);
v_snd_1492_ = lean_ctor_get(v___x_1491_, 1);
lean_inc(v_snd_1492_);
lean_dec(v___x_1491_);
v___y_1458_ = v_snd_1492_;
goto v___jp_1457_;
}
v___jp_1457_:
{
size_t v_sz_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v_sz_1459_ = lean_array_size(v___y_1458_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1416_, v___f_1456_, v_sz_1459_, v___x_1460_, v___y_1458_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_4100__overap_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v_nsStx_1454_);
lean_dec_ref(v___f_1451_);
lean_dec_ref(v___x_1429_);
lean_dec_ref(v___x_1428_);
lean_dec_ref(v___x_1427_);
lean_dec(v___f_1426_);
lean_dec(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1423_);
lean_dec_ref(v___x_1422_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec(v_inst_1407_);
lean_dec(v_toPure_1406_);
v___x_4100__overap_1462_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1415_);
v___x_1463_ = lean_apply_1(v___x_4100__overap_1462_, v_ref_1432_);
lean_inc(v_toBind_1408_);
v___x_1464_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1463_, v___f_1452_);
v___x_1465_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1464_, v___f_1433_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1467_; size_t v_sz_1468_; lean_object* v_tos_1469_; lean_object* v_froms_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_4116__overap_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v___f_1452_);
v_val_1466_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_n(v_val_1466_, 2);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1467_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1468_ = lean_array_size(v_val_1466_);
v_tos_1469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1467_, v___f_1417_, v_sz_1468_, v___x_1460_, v_val_1466_);
v_froms_1470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1467_, v___f_1418_, v_sz_1468_, v___x_1460_, v_val_1466_);
v___x_1471_ = lean_box(0);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed__const__1));
lean_inc(v_nsStx_1454_);
lean_inc(v_ref_1432_);
lean_inc_ref(v___x_1429_);
lean_inc_ref(v___x_1423_);
lean_inc_ref(v___x_1422_);
lean_inc_ref(v___x_1420_);
lean_inc_n(v_toBind_1408_, 2);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_1473_, 0, v_froms_1470_);
lean_closure_set(v___f_1473_, 1, v_tos_1469_);
lean_closure_set(v___f_1473_, 2, v_toPure_1406_);
lean_closure_set(v___f_1473_, 3, v_inst_1419_);
lean_closure_set(v___f_1473_, 4, v_inst_1407_);
lean_closure_set(v___f_1473_, 5, v_toBind_1408_);
lean_closure_set(v___f_1473_, 6, v___x_1420_);
lean_closure_set(v___f_1473_, 7, v___x_1421_);
lean_closure_set(v___f_1473_, 8, v___x_1422_);
lean_closure_set(v___f_1473_, 9, v___x_1423_);
lean_closure_set(v___f_1473_, 10, v___x_1415_);
lean_closure_set(v___f_1473_, 11, v___x_1424_);
lean_closure_set(v___f_1473_, 12, v___x_1425_);
lean_closure_set(v___f_1473_, 13, v___f_1426_);
lean_closure_set(v___f_1473_, 14, v___x_1427_);
lean_closure_set(v___f_1473_, 15, v___x_1428_);
lean_closure_set(v___f_1473_, 16, v___x_1429_);
lean_closure_set(v___f_1473_, 17, v___x_1472_);
lean_closure_set(v___f_1473_, 18, v_ref_1432_);
lean_closure_set(v___f_1473_, 19, v___f_1451_);
lean_closure_set(v___f_1473_, 20, v___x_1471_);
lean_closure_set(v___f_1473_, 21, v_nsStx_1454_);
v___x_4116__overap_1474_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1420_, v___x_1429_, v___x_1422_, v___x_1423_, v_nsStx_1454_);
v___x_1475_ = lean_apply_1(v___x_4116__overap_1474_, v_ref_1432_);
v___x_1476_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1475_, v___f_1473_);
v___x_1477_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1476_, v___f_1433_);
return v___x_1477_;
}
}
}
}
else
{
lean_object* v___f_1493_; lean_object* v___x_1494_; lean_object* v_nsStx_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_ids_1499_; lean_object* v___f_1500_; lean_object* v___x_4145__overap_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_inc_n(v_ref_1432_, 2);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1493_, 0, v___f_1414_);
lean_closure_set(v___f_1493_, 1, v_ref_1432_);
v___x_1494_ = lean_unsigned_to_nat(0u);
v_nsStx_1495_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1494_);
v___x_1496_ = lean_unsigned_to_nat(2u);
v___x_1497_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1496_);
lean_dec(v_stx_1413_);
v___x_1498_ = lean_box(0);
v_ids_1499_ = l_Lean_Syntax_getArgs(v___x_1497_);
lean_dec(v___x_1497_);
lean_inc(v_nsStx_1495_);
lean_inc_ref(v___x_1429_);
lean_inc_ref(v___x_1423_);
lean_inc_ref(v___x_1422_);
lean_inc_ref(v___x_1420_);
lean_inc_n(v_toBind_1408_, 2);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed), 23, 22);
lean_closure_set(v___f_1500_, 0, v_ids_1499_);
lean_closure_set(v___f_1500_, 1, v___f_1430_);
lean_closure_set(v___f_1500_, 2, v_inst_1407_);
lean_closure_set(v___f_1500_, 3, v_ref_1432_);
lean_closure_set(v___f_1500_, 4, v_toBind_1408_);
lean_closure_set(v___f_1500_, 5, v___f_1493_);
lean_closure_set(v___f_1500_, 6, v_toPure_1406_);
lean_closure_set(v___f_1500_, 7, v_inst_1419_);
lean_closure_set(v___f_1500_, 8, v___x_1420_);
lean_closure_set(v___f_1500_, 9, v___x_1421_);
lean_closure_set(v___f_1500_, 10, v___x_1422_);
lean_closure_set(v___f_1500_, 11, v___x_1423_);
lean_closure_set(v___f_1500_, 12, v___x_1415_);
lean_closure_set(v___f_1500_, 13, v___x_1424_);
lean_closure_set(v___f_1500_, 14, v___x_1425_);
lean_closure_set(v___f_1500_, 15, v___f_1426_);
lean_closure_set(v___f_1500_, 16, v___x_1427_);
lean_closure_set(v___f_1500_, 17, v___x_1428_);
lean_closure_set(v___f_1500_, 18, v___x_1429_);
lean_closure_set(v___f_1500_, 19, v___f_1431_);
lean_closure_set(v___f_1500_, 20, v___x_1498_);
lean_closure_set(v___f_1500_, 21, v_nsStx_1495_);
v___x_4145__overap_1501_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1420_, v___x_1429_, v___x_1422_, v___x_1423_, v_nsStx_1495_);
v___x_1502_ = lean_apply_1(v___x_4145__overap_1501_, v_ref_1432_);
v___x_1503_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1502_, v___f_1500_);
v___x_1504_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1503_, v___f_1433_);
return v___x_1504_;
}
}
else
{
lean_object* v___f_1505_; lean_object* v___x_1506_; lean_object* v_ns_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_ids_1510_; lean_object* v___f_1511_; lean_object* v___x_4153__overap_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v___f_1431_);
lean_dec_ref(v___f_1430_);
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_inc_n(v_ref_1432_, 2);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1505_, 0, v___f_1414_);
lean_closure_set(v___f_1505_, 1, v_ref_1432_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v_ns_1507_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1506_);
v___x_1508_ = lean_unsigned_to_nat(2u);
v___x_1509_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1508_);
lean_dec(v_stx_1413_);
v_ids_1510_ = l_Lean_Syntax_getArgs(v___x_1509_);
lean_dec(v___x_1509_);
lean_inc(v_ns_1507_);
lean_inc_ref(v___x_1429_);
lean_inc_ref(v___x_1423_);
lean_inc_ref(v___x_1422_);
lean_inc_ref(v___x_1420_);
lean_inc_n(v_toBind_1408_, 2);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed), 20, 19);
lean_closure_set(v___f_1511_, 0, v_toPure_1406_);
lean_closure_set(v___f_1511_, 1, v_inst_1419_);
lean_closure_set(v___f_1511_, 2, v_inst_1407_);
lean_closure_set(v___f_1511_, 3, v_toBind_1408_);
lean_closure_set(v___f_1511_, 4, v___x_1420_);
lean_closure_set(v___f_1511_, 5, v___x_1421_);
lean_closure_set(v___f_1511_, 6, v___x_1422_);
lean_closure_set(v___f_1511_, 7, v___x_1423_);
lean_closure_set(v___f_1511_, 8, v___x_1415_);
lean_closure_set(v___f_1511_, 9, v___x_1424_);
lean_closure_set(v___f_1511_, 10, v___x_1425_);
lean_closure_set(v___f_1511_, 11, v___f_1426_);
lean_closure_set(v___f_1511_, 12, v___x_1427_);
lean_closure_set(v___f_1511_, 13, v___x_1428_);
lean_closure_set(v___f_1511_, 14, v___x_1429_);
lean_closure_set(v___f_1511_, 15, v_ids_1510_);
lean_closure_set(v___f_1511_, 16, v_ref_1432_);
lean_closure_set(v___f_1511_, 17, v___f_1505_);
lean_closure_set(v___f_1511_, 18, v_ns_1507_);
v___x_4153__overap_1512_ = l_Lean_resolveNamespace___redArg(v___x_1420_, v___x_1429_, v___x_1422_, v___x_1423_, v_ns_1507_);
v___x_1513_ = lean_apply_1(v___x_4153__overap_1512_, v_ref_1432_);
v___x_1514_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1513_, v___f_1511_);
v___x_1515_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1514_, v___f_1433_);
return v___x_1515_;
}
}
else
{
lean_object* v___f_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_nss_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; size_t v_sz_1524_; size_t v___x_1525_; lean_object* v___x_4165__overap_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v___f_1430_);
lean_dec(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec(v_inst_1407_);
lean_inc(v_ref_1432_);
v___f_1516_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1516_, 0, v___f_1414_);
lean_closure_set(v___f_1516_, 1, v_ref_1432_);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1517_);
lean_dec(v_stx_1413_);
v_nss_1519_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1520_ = lean_box(0);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1521_, 0, v___x_1520_);
lean_closure_set(v___f_1521_, 1, v_toPure_1406_);
lean_inc_ref(v___f_1521_);
lean_inc_n(v_toBind_1408_, 3);
lean_inc_ref(v___x_1422_);
lean_inc_ref_n(v___x_1420_, 2);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed), 9, 5);
lean_closure_set(v___f_1522_, 0, v___x_1420_);
lean_closure_set(v___f_1522_, 1, v___x_1422_);
lean_closure_set(v___f_1522_, 2, v___f_1431_);
lean_closure_set(v___f_1522_, 3, v_toBind_1408_);
lean_closure_set(v___f_1522_, 4, v___f_1521_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 15, 11);
lean_closure_set(v___f_1523_, 0, v___x_1420_);
lean_closure_set(v___f_1523_, 1, v___f_1522_);
lean_closure_set(v___f_1523_, 2, v___x_1520_);
lean_closure_set(v___f_1523_, 3, v_toBind_1408_);
lean_closure_set(v___f_1523_, 4, v___f_1521_);
lean_closure_set(v___f_1523_, 5, v___x_1422_);
lean_closure_set(v___f_1523_, 6, v___x_1428_);
lean_closure_set(v___f_1523_, 7, v___x_1427_);
lean_closure_set(v___f_1523_, 8, v___f_1426_);
lean_closure_set(v___f_1523_, 9, v___x_1429_);
lean_closure_set(v___f_1523_, 10, v___x_1423_);
v_sz_1524_ = lean_array_size(v_nss_1519_);
v___x_1525_ = ((size_t)0ULL);
v___x_4165__overap_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1420_, v_nss_1519_, v___f_1523_, v_sz_1524_, v___x_1525_, v___x_1520_);
v___x_1527_ = lean_apply_1(v___x_4165__overap_1526_, v_ref_1432_);
v___x_1528_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1527_, v___f_1516_);
v___x_1529_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1528_, v___f_1433_);
return v___x_1529_;
}
}
else
{
lean_object* v___f_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_nss_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___f_1537_; lean_object* v___f_1538_; size_t v_sz_1539_; size_t v___x_1540_; lean_object* v___x_4178__overap_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v___f_1430_);
lean_dec(v___x_1425_);
lean_dec_ref(v___x_1424_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v___f_1418_);
lean_dec_ref(v___f_1417_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_inc(v_ref_1432_);
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1530_, 0, v___f_1414_);
lean_closure_set(v___f_1530_, 1, v_ref_1432_);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = l_Lean_Syntax_getArg(v_stx_1413_, v___x_1531_);
lean_dec(v_stx_1413_);
v___x_1533_ = lean_box(0);
v_nss_1534_ = l_Lean_Syntax_getArgs(v___x_1532_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1536_, 0, v___x_1535_);
lean_closure_set(v___f_1536_, 1, v_toPure_1406_);
lean_inc_ref(v___f_1536_);
lean_inc_n(v_toBind_1408_, 3);
lean_inc_ref(v___x_1422_);
lean_inc_ref_n(v___x_1420_, 2);
v___f_1537_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed), 11, 7);
lean_closure_set(v___f_1537_, 0, v___x_1420_);
lean_closure_set(v___f_1537_, 1, v___x_1422_);
lean_closure_set(v___f_1537_, 2, v___f_1431_);
lean_closure_set(v___f_1537_, 3, v_toBind_1408_);
lean_closure_set(v___f_1537_, 4, v___f_1536_);
lean_closure_set(v___f_1537_, 5, v___x_1533_);
lean_closure_set(v___f_1537_, 6, v_inst_1407_);
v___f_1538_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 15, 11);
lean_closure_set(v___f_1538_, 0, v___x_1420_);
lean_closure_set(v___f_1538_, 1, v___f_1537_);
lean_closure_set(v___f_1538_, 2, v___x_1535_);
lean_closure_set(v___f_1538_, 3, v_toBind_1408_);
lean_closure_set(v___f_1538_, 4, v___f_1536_);
lean_closure_set(v___f_1538_, 5, v___x_1422_);
lean_closure_set(v___f_1538_, 6, v___x_1428_);
lean_closure_set(v___f_1538_, 7, v___x_1427_);
lean_closure_set(v___f_1538_, 8, v___f_1426_);
lean_closure_set(v___f_1538_, 9, v___x_1429_);
lean_closure_set(v___f_1538_, 10, v___x_1423_);
v_sz_1539_ = lean_array_size(v_nss_1534_);
v___x_1540_ = ((size_t)0ULL);
v___x_4178__overap_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1420_, v_nss_1534_, v___f_1538_, v_sz_1539_, v___x_1540_, v___x_1535_);
v___x_1542_ = lean_apply_1(v___x_4178__overap_1541_, v_ref_1432_);
v___x_1543_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1542_, v___f_1530_);
v___x_1544_ = lean_apply_4(v_toBind_1408_, lean_box(0), lean_box(0), v___x_1543_, v___f_1433_);
return v___x_1544_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1406_ = stack[0].m_obj;
lean_object* v_inst_1407_ = stack[1].m_obj;
lean_object* v_toBind_1408_ = stack[2].m_obj;
uint8_t v___x_1409_ = stack[3].m_num;
lean_object* v___x_1410_ = stack[4].m_obj;
lean_object* v___x_1411_ = stack[5].m_obj;
lean_object* v___x_1412_ = stack[6].m_obj;
lean_object* v_stx_1413_ = stack[7].m_obj;
lean_object* v___f_1414_ = stack[8].m_obj;
lean_object* v___x_1415_ = stack[9].m_obj;
lean_object* v___x_1416_ = stack[10].m_obj;
lean_object* v___f_1417_ = stack[11].m_obj;
lean_object* v___f_1418_ = stack[12].m_obj;
lean_object* v_inst_1419_ = stack[13].m_obj;
lean_object* v___x_1420_ = stack[14].m_obj;
lean_object* v___x_1421_ = stack[15].m_obj;
lean_object* v___x_1422_ = stack[16].m_obj;
lean_object* v___x_1423_ = stack[17].m_obj;
lean_object* v___x_1424_ = stack[18].m_obj;
lean_object* v___x_1425_ = stack[19].m_obj;
lean_object* v___f_1426_ = stack[20].m_obj;
lean_object* v___x_1427_ = stack[21].m_obj;
lean_object* v___x_1428_ = stack[22].m_obj;
lean_object* v___x_1429_ = stack[23].m_obj;
lean_object* v___f_1430_ = stack[24].m_obj;
lean_object* v___f_1431_ = stack[25].m_obj;
lean_object* v_ref_1432_ = stack[26].m_obj;
lean_object* v_res_1545_;
v_res_1545_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(v_toPure_1406_, v_inst_1407_, v_toBind_1408_, v___x_1409_, v___x_1410_, v___x_1411_, v___x_1412_, v_stx_1413_, v___f_1414_, v___x_1415_, v___x_1416_, v___f_1417_, v___f_1418_, v_inst_1419_, v___x_1420_, v___x_1421_, v___x_1422_, v___x_1423_, v___x_1424_, v___x_1425_, v___f_1426_, v___x_1427_, v___x_1428_, v___x_1429_, v___f_1430_, v___f_1431_, v_ref_1432_);
stack->m_obj
 = v_res_1545_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object** _args){
lean_object* v_toPure_1546_ = _args[0];
lean_object* v_inst_1547_ = _args[1];
lean_object* v_toBind_1548_ = _args[2];
lean_object* v___x_1549_ = _args[3];
lean_object* v___x_1550_ = _args[4];
lean_object* v___x_1551_ = _args[5];
lean_object* v___x_1552_ = _args[6];
lean_object* v_stx_1553_ = _args[7];
lean_object* v___f_1554_ = _args[8];
lean_object* v___x_1555_ = _args[9];
lean_object* v___x_1556_ = _args[10];
lean_object* v___f_1557_ = _args[11];
lean_object* v___f_1558_ = _args[12];
lean_object* v_inst_1559_ = _args[13];
lean_object* v___x_1560_ = _args[14];
lean_object* v___x_1561_ = _args[15];
lean_object* v___x_1562_ = _args[16];
lean_object* v___x_1563_ = _args[17];
lean_object* v___x_1564_ = _args[18];
lean_object* v___x_1565_ = _args[19];
lean_object* v___f_1566_ = _args[20];
lean_object* v___x_1567_ = _args[21];
lean_object* v___x_1568_ = _args[22];
lean_object* v___x_1569_ = _args[23];
lean_object* v___f_1570_ = _args[24];
lean_object* v___f_1571_ = _args[25];
lean_object* v_ref_1572_ = _args[26];
_start:
{
uint8_t v___x_6207__boxed_1573_; lean_object* v_res_1574_; 
v___x_6207__boxed_1573_ = lean_unbox(v___x_1549_);
v_res_1574_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(v_toPure_1546_, v_inst_1547_, v_toBind_1548_, v___x_6207__boxed_1573_, v___x_1550_, v___x_1551_, v___x_1552_, v_stx_1553_, v___f_1554_, v___x_1555_, v___x_1556_, v___f_1557_, v___f_1558_, v_inst_1559_, v___x_1560_, v___x_1561_, v___x_1562_, v___x_1563_, v___x_1564_, v___x_1565_, v___f_1566_, v___x_1567_, v___x_1568_, v___x_1569_, v___f_1570_, v___f_1571_, v_ref_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v_toPure_1575_, lean_object* v_____x_1576_){
_start:
{
lean_object* v_fst_1577_; lean_object* v___x_1578_; 
v_fst_1577_ = lean_ctor_get(v_____x_1576_, 0);
lean_inc(v_fst_1577_);
lean_dec_ref(v_____x_1576_);
v___x_1578_ = lean_apply_2(v_toPure_1575_, lean_box(0), v_fst_1577_);
return v___x_1578_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object* v_toApplicative_1588_, lean_object* v_stx_1589_, lean_object* v_____do__lift_1590_, lean_object* v_inst_1591_, lean_object* v_toBind_1592_, lean_object* v___f_1593_, lean_object* v___x_1594_, lean_object* v___x_1595_, lean_object* v___f_1596_, lean_object* v___f_1597_, lean_object* v_inst_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v___f_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___f_1609_, lean_object* v___f_1610_, lean_object* v_____do__lift_1611_){
_start:
{
lean_object* v_toPure_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v_toPure_1612_ = lean_ctor_get(v_toApplicative_1588_, 1);
lean_inc_n(v_toPure_1612_, 2);
lean_dec_ref(v_toApplicative_1588_);
v___x_1613_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0));
v___x_1614_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1));
v___x_1615_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2));
v___x_1616_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4));
lean_inc(v_stx_1589_);
v___x_1617_ = l_Lean_Syntax_isOfKind(v_stx_1589_, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_____do__lift_1590_);
lean_ctor_set(v___x_1618_, 1, v_____do__lift_1611_);
v___x_1619_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1619_, 0, lean_box(0));
lean_closure_set(v___x_1619_, 1, lean_box(0));
lean_closure_set(v___x_1619_, 2, v___x_1618_);
lean_inc(v_inst_1591_);
v___x_1620_ = lean_apply_2(v_inst_1591_, lean_box(0), v___x_1619_);
v___x_1621_ = lean_box(v___x_1617_);
lean_inc_n(v_toBind_1592_, 2);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed), 27, 26);
lean_closure_set(v___f_1622_, 0, v_toPure_1612_);
lean_closure_set(v___f_1622_, 1, v_inst_1591_);
lean_closure_set(v___f_1622_, 2, v_toBind_1592_);
lean_closure_set(v___f_1622_, 3, v___x_1621_);
lean_closure_set(v___f_1622_, 4, v___x_1613_);
lean_closure_set(v___f_1622_, 5, v___x_1614_);
lean_closure_set(v___f_1622_, 6, v___x_1615_);
lean_closure_set(v___f_1622_, 7, v_stx_1589_);
lean_closure_set(v___f_1622_, 8, v___f_1593_);
lean_closure_set(v___f_1622_, 9, v___x_1594_);
lean_closure_set(v___f_1622_, 10, v___x_1595_);
lean_closure_set(v___f_1622_, 11, v___f_1596_);
lean_closure_set(v___f_1622_, 12, v___f_1597_);
lean_closure_set(v___f_1622_, 13, v_inst_1598_);
lean_closure_set(v___f_1622_, 14, v___x_1599_);
lean_closure_set(v___f_1622_, 15, v___x_1600_);
lean_closure_set(v___f_1622_, 16, v___x_1601_);
lean_closure_set(v___f_1622_, 17, v___x_1602_);
lean_closure_set(v___f_1622_, 18, v___x_1603_);
lean_closure_set(v___f_1622_, 19, v___x_1604_);
lean_closure_set(v___f_1622_, 20, v___f_1605_);
lean_closure_set(v___f_1622_, 21, v___x_1606_);
lean_closure_set(v___f_1622_, 22, v___x_1607_);
lean_closure_set(v___f_1622_, 23, v___x_1608_);
lean_closure_set(v___f_1622_, 24, v___f_1609_);
lean_closure_set(v___f_1622_, 25, v___f_1610_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37), 2, 1);
lean_closure_set(v___f_1623_, 0, v_toPure_1612_);
v___x_1624_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1620_, v___f_1622_);
v___x_1625_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1624_, v___f_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_1588_ = stack[0].m_obj;
lean_object* v_stx_1589_ = stack[1].m_obj;
lean_object* v_____do__lift_1590_ = stack[2].m_obj;
lean_object* v_inst_1591_ = stack[3].m_obj;
lean_object* v_toBind_1592_ = stack[4].m_obj;
lean_object* v___f_1593_ = stack[5].m_obj;
lean_object* v___x_1594_ = stack[6].m_obj;
lean_object* v___x_1595_ = stack[7].m_obj;
lean_object* v___f_1596_ = stack[8].m_obj;
lean_object* v___f_1597_ = stack[9].m_obj;
lean_object* v_inst_1598_ = stack[10].m_obj;
lean_object* v___x_1599_ = stack[11].m_obj;
lean_object* v___x_1600_ = stack[12].m_obj;
lean_object* v___x_1601_ = stack[13].m_obj;
lean_object* v___x_1602_ = stack[14].m_obj;
lean_object* v___x_1603_ = stack[15].m_obj;
lean_object* v___x_1604_ = stack[16].m_obj;
lean_object* v___f_1605_ = stack[17].m_obj;
lean_object* v___x_1606_ = stack[18].m_obj;
lean_object* v___x_1607_ = stack[19].m_obj;
lean_object* v___x_1608_ = stack[20].m_obj;
lean_object* v___f_1609_ = stack[21].m_obj;
lean_object* v___f_1610_ = stack[22].m_obj;
lean_object* v_____do__lift_1611_ = stack[23].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(v_toApplicative_1588_, v_stx_1589_, v_____do__lift_1590_, v_inst_1591_, v_toBind_1592_, v___f_1593_, v___x_1594_, v___x_1595_, v___f_1596_, v___f_1597_, v_inst_1598_, v___x_1599_, v___x_1600_, v___x_1601_, v___x_1602_, v___x_1603_, v___x_1604_, v___f_1605_, v___x_1606_, v___x_1607_, v___x_1608_, v___f_1609_, v___f_1610_, v_____do__lift_1611_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toApplicative_1627_ = _args[0];
lean_object* v_stx_1628_ = _args[1];
lean_object* v_____do__lift_1629_ = _args[2];
lean_object* v_inst_1630_ = _args[3];
lean_object* v_toBind_1631_ = _args[4];
lean_object* v___f_1632_ = _args[5];
lean_object* v___x_1633_ = _args[6];
lean_object* v___x_1634_ = _args[7];
lean_object* v___f_1635_ = _args[8];
lean_object* v___f_1636_ = _args[9];
lean_object* v_inst_1637_ = _args[10];
lean_object* v___x_1638_ = _args[11];
lean_object* v___x_1639_ = _args[12];
lean_object* v___x_1640_ = _args[13];
lean_object* v___x_1641_ = _args[14];
lean_object* v___x_1642_ = _args[15];
lean_object* v___x_1643_ = _args[16];
lean_object* v___f_1644_ = _args[17];
lean_object* v___x_1645_ = _args[18];
lean_object* v___x_1646_ = _args[19];
lean_object* v___x_1647_ = _args[20];
lean_object* v___f_1648_ = _args[21];
lean_object* v___f_1649_ = _args[22];
lean_object* v_____do__lift_1650_ = _args[23];
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(v_toApplicative_1627_, v_stx_1628_, v_____do__lift_1629_, v_inst_1630_, v_toBind_1631_, v___f_1632_, v___x_1633_, v___x_1634_, v___f_1635_, v___f_1636_, v_inst_1637_, v___x_1638_, v___x_1639_, v___x_1640_, v___x_1641_, v___x_1642_, v___x_1643_, v___f_1644_, v___x_1645_, v___x_1646_, v___x_1647_, v___f_1648_, v___f_1649_, v_____do__lift_1650_);
return v_res_1651_;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object* v_toApplicative_1652_, lean_object* v_stx_1653_, lean_object* v_inst_1654_, lean_object* v_toBind_1655_, lean_object* v___f_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v___f_1659_, lean_object* v___f_1660_, lean_object* v_inst_1661_, lean_object* v___x_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v___x_1665_, lean_object* v___x_1666_, lean_object* v___x_1667_, lean_object* v___f_1668_, lean_object* v___x_1669_, lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v___f_1672_, lean_object* v___f_1673_, lean_object* v_getCurrNamespace_1674_, lean_object* v_____do__lift_1675_){
_start:
{
lean_object* v___f_1676_; lean_object* v___x_1677_; 
lean_inc(v_toBind_1655_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed), 24, 23);
lean_closure_set(v___f_1676_, 0, v_toApplicative_1652_);
lean_closure_set(v___f_1676_, 1, v_stx_1653_);
lean_closure_set(v___f_1676_, 2, v_____do__lift_1675_);
lean_closure_set(v___f_1676_, 3, v_inst_1654_);
lean_closure_set(v___f_1676_, 4, v_toBind_1655_);
lean_closure_set(v___f_1676_, 5, v___f_1656_);
lean_closure_set(v___f_1676_, 6, v___x_1657_);
lean_closure_set(v___f_1676_, 7, v___x_1658_);
lean_closure_set(v___f_1676_, 8, v___f_1659_);
lean_closure_set(v___f_1676_, 9, v___f_1660_);
lean_closure_set(v___f_1676_, 10, v_inst_1661_);
lean_closure_set(v___f_1676_, 11, v___x_1662_);
lean_closure_set(v___f_1676_, 12, v___x_1663_);
lean_closure_set(v___f_1676_, 13, v___x_1664_);
lean_closure_set(v___f_1676_, 14, v___x_1665_);
lean_closure_set(v___f_1676_, 15, v___x_1666_);
lean_closure_set(v___f_1676_, 16, v___x_1667_);
lean_closure_set(v___f_1676_, 17, v___f_1668_);
lean_closure_set(v___f_1676_, 18, v___x_1669_);
lean_closure_set(v___f_1676_, 19, v___x_1670_);
lean_closure_set(v___f_1676_, 20, v___x_1671_);
lean_closure_set(v___f_1676_, 21, v___f_1672_);
lean_closure_set(v___f_1676_, 22, v___f_1673_);
v___x_1677_ = lean_apply_4(v_toBind_1655_, lean_box(0), lean_box(0), v_getCurrNamespace_1674_, v___f_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT void l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_1652_ = stack[0].m_obj;
lean_object* v_stx_1653_ = stack[1].m_obj;
lean_object* v_inst_1654_ = stack[2].m_obj;
lean_object* v_toBind_1655_ = stack[3].m_obj;
lean_object* v___f_1656_ = stack[4].m_obj;
lean_object* v___x_1657_ = stack[5].m_obj;
lean_object* v___x_1658_ = stack[6].m_obj;
lean_object* v___f_1659_ = stack[7].m_obj;
lean_object* v___f_1660_ = stack[8].m_obj;
lean_object* v_inst_1661_ = stack[9].m_obj;
lean_object* v___x_1662_ = stack[10].m_obj;
lean_object* v___x_1663_ = stack[11].m_obj;
lean_object* v___x_1664_ = stack[12].m_obj;
lean_object* v___x_1665_ = stack[13].m_obj;
lean_object* v___x_1666_ = stack[14].m_obj;
lean_object* v___x_1667_ = stack[15].m_obj;
lean_object* v___f_1668_ = stack[16].m_obj;
lean_object* v___x_1669_ = stack[17].m_obj;
lean_object* v___x_1670_ = stack[18].m_obj;
lean_object* v___x_1671_ = stack[19].m_obj;
lean_object* v___f_1672_ = stack[20].m_obj;
lean_object* v___f_1673_ = stack[21].m_obj;
lean_object* v_getCurrNamespace_1674_ = stack[22].m_obj;
lean_object* v_____do__lift_1675_ = stack[23].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(v_toApplicative_1652_, v_stx_1653_, v_inst_1654_, v_toBind_1655_, v___f_1656_, v___x_1657_, v___x_1658_, v___f_1659_, v___f_1660_, v_inst_1661_, v___x_1662_, v___x_1663_, v___x_1664_, v___x_1665_, v___x_1666_, v___x_1667_, v___f_1668_, v___x_1669_, v___x_1670_, v___x_1671_, v___f_1672_, v___f_1673_, v_getCurrNamespace_1674_, v_____do__lift_1675_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toApplicative_1679_ = _args[0];
lean_object* v_stx_1680_ = _args[1];
lean_object* v_inst_1681_ = _args[2];
lean_object* v_toBind_1682_ = _args[3];
lean_object* v___f_1683_ = _args[4];
lean_object* v___x_1684_ = _args[5];
lean_object* v___x_1685_ = _args[6];
lean_object* v___f_1686_ = _args[7];
lean_object* v___f_1687_ = _args[8];
lean_object* v_inst_1688_ = _args[9];
lean_object* v___x_1689_ = _args[10];
lean_object* v___x_1690_ = _args[11];
lean_object* v___x_1691_ = _args[12];
lean_object* v___x_1692_ = _args[13];
lean_object* v___x_1693_ = _args[14];
lean_object* v___x_1694_ = _args[15];
lean_object* v___f_1695_ = _args[16];
lean_object* v___x_1696_ = _args[17];
lean_object* v___x_1697_ = _args[18];
lean_object* v___x_1698_ = _args[19];
lean_object* v___f_1699_ = _args[20];
lean_object* v___f_1700_ = _args[21];
lean_object* v_getCurrNamespace_1701_ = _args[22];
lean_object* v_____do__lift_1702_ = _args[23];
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(v_toApplicative_1679_, v_stx_1680_, v_inst_1681_, v_toBind_1682_, v___f_1683_, v___x_1684_, v___x_1685_, v___f_1686_, v___f_1687_, v_inst_1688_, v___x_1689_, v___x_1690_, v___x_1691_, v___x_1692_, v___x_1693_, v___x_1694_, v___f_1695_, v___x_1696_, v___x_1697_, v___x_1698_, v___f_1699_, v___f_1700_, v_getCurrNamespace_1701_, v_____do__lift_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_stx_1738_){
_start:
{
lean_object* v___x_1739_; lean_object* v_toApplicative_1740_; lean_object* v_toBind_1741_; lean_object* v_getCurrNamespace_1742_; lean_object* v_getOpenDecls_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1782_; 
v___x_1739_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9));
v_toApplicative_1740_ = lean_ctor_get(v_inst_1728_, 0);
lean_inc_ref(v_toApplicative_1740_);
v_toBind_1741_ = lean_ctor_get(v_inst_1728_, 1);
lean_inc(v_toBind_1741_);
v_getCurrNamespace_1742_ = lean_ctor_get(v_inst_1736_, 0);
v_getOpenDecls_1743_ = lean_ctor_get(v_inst_1736_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_inst_1736_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1745_ = v_inst_1736_;
v_isShared_1746_ = v_isSharedCheck_1782_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_getOpenDecls_1743_);
lean_inc(v_getCurrNamespace_1742_);
lean_dec(v_inst_1736_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1782_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___f_1748_; lean_object* v___f_1749_; lean_object* v___x_1751_; 
lean_inc_ref(v_inst_1728_);
v___x_1747_ = l_StateRefT_x27_instMonad___redArg(v_inst_1728_);
lean_inc_ref(v_inst_1730_);
v___f_1748_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1748_, 0, v_inst_1730_);
v___f_1749_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1749_, 0, v_inst_1730_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___f_1749_);
lean_ctor_set(v___x_1745_, 0, v___f_1748_);
v___x_1751_ = v___x_1745_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___f_1748_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___f_1749_);
v___x_1751_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v_getEnv_1753_; lean_object* v_modifyEnv_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1780_; 
lean_inc(v_inst_1733_);
v___x_1752_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1728_, v_inst_1733_);
v_getEnv_1753_ = lean_ctor_get(v_inst_1729_, 0);
v_modifyEnv_1754_ = lean_ctor_get(v_inst_1729_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_inst_1729_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1756_ = v_inst_1729_;
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_modifyEnv_1754_);
lean_inc(v_getEnv_1753_);
lean_dec(v_inst_1729_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1780_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___f_1758_; lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_inc_ref(v_toApplicative_1740_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1758_, 0, v_toApplicative_1740_);
lean_inc(v_toBind_1741_);
lean_inc(v_inst_1733_);
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1759_, 0, v_inst_1733_);
lean_closure_set(v___f_1759_, 1, v_toBind_1741_);
lean_closure_set(v___f_1759_, 2, v___f_1758_);
v___f_1760_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10));
v___f_1761_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11));
v___f_1762_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12));
v___x_1763_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1764_, 0, v_modifyEnv_1754_);
lean_closure_set(v___f_1764_, 1, v___x_1763_);
v___x_1765_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1765_, 0, lean_box(0));
lean_closure_set(v___x_1765_, 1, lean_box(0));
lean_closure_set(v___x_1765_, 2, lean_box(0));
lean_closure_set(v___x_1765_, 3, lean_box(0));
lean_closure_set(v___x_1765_, 4, v_getEnv_1753_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v___f_1764_);
lean_ctor_set(v___x_1756_, 0, v___x_1765_);
v___x_1767_ = v___x_1756_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___f_1764_);
v___x_1767_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; lean_object* v___x_1778_; 
v___x_1768_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_1769_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1763_, v___x_1768_, v_inst_1731_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1770_, 0, v_inst_1732_);
lean_closure_set(v___f_1770_, 1, v___x_1763_);
lean_inc_ref(v___x_1747_);
lean_inc_ref(v___f_1770_);
v___x_1771_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1770_, v___x_1747_);
lean_inc(v___x_1771_);
lean_inc_ref(v___x_1769_);
lean_inc_ref(v___x_1751_);
v___x_1772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1751_);
lean_ctor_set(v___x_1772_, 1, v___x_1769_);
lean_ctor_set(v___x_1772_, 2, v___x_1771_);
v___x_1773_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_1763_, v_inst_1735_);
v___x_1774_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1763_, v_inst_1734_);
lean_inc_ref(v_inst_1737_);
v___x_1775_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_1763_, v_inst_1737_);
lean_inc(v_inst_1733_);
v___f_1776_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1776_, 0, v_inst_1733_);
lean_closure_set(v___f_1776_, 1, v___x_1763_);
lean_inc(v_toBind_1741_);
v___f_1777_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed), 24, 23);
lean_closure_set(v___f_1777_, 0, v_toApplicative_1740_);
lean_closure_set(v___f_1777_, 1, v_stx_1738_);
lean_closure_set(v___f_1777_, 2, v_inst_1733_);
lean_closure_set(v___f_1777_, 3, v_toBind_1741_);
lean_closure_set(v___f_1777_, 4, v___f_1759_);
lean_closure_set(v___f_1777_, 5, v___x_1751_);
lean_closure_set(v___f_1777_, 6, v___x_1739_);
lean_closure_set(v___f_1777_, 7, v___f_1762_);
lean_closure_set(v___f_1777_, 8, v___f_1761_);
lean_closure_set(v___f_1777_, 9, v_inst_1737_);
lean_closure_set(v___f_1777_, 10, v___x_1747_);
lean_closure_set(v___f_1777_, 11, v___x_1775_);
lean_closure_set(v___f_1777_, 12, v___x_1767_);
lean_closure_set(v___f_1777_, 13, v___x_1772_);
lean_closure_set(v___f_1777_, 14, v___x_1769_);
lean_closure_set(v___f_1777_, 15, v___x_1771_);
lean_closure_set(v___f_1777_, 16, v___f_1770_);
lean_closure_set(v___f_1777_, 17, v___x_1774_);
lean_closure_set(v___f_1777_, 18, v___x_1773_);
lean_closure_set(v___f_1777_, 19, v___x_1752_);
lean_closure_set(v___f_1777_, 20, v___f_1760_);
lean_closure_set(v___f_1777_, 21, v___f_1776_);
lean_closure_set(v___f_1777_, 22, v_getCurrNamespace_1742_);
v___x_1778_ = lean_apply_4(v_toBind_1741_, lean_box(0), lean_box(0), v_getOpenDecls_1743_, v___f_1777_);
return v___x_1778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_stx_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1784_, v_inst_1785_, v_inst_1786_, v_inst_1787_, v_inst_1788_, v_inst_1789_, v_inst_1790_, v_inst_1791_, v_inst_1792_, v_inst_1793_, v_stx_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object* v_a_1796_, lean_object* v_toPure_1797_, lean_object* v_s_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_a_1796_);
lean_ctor_set(v___x_1799_, 1, v_s_1798_);
v___x_1800_ = lean_apply_2(v_toPure_1797_, lean_box(0), v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object* v_toPure_1801_, lean_object* v_ref_1802_, lean_object* v_inst_1803_, lean_object* v_toBind_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1806_, 0, v_a_1805_);
lean_closure_set(v___f_1806_, 1, v_toPure_1801_);
v___x_1807_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1807_, 0, lean_box(0));
lean_closure_set(v___x_1807_, 1, lean_box(0));
lean_closure_set(v___x_1807_, 2, v_ref_1802_);
v___x_1808_ = lean_apply_2(v_inst_1803_, lean_box(0), v___x_1807_);
v___x_1809_ = lean_apply_4(v_toBind_1804_, lean_box(0), lean_box(0), v___x_1808_, v___f_1806_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object* v_toPure_1810_, lean_object* v_inst_1811_, lean_object* v_toBind_1812_, lean_object* v___x_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v___x_1817_, lean_object* v___f_1818_, lean_object* v___x_1819_, lean_object* v___x_1820_, lean_object* v___x_1821_, lean_object* v_nss_1822_, lean_object* v_idStx_1823_, lean_object* v_ref_1824_){
_start:
{
lean_object* v___f_1825_; lean_object* v___x_107__overap_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc(v_toBind_1812_);
lean_inc(v_ref_1824_);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1825_, 0, v_toPure_1810_);
lean_closure_set(v___f_1825_, 1, v_ref_1824_);
lean_closure_set(v___f_1825_, 2, v_inst_1811_);
lean_closure_set(v___f_1825_, 3, v_toBind_1812_);
v___x_107__overap_1826_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1813_, v___x_1814_, v___x_1815_, v___x_1816_, v___x_1817_, v___f_1818_, v___x_1819_, v___x_1820_, v___x_1821_, v_nss_1822_, v_idStx_1823_);
v___x_1827_ = lean_apply_1(v___x_107__overap_1826_, v_ref_1824_);
v___x_1828_ = lean_apply_4(v_toBind_1812_, lean_box(0), lean_box(0), v___x_1827_, v___f_1825_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object* v_toPure_1829_, lean_object* v_____x_1830_){
_start:
{
lean_object* v_fst_1831_; lean_object* v___x_1832_; 
v_fst_1831_ = lean_ctor_get(v_____x_1830_, 0);
lean_inc(v_fst_1831_);
lean_dec_ref(v_____x_1830_);
v___x_1832_ = lean_apply_2(v_toPure_1829_, lean_box(0), v_fst_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object* v_toApplicative_1833_, lean_object* v_____do__lift_1834_, lean_object* v_inst_1835_, lean_object* v_toBind_1836_, lean_object* v___x_1837_, lean_object* v___x_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, lean_object* v___x_1841_, lean_object* v___f_1842_, lean_object* v___x_1843_, lean_object* v___x_1844_, lean_object* v___x_1845_, lean_object* v_nss_1846_, lean_object* v_idStx_1847_, lean_object* v_____do__lift_1848_){
_start:
{
lean_object* v_toPure_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_toPure_1849_ = lean_ctor_get(v_toApplicative_1833_, 1);
lean_inc_n(v_toPure_1849_, 2);
lean_dec_ref(v_toApplicative_1833_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_____do__lift_1834_);
lean_ctor_set(v___x_1850_, 1, v_____do__lift_1848_);
v___x_1851_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1851_, 0, lean_box(0));
lean_closure_set(v___x_1851_, 1, lean_box(0));
lean_closure_set(v___x_1851_, 2, v___x_1850_);
lean_inc(v_inst_1835_);
v___x_1852_ = lean_apply_2(v_inst_1835_, lean_box(0), v___x_1851_);
lean_inc_n(v_toBind_1836_, 2);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2), 15, 14);
lean_closure_set(v___f_1853_, 0, v_toPure_1849_);
lean_closure_set(v___f_1853_, 1, v_inst_1835_);
lean_closure_set(v___f_1853_, 2, v_toBind_1836_);
lean_closure_set(v___f_1853_, 3, v___x_1837_);
lean_closure_set(v___f_1853_, 4, v___x_1838_);
lean_closure_set(v___f_1853_, 5, v___x_1839_);
lean_closure_set(v___f_1853_, 6, v___x_1840_);
lean_closure_set(v___f_1853_, 7, v___x_1841_);
lean_closure_set(v___f_1853_, 8, v___f_1842_);
lean_closure_set(v___f_1853_, 9, v___x_1843_);
lean_closure_set(v___f_1853_, 10, v___x_1844_);
lean_closure_set(v___f_1853_, 11, v___x_1845_);
lean_closure_set(v___f_1853_, 12, v_nss_1846_);
lean_closure_set(v___f_1853_, 13, v_idStx_1847_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1854_, 0, v_toPure_1849_);
v___x_1855_ = lean_apply_4(v_toBind_1836_, lean_box(0), lean_box(0), v___x_1852_, v___f_1853_);
v___x_1856_ = lean_apply_4(v_toBind_1836_, lean_box(0), lean_box(0), v___x_1855_, v___f_1854_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object* v_toApplicative_1857_, lean_object* v_inst_1858_, lean_object* v_toBind_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v___x_1863_, lean_object* v___x_1864_, lean_object* v___f_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v_nss_1869_, lean_object* v_idStx_1870_, lean_object* v_getCurrNamespace_1871_, lean_object* v_____do__lift_1872_){
_start:
{
lean_object* v___f_1873_; lean_object* v___x_1874_; 
lean_inc(v_toBind_1859_);
v___f_1873_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4), 16, 15);
lean_closure_set(v___f_1873_, 0, v_toApplicative_1857_);
lean_closure_set(v___f_1873_, 1, v_____do__lift_1872_);
lean_closure_set(v___f_1873_, 2, v_inst_1858_);
lean_closure_set(v___f_1873_, 3, v_toBind_1859_);
lean_closure_set(v___f_1873_, 4, v___x_1860_);
lean_closure_set(v___f_1873_, 5, v___x_1861_);
lean_closure_set(v___f_1873_, 6, v___x_1862_);
lean_closure_set(v___f_1873_, 7, v___x_1863_);
lean_closure_set(v___f_1873_, 8, v___x_1864_);
lean_closure_set(v___f_1873_, 9, v___f_1865_);
lean_closure_set(v___f_1873_, 10, v___x_1866_);
lean_closure_set(v___f_1873_, 11, v___x_1867_);
lean_closure_set(v___f_1873_, 12, v___x_1868_);
lean_closure_set(v___f_1873_, 13, v_nss_1869_);
lean_closure_set(v___f_1873_, 14, v_idStx_1870_);
v___x_1874_ = lean_apply_4(v_toBind_1859_, lean_box(0), lean_box(0), v_getCurrNamespace_1871_, v___f_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_nss_1884_, lean_object* v_idStx_1885_){
_start:
{
lean_object* v_toApplicative_1886_; lean_object* v_toBind_1887_; lean_object* v_getCurrNamespace_1888_; lean_object* v_getOpenDecls_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1920_; 
v_toApplicative_1886_ = lean_ctor_get(v_inst_1875_, 0);
lean_inc_ref(v_toApplicative_1886_);
v_toBind_1887_ = lean_ctor_get(v_inst_1875_, 1);
lean_inc(v_toBind_1887_);
v_getCurrNamespace_1888_ = lean_ctor_get(v_inst_1883_, 0);
v_getOpenDecls_1889_ = lean_ctor_get(v_inst_1883_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_inst_1883_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1891_ = v_inst_1883_;
v_isShared_1892_ = v_isSharedCheck_1920_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_getOpenDecls_1889_);
lean_inc(v_getCurrNamespace_1888_);
lean_dec(v_inst_1883_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1920_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_getEnv_1894_; lean_object* v_modifyEnv_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1919_; 
lean_inc_ref(v_inst_1875_);
v___x_1893_ = l_StateRefT_x27_instMonad___redArg(v_inst_1875_);
v_getEnv_1894_ = lean_ctor_get(v_inst_1876_, 0);
v_modifyEnv_1895_ = lean_ctor_get(v_inst_1876_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_inst_1876_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1897_ = v_inst_1876_;
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_modifyEnv_1895_);
lean_inc(v_getEnv_1894_);
lean_dec(v_inst_1876_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___f_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1900_, 0, v_modifyEnv_1895_);
lean_closure_set(v___f_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1901_, 0, lean_box(0));
lean_closure_set(v___x_1901_, 1, lean_box(0));
lean_closure_set(v___x_1901_, 2, lean_box(0));
lean_closure_set(v___x_1901_, 3, lean_box(0));
lean_closure_set(v___x_1901_, 4, v_getEnv_1894_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___f_1900_);
lean_ctor_set(v___x_1897_, 0, v___x_1901_);
v___x_1903_ = v___x_1897_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___f_1900_);
v___x_1903_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___f_1904_; lean_object* v___f_1905_; lean_object* v___x_1907_; 
lean_inc_ref(v_inst_1877_);
v___f_1904_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1904_, 0, v_inst_1877_);
v___f_1905_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1905_, 0, v_inst_1877_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v___f_1905_);
lean_ctor_set(v___x_1891_, 0, v___f_1904_);
v___x_1907_ = v___x_1891_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___f_1904_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___f_1905_);
v___x_1907_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; 
v___x_1908_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_1909_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1899_, v___x_1908_, v_inst_1878_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1910_, 0, v_inst_1879_);
lean_closure_set(v___f_1910_, 1, v___x_1899_);
lean_inc_ref(v___x_1893_);
lean_inc_ref(v___f_1910_);
v___x_1911_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1910_, v___x_1893_);
v___x_1912_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1899_, v_inst_1881_);
v___x_1913_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_1899_, v_inst_1882_);
lean_inc(v_inst_1880_);
v___x_1914_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1875_, v_inst_1880_);
lean_inc(v_toBind_1887_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5), 16, 15);
lean_closure_set(v___f_1915_, 0, v_toApplicative_1886_);
lean_closure_set(v___f_1915_, 1, v_inst_1880_);
lean_closure_set(v___f_1915_, 2, v_toBind_1887_);
lean_closure_set(v___f_1915_, 3, v___x_1893_);
lean_closure_set(v___f_1915_, 4, v___x_1903_);
lean_closure_set(v___f_1915_, 5, v___x_1907_);
lean_closure_set(v___f_1915_, 6, v___x_1909_);
lean_closure_set(v___f_1915_, 7, v___x_1911_);
lean_closure_set(v___f_1915_, 8, v___f_1910_);
lean_closure_set(v___f_1915_, 9, v___x_1912_);
lean_closure_set(v___f_1915_, 10, v___x_1913_);
lean_closure_set(v___f_1915_, 11, v___x_1914_);
lean_closure_set(v___f_1915_, 12, v_nss_1884_);
lean_closure_set(v___f_1915_, 13, v_idStx_1885_);
lean_closure_set(v___f_1915_, 14, v_getCurrNamespace_1888_);
v___x_1916_ = lean_apply_4(v_toBind_1887_, lean_box(0), lean_box(0), v_getOpenDecls_1889_, v___f_1915_);
return v___x_1916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object* v_m_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_nss_1931_, lean_object* v_idStx_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(v_inst_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_inst_1926_, v_inst_1927_, v_inst_1928_, v_inst_1929_, v_inst_1930_, v_nss_1931_, v_idStx_1932_);
return v___x_1933_;
}
}
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Open(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_AmbiguousOpen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Open(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Open(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_AmbiguousOpen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Open(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Open(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Open(builtin);
}
#ifdef __cplusplus
}
#endif
