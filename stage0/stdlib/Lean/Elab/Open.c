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
lean_dec(v_inst_51_);
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
lean_object* v___x_3554__overap_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_3554__overap_496_ = l_Lean_Elab_addConstInfo___redArg(v___x_485_, v___x_486_, v___x_487_, v___x_488_, v_snd_489_, v_a_490_, v___x_491_);
lean_inc(v___y_492_);
v___x_497_ = lean_apply_1(v___x_3554__overap_496_, v___y_492_);
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
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_3569__overap_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
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
v___x_3569__overap_528_ = l_Lean_Elab_addConstInfo___redArg(v___x_514_, v___x_515_, v___x_516_, v___x_517_, v_fst_522_, v_a_519_, v___x_526_);
v___x_529_ = lean_apply_1(v___x_3569__overap_528_, v___y_513_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v_inst_577_, lean_object* v_inst_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___f_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___f_600_; lean_object* v___x_3607__overap_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
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
v___x_3607__overap_601_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_582_, v___x_584_, v___x_586_, v___x_587_, v___x_588_, v___f_589_, v___x_590_, v___x_591_, v___x_592_, v_a_593_, v_fst_598_);
v___x_602_ = lean_apply_1(v___x_3607__overap_601_, v___y_597_);
v___x_603_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_602_, v___f_600_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object** _args){
lean_object* v_inst_604_ = _args[0];
lean_object* v_inst_605_ = _args[1];
lean_object* v_toBind_606_ = _args[2];
lean_object* v___f_607_ = _args[3];
lean_object* v___x_608_ = _args[4];
lean_object* v___x_609_ = _args[5];
lean_object* v___x_610_ = _args[6];
lean_object* v___x_611_ = _args[7];
lean_object* v___x_612_ = _args[8];
lean_object* v___x_613_ = _args[9];
lean_object* v___x_614_ = _args[10];
lean_object* v___x_615_ = _args[11];
lean_object* v___f_616_ = _args[12];
lean_object* v___x_617_ = _args[13];
lean_object* v___x_618_ = _args[14];
lean_object* v___x_619_ = _args[15];
lean_object* v_a_620_ = _args[16];
lean_object* v_a_621_ = _args[17];
lean_object* v_x_622_ = _args[18];
lean_object* v___y_623_ = _args[19];
lean_object* v___y_624_ = _args[20];
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v_inst_604_, v_inst_605_, v_toBind_606_, v___f_607_, v___x_608_, v___x_609_, v___x_610_, v___x_611_, v___x_612_, v___x_613_, v___x_614_, v___x_615_, v___f_616_, v___x_617_, v___x_618_, v___x_619_, v_a_620_, v_a_621_, v_x_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_froms_626_, lean_object* v_tos_627_, lean_object* v_toPure_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_toBind_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v___f_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v_a_643_, size_t v___x_644_, lean_object* v_ref_645_, lean_object* v___f_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___f_651_; size_t v_sz_652_; lean_object* v___x_3628__overap_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_648_ = l_Array_zip___redArg(v_froms_626_, v_tos_627_);
v___x_649_ = lean_box(0);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_650_, 0, v___x_649_);
lean_closure_set(v___f_650_, 1, v_toPure_628_);
lean_inc_ref(v___x_632_);
lean_inc(v_toBind_631_);
v___f_651_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 21, 17);
lean_closure_set(v___f_651_, 0, v_inst_629_);
lean_closure_set(v___f_651_, 1, v_inst_630_);
lean_closure_set(v___f_651_, 2, v_toBind_631_);
lean_closure_set(v___f_651_, 3, v___f_650_);
lean_closure_set(v___f_651_, 4, v___x_649_);
lean_closure_set(v___f_651_, 5, v___x_632_);
lean_closure_set(v___f_651_, 6, v___x_633_);
lean_closure_set(v___f_651_, 7, v___x_634_);
lean_closure_set(v___f_651_, 8, v___x_635_);
lean_closure_set(v___f_651_, 9, v___x_636_);
lean_closure_set(v___f_651_, 10, v___x_637_);
lean_closure_set(v___f_651_, 11, v___x_638_);
lean_closure_set(v___f_651_, 12, v___f_639_);
lean_closure_set(v___f_651_, 13, v___x_640_);
lean_closure_set(v___f_651_, 14, v___x_641_);
lean_closure_set(v___f_651_, 15, v___x_642_);
lean_closure_set(v___f_651_, 16, v_a_643_);
v_sz_652_ = lean_array_size(v___x_648_);
v___x_3628__overap_653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_632_, v___x_648_, v___f_651_, v_sz_652_, v___x_644_, v___x_649_);
v___x_654_ = lean_apply_1(v___x_3628__overap_653_, v_ref_645_);
v___x_655_ = lean_apply_4(v_toBind_631_, lean_box(0), lean_box(0), v___x_654_, v___f_646_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_froms_656_ = _args[0];
lean_object* v_tos_657_ = _args[1];
lean_object* v_toPure_658_ = _args[2];
lean_object* v_inst_659_ = _args[3];
lean_object* v_inst_660_ = _args[4];
lean_object* v_toBind_661_ = _args[5];
lean_object* v___x_662_ = _args[6];
lean_object* v___x_663_ = _args[7];
lean_object* v___x_664_ = _args[8];
lean_object* v___x_665_ = _args[9];
lean_object* v___x_666_ = _args[10];
lean_object* v___x_667_ = _args[11];
lean_object* v___x_668_ = _args[12];
lean_object* v___f_669_ = _args[13];
lean_object* v___x_670_ = _args[14];
lean_object* v___x_671_ = _args[15];
lean_object* v___x_672_ = _args[16];
lean_object* v_a_673_ = _args[17];
lean_object* v___x_674_ = _args[18];
lean_object* v_ref_675_ = _args[19];
lean_object* v___f_676_ = _args[20];
lean_object* v_a_677_ = _args[21];
_start:
{
size_t v___x_4494__boxed_678_; lean_object* v_res_679_; 
v___x_4494__boxed_678_ = lean_unbox_usize(v___x_674_);
lean_dec(v___x_674_);
v_res_679_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_656_, v_tos_657_, v_toPure_658_, v_inst_659_, v_inst_660_, v_toBind_661_, v___x_662_, v___x_663_, v___x_664_, v___x_665_, v___x_666_, v___x_667_, v___x_668_, v___f_669_, v___x_670_, v___x_671_, v___x_672_, v_a_673_, v___x_4494__boxed_678_, v_ref_675_, v___f_676_, v_a_677_);
lean_dec_ref(v_tos_657_);
lean_dec_ref(v_froms_656_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object* v_froms_680_, lean_object* v_tos_681_, lean_object* v_toPure_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_toBind_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v___x_688_, lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v___x_692_, lean_object* v___f_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___x_696_, size_t v___x_697_, lean_object* v_ref_698_, lean_object* v___f_699_, lean_object* v___x_700_, lean_object* v_nsStx_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_3648__overap_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = lean_box_usize(v___x_697_);
lean_inc(v_ref_698_);
lean_inc(v_a_702_);
lean_inc_ref(v___x_696_);
lean_inc(v___x_695_);
lean_inc_ref(v___x_694_);
lean_inc(v___f_693_);
lean_inc_ref(v___x_688_);
lean_inc_ref(v___x_686_);
lean_inc(v_toBind_685_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 22, 21);
lean_closure_set(v___f_704_, 0, v_froms_680_);
lean_closure_set(v___f_704_, 1, v_tos_681_);
lean_closure_set(v___f_704_, 2, v_toPure_682_);
lean_closure_set(v___f_704_, 3, v_inst_683_);
lean_closure_set(v___f_704_, 4, v_inst_684_);
lean_closure_set(v___f_704_, 5, v_toBind_685_);
lean_closure_set(v___f_704_, 6, v___x_686_);
lean_closure_set(v___f_704_, 7, v___x_687_);
lean_closure_set(v___f_704_, 8, v___x_688_);
lean_closure_set(v___f_704_, 9, v___x_689_);
lean_closure_set(v___f_704_, 10, v___x_690_);
lean_closure_set(v___f_704_, 11, v___x_691_);
lean_closure_set(v___f_704_, 12, v___x_692_);
lean_closure_set(v___f_704_, 13, v___f_693_);
lean_closure_set(v___f_704_, 14, v___x_694_);
lean_closure_set(v___f_704_, 15, v___x_695_);
lean_closure_set(v___f_704_, 16, v___x_696_);
lean_closure_set(v___f_704_, 17, v_a_702_);
lean_closure_set(v___f_704_, 18, v___x_703_);
lean_closure_set(v___f_704_, 19, v_ref_698_);
lean_closure_set(v___f_704_, 20, v___f_699_);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v_a_702_);
lean_ctor_set(v___x_705_, 1, v___x_700_);
v___x_3648__overap_706_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_686_, v___x_688_, v___x_695_, v___x_694_, v___f_693_, v___x_696_, v_nsStx_701_, v___x_705_);
v___x_707_ = lean_apply_1(v___x_3648__overap_706_, v_ref_698_);
v___x_708_ = lean_apply_4(v_toBind_685_, lean_box(0), lean_box(0), v___x_707_, v___f_704_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_froms_709_ = _args[0];
lean_object* v_tos_710_ = _args[1];
lean_object* v_toPure_711_ = _args[2];
lean_object* v_inst_712_ = _args[3];
lean_object* v_inst_713_ = _args[4];
lean_object* v_toBind_714_ = _args[5];
lean_object* v___x_715_ = _args[6];
lean_object* v___x_716_ = _args[7];
lean_object* v___x_717_ = _args[8];
lean_object* v___x_718_ = _args[9];
lean_object* v___x_719_ = _args[10];
lean_object* v___x_720_ = _args[11];
lean_object* v___x_721_ = _args[12];
lean_object* v___f_722_ = _args[13];
lean_object* v___x_723_ = _args[14];
lean_object* v___x_724_ = _args[15];
lean_object* v___x_725_ = _args[16];
lean_object* v___x_726_ = _args[17];
lean_object* v_ref_727_ = _args[18];
lean_object* v___f_728_ = _args[19];
lean_object* v___x_729_ = _args[20];
lean_object* v_nsStx_730_ = _args[21];
lean_object* v_a_731_ = _args[22];
_start:
{
size_t v___x_4551__boxed_732_; lean_object* v_res_733_; 
v___x_4551__boxed_732_ = lean_unbox_usize(v___x_726_);
lean_dec(v___x_726_);
v_res_733_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v_froms_709_, v_tos_710_, v_toPure_711_, v_inst_712_, v_inst_713_, v_toBind_714_, v___x_715_, v___x_716_, v___x_717_, v___x_718_, v___x_719_, v___x_720_, v___x_721_, v___f_722_, v___x_723_, v___x_724_, v___x_725_, v___x_4551__boxed_732_, v_ref_727_, v___f_728_, v___x_729_, v_nsStx_730_, v_a_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(uint8_t v___x_734_, uint8_t v___x_735_, lean_object* v_x1_736_, lean_object* v_x2_737_){
_start:
{
lean_object* v_fst_738_; uint8_t v___x_739_; 
v_fst_738_ = lean_ctor_get(v_x1_736_, 0);
v___x_739_ = lean_unbox(v_fst_738_);
if (v___x_739_ == 0)
{
lean_object* v_snd_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_x2_737_);
v_snd_740_ = lean_ctor_get(v_x1_736_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x1_736_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v_x1_736_, 0);
lean_dec(v_unused_749_);
v___x_742_ = v_x1_736_;
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_snd_740_);
lean_dec(v_x1_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_748_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_box(v___x_734_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_740_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_759_; 
v_snd_750_ = lean_ctor_get(v_x1_736_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_x1_736_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_x1_736_, 0);
lean_dec(v_unused_760_);
v___x_752_ = v_x1_736_;
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_dec(v_x1_736_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_754_ = lean_array_push(v_snd_750_, v_x2_737_);
v___x_755_ = lean_box(v___x_735_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_754_);
lean_ctor_set(v___x_752_, 0, v___x_755_);
v___x_757_ = v___x_752_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_754_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_x1_763_, lean_object* v_x2_764_){
_start:
{
uint8_t v___x_4596__boxed_765_; uint8_t v___x_4597__boxed_766_; lean_object* v_res_767_; 
v___x_4596__boxed_765_ = lean_unbox(v___x_761_);
v___x_4597__boxed_766_ = lean_unbox(v___x_762_);
v_res_767_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v___x_4596__boxed_765_, v___x_4597__boxed_766_, v_x1_763_, v_x2_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v_ids_768_, lean_object* v___f_769_, lean_object* v_a_770_, lean_object* v_inst_771_, lean_object* v_ref_772_, lean_object* v_toBind_773_, lean_object* v___f_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_776_; size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_776_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_777_ = lean_array_size(v_ids_768_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_776_, v___f_769_, v_sz_777_, v___x_778_, v_ids_768_);
v___x_780_ = lean_array_to_list(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_a_770_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_771_, v___x_781_, v_ref_772_);
v___x_783_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_782_, v___f_774_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v_ids_784_, lean_object* v___f_785_, lean_object* v_a_786_, lean_object* v_inst_787_, lean_object* v_ref_788_, lean_object* v_toBind_789_, lean_object* v___f_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v_ids_784_, v___f_785_, v_a_786_, v_inst_787_, v_ref_788_, v_toBind_789_, v___f_790_, v_a_791_);
lean_dec(v_ref_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v___x_793_, lean_object* v_toPure_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v___y_801_, lean_object* v_toBind_802_, lean_object* v___f_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_enabled_805_; 
v_enabled_805_ = lean_ctor_get_uint8(v_a_804_, sizeof(void*)*3);
if (v_enabled_805_ == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v___f_803_);
lean_dec(v_toBind_802_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v___x_798_);
lean_dec_ref(v___x_797_);
lean_dec_ref(v___x_796_);
lean_dec_ref(v___x_795_);
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_793_);
v___x_807_ = lean_apply_2(v_toPure_794_, lean_box(0), v___x_806_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_3693__overap_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_toPure_794_);
v___x_808_ = lean_box(0);
v___x_3693__overap_809_ = l_Lean_Elab_addConstInfo___redArg(v___x_795_, v___x_796_, v___x_797_, v___x_798_, v_a_799_, v_a_800_, v___x_808_);
lean_inc(v___y_801_);
v___x_810_ = lean_apply_1(v___x_3693__overap_809_, v___y_801_);
v___x_811_ = lean_apply_4(v_toBind_802_, lean_box(0), lean_box(0), v___x_810_, v___f_803_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object* v___x_812_, lean_object* v_toPure_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v___x_816_, lean_object* v___x_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v___y_820_, lean_object* v_toBind_821_, lean_object* v___f_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v___x_812_, v_toPure_813_, v___x_814_, v___x_815_, v___x_816_, v___x_817_, v_a_818_, v_a_819_, v___y_820_, v_toBind_821_, v___f_822_, v_a_823_);
lean_dec_ref(v_a_823_);
lean_dec(v___y_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object* v_inst_825_, lean_object* v___x_826_, lean_object* v_toPure_827_, lean_object* v___x_828_, lean_object* v___x_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v_a_832_, lean_object* v___y_833_, lean_object* v_toBind_834_, lean_object* v___f_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_getInfoState_837_; lean_object* v___f_838_; lean_object* v___x_839_; 
v_getInfoState_837_ = lean_ctor_get(v_inst_825_, 0);
lean_inc(v_getInfoState_837_);
lean_dec_ref(v_inst_825_);
lean_inc(v_toBind_834_);
lean_inc(v___y_833_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 12, 11);
lean_closure_set(v___f_838_, 0, v___x_826_);
lean_closure_set(v___f_838_, 1, v_toPure_827_);
lean_closure_set(v___f_838_, 2, v___x_828_);
lean_closure_set(v___f_838_, 3, v___x_829_);
lean_closure_set(v___f_838_, 4, v___x_830_);
lean_closure_set(v___f_838_, 5, v___x_831_);
lean_closure_set(v___f_838_, 6, v_a_832_);
lean_closure_set(v___f_838_, 7, v_a_836_);
lean_closure_set(v___f_838_, 8, v___y_833_);
lean_closure_set(v___f_838_, 9, v_toBind_834_);
lean_closure_set(v___f_838_, 10, v___f_835_);
v___x_839_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v_getInfoState_837_, v___f_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object* v_inst_840_, lean_object* v___x_841_, lean_object* v_toPure_842_, lean_object* v___x_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v___x_846_, lean_object* v_a_847_, lean_object* v___y_848_, lean_object* v_toBind_849_, lean_object* v___f_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(v_inst_840_, v___x_841_, v_toPure_842_, v___x_843_, v___x_844_, v___x_845_, v___x_846_, v_a_847_, v___y_848_, v_toBind_849_, v___f_850_, v_a_851_);
lean_dec(v___y_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v_inst_853_, lean_object* v___x_854_, lean_object* v_toPure_855_, lean_object* v___x_856_, lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v_toBind_860_, lean_object* v___f_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v___f_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_x_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___f_874_; lean_object* v___x_3723__overap_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc(v_toBind_860_);
lean_inc_n(v___y_873_, 2);
lean_inc(v_a_870_);
lean_inc_ref(v___x_858_);
lean_inc_ref(v___x_856_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_874_, 0, v_inst_853_);
lean_closure_set(v___f_874_, 1, v___x_854_);
lean_closure_set(v___f_874_, 2, v_toPure_855_);
lean_closure_set(v___f_874_, 3, v___x_856_);
lean_closure_set(v___f_874_, 4, v___x_857_);
lean_closure_set(v___f_874_, 5, v___x_858_);
lean_closure_set(v___f_874_, 6, v___x_859_);
lean_closure_set(v___f_874_, 7, v_a_870_);
lean_closure_set(v___f_874_, 8, v___y_873_);
lean_closure_set(v___f_874_, 9, v_toBind_860_);
lean_closure_set(v___f_874_, 10, v___f_861_);
v___x_3723__overap_875_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_856_, v___x_858_, v___x_862_, v___x_863_, v___x_864_, v___f_865_, v___x_866_, v___x_867_, v___x_868_, v_a_869_, v_a_870_);
v___x_876_ = lean_apply_1(v___x_3723__overap_875_, v___y_873_);
v___x_877_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_876_, v___f_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_inst_878_ = _args[0];
lean_object* v___x_879_ = _args[1];
lean_object* v_toPure_880_ = _args[2];
lean_object* v___x_881_ = _args[3];
lean_object* v___x_882_ = _args[4];
lean_object* v___x_883_ = _args[5];
lean_object* v___x_884_ = _args[6];
lean_object* v_toBind_885_ = _args[7];
lean_object* v___f_886_ = _args[8];
lean_object* v___x_887_ = _args[9];
lean_object* v___x_888_ = _args[10];
lean_object* v___x_889_ = _args[11];
lean_object* v___f_890_ = _args[12];
lean_object* v___x_891_ = _args[13];
lean_object* v___x_892_ = _args[14];
lean_object* v___x_893_ = _args[15];
lean_object* v_a_894_ = _args[16];
lean_object* v_a_895_ = _args[17];
lean_object* v_x_896_ = _args[18];
lean_object* v___y_897_ = _args[19];
lean_object* v___y_898_ = _args[20];
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v_inst_878_, v___x_879_, v_toPure_880_, v___x_881_, v___x_882_, v___x_883_, v___x_884_, v_toBind_885_, v___f_886_, v___x_887_, v___x_888_, v___x_889_, v___f_890_, v___x_891_, v___x_892_, v___x_893_, v_a_894_, v_a_895_, v_x_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_toPure_900_, lean_object* v_inst_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_toBind_906_, lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v___f_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_a_914_, lean_object* v_ids_915_, lean_object* v_ref_916_, lean_object* v___f_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___f_921_; size_t v_sz_922_; size_t v___x_923_; lean_object* v___x_3742__overap_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_919_ = lean_box(0);
lean_inc(v_toPure_900_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_920_, 0, v___x_919_);
lean_closure_set(v___f_920_, 1, v_toPure_900_);
lean_inc(v_toBind_906_);
lean_inc_ref(v___x_902_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 21, 17);
lean_closure_set(v___f_921_, 0, v_inst_901_);
lean_closure_set(v___f_921_, 1, v___x_919_);
lean_closure_set(v___f_921_, 2, v_toPure_900_);
lean_closure_set(v___f_921_, 3, v___x_902_);
lean_closure_set(v___f_921_, 4, v___x_903_);
lean_closure_set(v___f_921_, 5, v___x_904_);
lean_closure_set(v___f_921_, 6, v___x_905_);
lean_closure_set(v___f_921_, 7, v_toBind_906_);
lean_closure_set(v___f_921_, 8, v___f_920_);
lean_closure_set(v___f_921_, 9, v___x_907_);
lean_closure_set(v___f_921_, 10, v___x_908_);
lean_closure_set(v___f_921_, 11, v___x_909_);
lean_closure_set(v___f_921_, 12, v___f_910_);
lean_closure_set(v___f_921_, 13, v___x_911_);
lean_closure_set(v___f_921_, 14, v___x_912_);
lean_closure_set(v___f_921_, 15, v___x_913_);
lean_closure_set(v___f_921_, 16, v_a_914_);
v_sz_922_ = lean_array_size(v_ids_915_);
v___x_923_ = ((size_t)0ULL);
v___x_3742__overap_924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_902_, v_ids_915_, v___f_921_, v_sz_922_, v___x_923_, v___x_919_);
v___x_925_ = lean_apply_1(v___x_3742__overap_924_, v_ref_916_);
v___x_926_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_925_, v___f_917_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_toPure_927_ = _args[0];
lean_object* v_inst_928_ = _args[1];
lean_object* v___x_929_ = _args[2];
lean_object* v___x_930_ = _args[3];
lean_object* v___x_931_ = _args[4];
lean_object* v___x_932_ = _args[5];
lean_object* v_toBind_933_ = _args[6];
lean_object* v___x_934_ = _args[7];
lean_object* v___x_935_ = _args[8];
lean_object* v___x_936_ = _args[9];
lean_object* v___f_937_ = _args[10];
lean_object* v___x_938_ = _args[11];
lean_object* v___x_939_ = _args[12];
lean_object* v___x_940_ = _args[13];
lean_object* v_a_941_ = _args[14];
lean_object* v_ids_942_ = _args[15];
lean_object* v_ref_943_ = _args[16];
lean_object* v___f_944_ = _args[17];
lean_object* v_a_945_ = _args[18];
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_toPure_927_, v_inst_928_, v___x_929_, v___x_930_, v___x_931_, v___x_932_, v_toBind_933_, v___x_934_, v___x_935_, v___x_936_, v___f_937_, v___x_938_, v___x_939_, v___x_940_, v_a_941_, v_ids_942_, v_ref_943_, v___f_944_, v_a_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v___x_947_, lean_object* v___x_948_, lean_object* v___f_949_, lean_object* v_a_950_, lean_object* v_ref_951_, lean_object* v_toBind_952_, lean_object* v___f_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_3748__overap_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_3748__overap_955_ = l_Lean_activateScoped___redArg(v___x_947_, v___x_948_, v___f_949_, v_a_950_);
v___x_956_ = lean_apply_1(v___x_3748__overap_955_, v_ref_951_);
v___x_957_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v___x_956_, v___f_953_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v_ids_958_, lean_object* v___f_959_, lean_object* v_inst_960_, lean_object* v_ref_961_, lean_object* v_toBind_962_, lean_object* v___f_963_, lean_object* v_toPure_964_, lean_object* v_inst_965_, lean_object* v___x_966_, lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___f_973_, lean_object* v___x_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v___f_977_, lean_object* v___x_978_, lean_object* v_nsStx_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_3771__overap_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_inc_n(v_toBind_962_, 3);
lean_inc_n(v_ref_961_, 3);
lean_inc_n(v_a_980_, 3);
lean_inc_ref(v_ids_958_);
v___f_981_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 8, 7);
lean_closure_set(v___f_981_, 0, v_ids_958_);
lean_closure_set(v___f_981_, 1, v___f_959_);
lean_closure_set(v___f_981_, 2, v_a_980_);
lean_closure_set(v___f_981_, 3, v_inst_960_);
lean_closure_set(v___f_981_, 4, v_ref_961_);
lean_closure_set(v___f_981_, 5, v_toBind_962_);
lean_closure_set(v___f_981_, 6, v___f_963_);
lean_inc_ref(v___x_976_);
lean_inc(v___x_975_);
lean_inc_ref(v___x_974_);
lean_inc(v___f_973_);
lean_inc_ref_n(v___x_968_, 2);
lean_inc_ref_n(v___x_966_, 2);
v___f_982_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 19, 18);
lean_closure_set(v___f_982_, 0, v_toPure_964_);
lean_closure_set(v___f_982_, 1, v_inst_965_);
lean_closure_set(v___f_982_, 2, v___x_966_);
lean_closure_set(v___f_982_, 3, v___x_967_);
lean_closure_set(v___f_982_, 4, v___x_968_);
lean_closure_set(v___f_982_, 5, v___x_969_);
lean_closure_set(v___f_982_, 6, v_toBind_962_);
lean_closure_set(v___f_982_, 7, v___x_970_);
lean_closure_set(v___f_982_, 8, v___x_971_);
lean_closure_set(v___f_982_, 9, v___x_972_);
lean_closure_set(v___f_982_, 10, v___f_973_);
lean_closure_set(v___f_982_, 11, v___x_974_);
lean_closure_set(v___f_982_, 12, v___x_975_);
lean_closure_set(v___f_982_, 13, v___x_976_);
lean_closure_set(v___f_982_, 14, v_a_980_);
lean_closure_set(v___f_982_, 15, v_ids_958_);
lean_closure_set(v___f_982_, 16, v_ref_961_);
lean_closure_set(v___f_982_, 17, v___f_981_);
v___f_983_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24), 8, 7);
lean_closure_set(v___f_983_, 0, v___x_966_);
lean_closure_set(v___f_983_, 1, v___x_968_);
lean_closure_set(v___f_983_, 2, v___f_977_);
lean_closure_set(v___f_983_, 3, v_a_980_);
lean_closure_set(v___f_983_, 4, v_ref_961_);
lean_closure_set(v___f_983_, 5, v_toBind_962_);
lean_closure_set(v___f_983_, 6, v___f_982_);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v_a_980_);
lean_ctor_set(v___x_984_, 1, v___x_978_);
v___x_3771__overap_985_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_966_, v___x_968_, v___x_975_, v___x_974_, v___f_973_, v___x_976_, v_nsStx_979_, v___x_984_);
v___x_986_ = lean_apply_1(v___x_3771__overap_985_, v_ref_961_);
v___x_987_ = lean_apply_4(v_toBind_962_, lean_box(0), lean_box(0), v___x_986_, v___f_983_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object** _args){
lean_object* v_ids_988_ = _args[0];
lean_object* v___f_989_ = _args[1];
lean_object* v_inst_990_ = _args[2];
lean_object* v_ref_991_ = _args[3];
lean_object* v_toBind_992_ = _args[4];
lean_object* v___f_993_ = _args[5];
lean_object* v_toPure_994_ = _args[6];
lean_object* v_inst_995_ = _args[7];
lean_object* v___x_996_ = _args[8];
lean_object* v___x_997_ = _args[9];
lean_object* v___x_998_ = _args[10];
lean_object* v___x_999_ = _args[11];
lean_object* v___x_1000_ = _args[12];
lean_object* v___x_1001_ = _args[13];
lean_object* v___x_1002_ = _args[14];
lean_object* v___f_1003_ = _args[15];
lean_object* v___x_1004_ = _args[16];
lean_object* v___x_1005_ = _args[17];
lean_object* v___x_1006_ = _args[18];
lean_object* v___f_1007_ = _args[19];
lean_object* v___x_1008_ = _args[20];
lean_object* v_nsStx_1009_ = _args[21];
lean_object* v_a_1010_ = _args[22];
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v_ids_988_, v___f_989_, v_inst_990_, v_ref_991_, v_toBind_992_, v___f_993_, v_toPure_994_, v_inst_995_, v___x_996_, v___x_997_, v___x_998_, v___x_999_, v___x_1000_, v___x_1001_, v___x_1002_, v___f_1003_, v___x_1004_, v___x_1005_, v___x_1006_, v___f_1007_, v___x_1008_, v_nsStx_1009_, v_a_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_inst_1014_, lean_object* v_toBind_1015_, lean_object* v___f_1016_, lean_object* v_____r_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1019_ = l_Lean_TSyntax_getId(v_a_1012_);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_1013_);
v___x_1021_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1014_, v___x_1020_, v___y_1018_);
v___x_1022_ = lean_apply_4(v_toBind_1015_, lean_box(0), lean_box(0), v___x_1021_, v___f_1016_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_inst_1025_, lean_object* v_toBind_1026_, lean_object* v___f_1027_, lean_object* v_____r_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_a_1023_, v_a_1024_, v_inst_1025_, v_toBind_1026_, v___f_1027_, v_____r_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec(v_a_1023_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v___f_1031_, lean_object* v___x_1032_, lean_object* v___y_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_toBind_1040_, lean_object* v___f_1041_, lean_object* v_a_1042_){
_start:
{
uint8_t v_enabled_1043_; 
v_enabled_1043_ = lean_ctor_get_uint8(v_a_1042_, sizeof(void*)*3);
if (v_enabled_1043_ == 0)
{
lean_object* v___x_1044_; 
lean_dec(v___f_1041_);
lean_dec(v_toBind_1040_);
lean_dec(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v___x_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___x_1034_);
lean_inc(v___y_1033_);
v___x_1044_ = lean_apply_2(v___f_1031_, v___x_1032_, v___y_1033_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_3800__overap_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v___f_1031_);
v___x_1045_ = lean_box(0);
v___x_3800__overap_1046_ = l_Lean_Elab_addConstInfo___redArg(v___x_1034_, v___x_1035_, v___x_1036_, v___x_1037_, v_a_1038_, v_a_1039_, v___x_1045_);
lean_inc(v___y_1033_);
v___x_1047_ = lean_apply_1(v___x_3800__overap_1046_, v___y_1033_);
v___x_1048_ = lean_apply_4(v_toBind_1040_, lean_box(0), lean_box(0), v___x_1047_, v___f_1041_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object* v___f_1049_, lean_object* v___x_1050_, lean_object* v___y_1051_, lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_toBind_1058_, lean_object* v___f_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v___f_1049_, v___x_1050_, v___y_1051_, v___x_1052_, v___x_1053_, v___x_1054_, v___x_1055_, v_a_1056_, v_a_1057_, v_toBind_1058_, v___f_1059_, v_a_1060_);
lean_dec_ref(v_a_1060_);
lean_dec(v___y_1051_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v_inst_1062_, lean_object* v_a_1063_, lean_object* v_inst_1064_, lean_object* v_toBind_1065_, lean_object* v___f_1066_, lean_object* v___y_1067_, lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_getInfoState_1074_; lean_object* v___f_1075_; lean_object* v___f_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; 
v_getInfoState_1074_ = lean_ctor_get(v_inst_1062_, 0);
lean_inc(v_getInfoState_1074_);
lean_dec_ref(v_inst_1062_);
lean_inc_n(v_toBind_1065_, 2);
lean_inc(v_a_1073_);
lean_inc(v_a_1063_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 7, 5);
lean_closure_set(v___f_1075_, 0, v_a_1063_);
lean_closure_set(v___f_1075_, 1, v_a_1073_);
lean_closure_set(v___f_1075_, 2, v_inst_1064_);
lean_closure_set(v___f_1075_, 3, v_toBind_1065_);
lean_closure_set(v___f_1075_, 4, v___f_1066_);
lean_inc_n(v___y_1067_, 2);
lean_inc_ref(v___f_1075_);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_1076_, 0, v___f_1075_);
lean_closure_set(v___f_1076_, 1, v___y_1067_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 12, 11);
lean_closure_set(v___f_1077_, 0, v___f_1075_);
lean_closure_set(v___f_1077_, 1, v___x_1068_);
lean_closure_set(v___f_1077_, 2, v___y_1067_);
lean_closure_set(v___f_1077_, 3, v___x_1069_);
lean_closure_set(v___f_1077_, 4, v___x_1070_);
lean_closure_set(v___f_1077_, 5, v___x_1071_);
lean_closure_set(v___f_1077_, 6, v___x_1072_);
lean_closure_set(v___f_1077_, 7, v_a_1063_);
lean_closure_set(v___f_1077_, 8, v_a_1073_);
lean_closure_set(v___f_1077_, 9, v_toBind_1065_);
lean_closure_set(v___f_1077_, 10, v___f_1076_);
v___x_1078_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v_getInfoState_1074_, v___f_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object* v_inst_1079_, lean_object* v_a_1080_, lean_object* v_inst_1081_, lean_object* v_toBind_1082_, lean_object* v___f_1083_, lean_object* v___y_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v_inst_1079_, v_a_1080_, v_inst_1081_, v_toBind_1082_, v___f_1083_, v___y_1084_, v___x_1085_, v___x_1086_, v___x_1087_, v___x_1088_, v___x_1089_, v_a_1090_);
lean_dec(v___y_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_toBind_1094_, lean_object* v___f_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___f_1104_, lean_object* v___x_1105_, lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_x_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_3834__overap_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_inc_ref(v___x_1099_);
lean_inc_ref(v___x_1097_);
lean_inc_n(v___y_1112_, 2);
lean_inc(v_toBind_1094_);
lean_inc(v_a_1109_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 12, 11);
lean_closure_set(v___f_1113_, 0, v_inst_1092_);
lean_closure_set(v___f_1113_, 1, v_a_1109_);
lean_closure_set(v___f_1113_, 2, v_inst_1093_);
lean_closure_set(v___f_1113_, 3, v_toBind_1094_);
lean_closure_set(v___f_1113_, 4, v___f_1095_);
lean_closure_set(v___f_1113_, 5, v___y_1112_);
lean_closure_set(v___f_1113_, 6, v___x_1096_);
lean_closure_set(v___f_1113_, 7, v___x_1097_);
lean_closure_set(v___f_1113_, 8, v___x_1098_);
lean_closure_set(v___f_1113_, 9, v___x_1099_);
lean_closure_set(v___f_1113_, 10, v___x_1100_);
v___x_3834__overap_1114_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1097_, v___x_1099_, v___x_1101_, v___x_1102_, v___x_1103_, v___f_1104_, v___x_1105_, v___x_1106_, v___x_1107_, v_a_1108_, v_a_1109_);
v___x_1115_ = lean_apply_1(v___x_3834__overap_1114_, v___y_1112_);
v___x_1116_ = lean_apply_4(v_toBind_1094_, lean_box(0), lean_box(0), v___x_1115_, v___f_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object** _args){
lean_object* v_inst_1117_ = _args[0];
lean_object* v_inst_1118_ = _args[1];
lean_object* v_toBind_1119_ = _args[2];
lean_object* v___f_1120_ = _args[3];
lean_object* v___x_1121_ = _args[4];
lean_object* v___x_1122_ = _args[5];
lean_object* v___x_1123_ = _args[6];
lean_object* v___x_1124_ = _args[7];
lean_object* v___x_1125_ = _args[8];
lean_object* v___x_1126_ = _args[9];
lean_object* v___x_1127_ = _args[10];
lean_object* v___x_1128_ = _args[11];
lean_object* v___f_1129_ = _args[12];
lean_object* v___x_1130_ = _args[13];
lean_object* v___x_1131_ = _args[14];
lean_object* v___x_1132_ = _args[15];
lean_object* v_a_1133_ = _args[16];
lean_object* v_a_1134_ = _args[17];
lean_object* v_x_1135_ = _args[18];
lean_object* v___y_1136_ = _args[19];
lean_object* v___y_1137_ = _args[20];
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v_inst_1117_, v_inst_1118_, v_toBind_1119_, v___f_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_, v___x_1125_, v___x_1126_, v___x_1127_, v___x_1128_, v___f_1129_, v___x_1130_, v___x_1131_, v___x_1132_, v_a_1133_, v_a_1134_, v_x_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v_toPure_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_toBind_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v___x_1149_, lean_object* v___f_1150_, lean_object* v___x_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v_a_1154_, lean_object* v_ids_1155_, lean_object* v_ref_1156_, lean_object* v___f_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___f_1160_; lean_object* v___f_1161_; size_t v_sz_1162_; size_t v___x_1163_; lean_object* v___x_3854__overap_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1159_ = lean_box(0);
v___f_1160_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1160_, 0, v___x_1159_);
lean_closure_set(v___f_1160_, 1, v_toPure_1139_);
lean_inc_ref(v___x_1143_);
lean_inc(v_toBind_1142_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 21, 17);
lean_closure_set(v___f_1161_, 0, v_inst_1140_);
lean_closure_set(v___f_1161_, 1, v_inst_1141_);
lean_closure_set(v___f_1161_, 2, v_toBind_1142_);
lean_closure_set(v___f_1161_, 3, v___f_1160_);
lean_closure_set(v___f_1161_, 4, v___x_1159_);
lean_closure_set(v___f_1161_, 5, v___x_1143_);
lean_closure_set(v___f_1161_, 6, v___x_1144_);
lean_closure_set(v___f_1161_, 7, v___x_1145_);
lean_closure_set(v___f_1161_, 8, v___x_1146_);
lean_closure_set(v___f_1161_, 9, v___x_1147_);
lean_closure_set(v___f_1161_, 10, v___x_1148_);
lean_closure_set(v___f_1161_, 11, v___x_1149_);
lean_closure_set(v___f_1161_, 12, v___f_1150_);
lean_closure_set(v___f_1161_, 13, v___x_1151_);
lean_closure_set(v___f_1161_, 14, v___x_1152_);
lean_closure_set(v___f_1161_, 15, v___x_1153_);
lean_closure_set(v___f_1161_, 16, v_a_1154_);
v_sz_1162_ = lean_array_size(v_ids_1155_);
v___x_1163_ = ((size_t)0ULL);
v___x_3854__overap_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1143_, v_ids_1155_, v___f_1161_, v_sz_1162_, v___x_1163_, v___x_1159_);
v___x_1165_ = lean_apply_1(v___x_3854__overap_1164_, v_ref_1156_);
v___x_1166_ = lean_apply_4(v_toBind_1142_, lean_box(0), lean_box(0), v___x_1165_, v___f_1157_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object** _args){
lean_object* v_toPure_1167_ = _args[0];
lean_object* v_inst_1168_ = _args[1];
lean_object* v_inst_1169_ = _args[2];
lean_object* v_toBind_1170_ = _args[3];
lean_object* v___x_1171_ = _args[4];
lean_object* v___x_1172_ = _args[5];
lean_object* v___x_1173_ = _args[6];
lean_object* v___x_1174_ = _args[7];
lean_object* v___x_1175_ = _args[8];
lean_object* v___x_1176_ = _args[9];
lean_object* v___x_1177_ = _args[10];
lean_object* v___f_1178_ = _args[11];
lean_object* v___x_1179_ = _args[12];
lean_object* v___x_1180_ = _args[13];
lean_object* v___x_1181_ = _args[14];
lean_object* v_a_1182_ = _args[15];
lean_object* v_ids_1183_ = _args[16];
lean_object* v_ref_1184_ = _args[17];
lean_object* v___f_1185_ = _args[18];
lean_object* v_a_1186_ = _args[19];
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v_toPure_1167_, v_inst_1168_, v_inst_1169_, v_toBind_1170_, v___x_1171_, v___x_1172_, v___x_1173_, v___x_1174_, v___x_1175_, v___x_1176_, v___x_1177_, v___f_1178_, v___x_1179_, v___x_1180_, v___x_1181_, v_a_1182_, v_ids_1183_, v_ref_1184_, v___f_1185_, v_a_1186_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_toPure_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_toBind_1191_, lean_object* v___x_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___f_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_ids_1203_, lean_object* v_ref_1204_, lean_object* v___f_1205_, lean_object* v_ns_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___f_1208_; lean_object* v___x_3871__overap_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_inc(v_ref_1204_);
lean_inc(v_a_1207_);
lean_inc_ref(v___x_1202_);
lean_inc(v___x_1201_);
lean_inc_ref(v___x_1200_);
lean_inc(v___f_1199_);
lean_inc_ref(v___x_1194_);
lean_inc_ref(v___x_1192_);
lean_inc(v_toBind_1191_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed), 20, 19);
lean_closure_set(v___f_1208_, 0, v_toPure_1188_);
lean_closure_set(v___f_1208_, 1, v_inst_1189_);
lean_closure_set(v___f_1208_, 2, v_inst_1190_);
lean_closure_set(v___f_1208_, 3, v_toBind_1191_);
lean_closure_set(v___f_1208_, 4, v___x_1192_);
lean_closure_set(v___f_1208_, 5, v___x_1193_);
lean_closure_set(v___f_1208_, 6, v___x_1194_);
lean_closure_set(v___f_1208_, 7, v___x_1195_);
lean_closure_set(v___f_1208_, 8, v___x_1196_);
lean_closure_set(v___f_1208_, 9, v___x_1197_);
lean_closure_set(v___f_1208_, 10, v___x_1198_);
lean_closure_set(v___f_1208_, 11, v___f_1199_);
lean_closure_set(v___f_1208_, 12, v___x_1200_);
lean_closure_set(v___f_1208_, 13, v___x_1201_);
lean_closure_set(v___f_1208_, 14, v___x_1202_);
lean_closure_set(v___f_1208_, 15, v_a_1207_);
lean_closure_set(v___f_1208_, 16, v_ids_1203_);
lean_closure_set(v___f_1208_, 17, v_ref_1204_);
lean_closure_set(v___f_1208_, 18, v___f_1205_);
v___x_3871__overap_1209_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1192_, v___x_1194_, v___x_1201_, v___x_1200_, v___f_1199_, v___x_1202_, v_ns_1206_, v_a_1207_);
v___x_1210_ = lean_apply_1(v___x_3871__overap_1209_, v_ref_1204_);
v___x_1211_ = lean_apply_4(v_toBind_1191_, lean_box(0), lean_box(0), v___x_1210_, v___f_1208_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toPure_1212_ = _args[0];
lean_object* v_inst_1213_ = _args[1];
lean_object* v_inst_1214_ = _args[2];
lean_object* v_toBind_1215_ = _args[3];
lean_object* v___x_1216_ = _args[4];
lean_object* v___x_1217_ = _args[5];
lean_object* v___x_1218_ = _args[6];
lean_object* v___x_1219_ = _args[7];
lean_object* v___x_1220_ = _args[8];
lean_object* v___x_1221_ = _args[9];
lean_object* v___x_1222_ = _args[10];
lean_object* v___f_1223_ = _args[11];
lean_object* v___x_1224_ = _args[12];
lean_object* v___x_1225_ = _args[13];
lean_object* v___x_1226_ = _args[14];
lean_object* v_ids_1227_ = _args[15];
lean_object* v_ref_1228_ = _args[16];
lean_object* v___f_1229_ = _args[17];
lean_object* v_ns_1230_ = _args[18];
lean_object* v_a_1231_ = _args[19];
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_toPure_1212_, v_inst_1213_, v_inst_1214_, v_toBind_1215_, v___x_1216_, v___x_1217_, v___x_1218_, v___x_1219_, v___x_1220_, v___x_1221_, v___x_1222_, v___f_1223_, v___x_1224_, v___x_1225_, v___x_1226_, v_ids_1227_, v_ref_1228_, v___f_1229_, v_ns_1230_, v_a_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v___f_1235_, lean_object* v_toBind_1236_, lean_object* v___f_1237_, lean_object* v_a_1238_, lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_3886__overap_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_3886__overap_1242_ = l_Lean_activateScoped___redArg(v___x_1233_, v___x_1234_, v___f_1235_, v_a_1238_);
lean_inc(v___y_1241_);
v___x_1243_ = lean_apply_1(v___x_3886__overap_1242_, v___y_1241_);
v___x_1244_ = lean_apply_4(v_toBind_1236_, lean_box(0), lean_box(0), v___x_1243_, v___f_1237_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v___f_1247_, lean_object* v_toBind_1248_, lean_object* v___f_1249_, lean_object* v_a_1250_, lean_object* v_x_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(v___x_1245_, v___x_1246_, v___f_1247_, v_toBind_1248_, v___f_1249_, v_a_1250_, v_x_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v___x_1255_, lean_object* v___f_1256_, lean_object* v_a_1257_, lean_object* v___x_1258_, lean_object* v___y_1259_, lean_object* v_toBind_1260_, lean_object* v___f_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_3896__overap_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_3896__overap_1263_ = l_List_forIn_x27_loop___redArg(v___x_1255_, v___f_1256_, v_a_1257_, v___x_1258_);
lean_inc(v___y_1259_);
v___x_1264_ = lean_apply_1(v___x_3896__overap_1263_, v___y_1259_);
v___x_1265_ = lean_apply_4(v_toBind_1260_, lean_box(0), lean_box(0), v___x_1264_, v___f_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object* v___x_1266_, lean_object* v___f_1267_, lean_object* v_a_1268_, lean_object* v___x_1269_, lean_object* v___y_1270_, lean_object* v_toBind_1271_, lean_object* v___f_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v___x_1266_, v___f_1267_, v_a_1268_, v___x_1269_, v___y_1270_, v_toBind_1271_, v___f_1272_, v_a_1273_);
lean_dec(v___y_1270_);
lean_dec(v_a_1268_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v___x_1275_, lean_object* v___f_1276_, lean_object* v___x_1277_, lean_object* v___y_1278_, lean_object* v_toBind_1279_, lean_object* v___f_1280_, lean_object* v___x_1281_, lean_object* v___x_1282_, lean_object* v___x_1283_, lean_object* v___f_1284_, lean_object* v___x_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___f_1288_; lean_object* v___x_3909__overap_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_toBind_1279_);
lean_inc_n(v___y_1278_, 2);
lean_inc(v_a_1287_);
lean_inc_ref(v___x_1275_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 8, 7);
lean_closure_set(v___f_1288_, 0, v___x_1275_);
lean_closure_set(v___f_1288_, 1, v___f_1276_);
lean_closure_set(v___f_1288_, 2, v_a_1287_);
lean_closure_set(v___f_1288_, 3, v___x_1277_);
lean_closure_set(v___f_1288_, 4, v___y_1278_);
lean_closure_set(v___f_1288_, 5, v_toBind_1279_);
lean_closure_set(v___f_1288_, 6, v___f_1280_);
v___x_3909__overap_1289_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1275_, v___x_1281_, v___x_1282_, v___x_1283_, v___f_1284_, v___x_1285_, v_a_1286_, v_a_1287_);
v___x_1290_ = lean_apply_1(v___x_3909__overap_1289_, v___y_1278_);
v___x_1291_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1290_, v___f_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object* v___x_1292_, lean_object* v___f_1293_, lean_object* v___x_1294_, lean_object* v___y_1295_, lean_object* v_toBind_1296_, lean_object* v___f_1297_, lean_object* v___x_1298_, lean_object* v___x_1299_, lean_object* v___x_1300_, lean_object* v___f_1301_, lean_object* v___x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(v___x_1292_, v___f_1293_, v___x_1294_, v___y_1295_, v_toBind_1296_, v___f_1297_, v___x_1298_, v___x_1299_, v___x_1300_, v___f_1301_, v___x_1302_, v_a_1303_, v_a_1304_);
lean_dec(v___y_1295_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v___x_1306_, lean_object* v___f_1307_, lean_object* v___x_1308_, lean_object* v_toBind_1309_, lean_object* v___f_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v___x_1313_, lean_object* v___f_1314_, lean_object* v___x_1315_, lean_object* v___x_1316_, lean_object* v_a_1317_, lean_object* v_x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___f_1321_; lean_object* v___x_3925__overap_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_inc(v_a_1317_);
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___x_1311_);
lean_inc(v_toBind_1309_);
lean_inc_n(v___y_1320_, 2);
lean_inc_ref(v___x_1306_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed), 13, 12);
lean_closure_set(v___f_1321_, 0, v___x_1306_);
lean_closure_set(v___f_1321_, 1, v___f_1307_);
lean_closure_set(v___f_1321_, 2, v___x_1308_);
lean_closure_set(v___f_1321_, 3, v___y_1320_);
lean_closure_set(v___f_1321_, 4, v_toBind_1309_);
lean_closure_set(v___f_1321_, 5, v___f_1310_);
lean_closure_set(v___f_1321_, 6, v___x_1311_);
lean_closure_set(v___f_1321_, 7, v___x_1312_);
lean_closure_set(v___f_1321_, 8, v___x_1313_);
lean_closure_set(v___f_1321_, 9, v___f_1314_);
lean_closure_set(v___f_1321_, 10, v___x_1315_);
lean_closure_set(v___f_1321_, 11, v_a_1317_);
v___x_3925__overap_1322_ = l_Lean_resolveNamespace___redArg(v___x_1306_, v___x_1315_, v___x_1311_, v___x_1316_, v_a_1317_);
v___x_1323_ = lean_apply_1(v___x_3925__overap_1322_, v___y_1320_);
v___x_1324_ = lean_apply_4(v_toBind_1309_, lean_box(0), lean_box(0), v___x_1323_, v___f_1321_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object* v___x_1325_, lean_object* v___f_1326_, lean_object* v___x_1327_, lean_object* v_toBind_1328_, lean_object* v___f_1329_, lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v___x_1332_, lean_object* v___f_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v_a_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(v___x_1325_, v___f_1326_, v___x_1327_, v_toBind_1328_, v___f_1329_, v___x_1330_, v___x_1331_, v___x_1332_, v___f_1333_, v___x_1334_, v___x_1335_, v_a_1336_, v_x_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v___f_1343_, lean_object* v_a_1344_, lean_object* v___y_1345_, lean_object* v_toBind_1346_, lean_object* v___f_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v___x_3938__overap_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_3938__overap_1349_ = l_Lean_activateScoped___redArg(v___x_1341_, v___x_1342_, v___f_1343_, v_a_1344_);
lean_inc(v___y_1345_);
v___x_1350_ = lean_apply_1(v___x_3938__overap_1349_, v___y_1345_);
v___x_1351_ = lean_apply_4(v_toBind_1346_, lean_box(0), lean_box(0), v___x_1350_, v___f_1347_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object* v___x_1352_, lean_object* v___x_1353_, lean_object* v___f_1354_, lean_object* v_a_1355_, lean_object* v___y_1356_, lean_object* v_toBind_1357_, lean_object* v___f_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(v___x_1352_, v___x_1353_, v___f_1354_, v_a_1355_, v___y_1356_, v_toBind_1357_, v___f_1358_, v_a_1359_);
lean_dec(v___y_1356_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___f_1363_, lean_object* v_toBind_1364_, lean_object* v___f_1365_, lean_object* v___x_1366_, lean_object* v_inst_1367_, lean_object* v_a_1368_, lean_object* v_x_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc(v_toBind_1364_);
lean_inc(v___y_1371_);
lean_inc(v_a_1368_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed), 8, 7);
lean_closure_set(v___f_1372_, 0, v___x_1361_);
lean_closure_set(v___f_1372_, 1, v___x_1362_);
lean_closure_set(v___f_1372_, 2, v___f_1363_);
lean_closure_set(v___f_1372_, 3, v_a_1368_);
lean_closure_set(v___f_1372_, 4, v___y_1371_);
lean_closure_set(v___f_1372_, 5, v_toBind_1364_);
lean_closure_set(v___f_1372_, 6, v___f_1365_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1368_);
lean_ctor_set(v___x_1373_, 1, v___x_1366_);
v___x_1374_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1367_, v___x_1373_, v___y_1371_);
v___x_1375_ = lean_apply_4(v_toBind_1364_, lean_box(0), lean_box(0), v___x_1374_, v___f_1372_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v___f_1378_, lean_object* v_toBind_1379_, lean_object* v___f_1380_, lean_object* v___x_1381_, lean_object* v_inst_1382_, lean_object* v_a_1383_, lean_object* v_x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(v___x_1376_, v___x_1377_, v___f_1378_, v_toBind_1379_, v___f_1380_, v___x_1381_, v_inst_1382_, v_a_1383_, v_x_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object* v_toPure_1396_, lean_object* v_inst_1397_, lean_object* v_toBind_1398_, uint8_t v___x_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v_stx_1403_, lean_object* v___f_1404_, lean_object* v___x_1405_, lean_object* v___x_1406_, lean_object* v___f_1407_, lean_object* v___f_1408_, lean_object* v_inst_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v___x_1415_, lean_object* v___f_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___f_1420_, lean_object* v___f_1421_, lean_object* v_ref_1422_){
_start:
{
lean_object* v___f_1423_; 
lean_inc(v_toBind_1398_);
lean_inc(v_inst_1397_);
lean_inc(v_ref_1422_);
lean_inc(v_toPure_1396_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1423_, 0, v_toPure_1396_);
lean_closure_set(v___f_1423_, 1, v_ref_1422_);
lean_closure_set(v___f_1423_, 2, v_inst_1397_);
lean_closure_set(v___f_1423_, 3, v_toBind_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__0));
lean_inc_ref(v___x_1402_);
lean_inc_ref(v___x_1401_);
lean_inc_ref(v___x_1400_);
v___x_1425_ = l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1424_);
lean_inc(v_stx_1403_);
v___x_1426_ = l_Lean_Syntax_isOfKind(v_stx_1403_, v___x_1425_);
lean_dec(v___x_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__1));
lean_inc_ref(v___x_1402_);
lean_inc_ref(v___x_1401_);
lean_inc_ref(v___x_1400_);
v___x_1428_ = l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1427_);
lean_inc(v_stx_1403_);
v___x_1429_ = l_Lean_Syntax_isOfKind(v_stx_1403_, v___x_1428_);
lean_dec(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__2));
lean_inc_ref(v___x_1402_);
lean_inc_ref(v___x_1401_);
lean_inc_ref(v___x_1400_);
v___x_1431_ = l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1430_);
lean_inc(v_stx_1403_);
v___x_1432_ = l_Lean_Syntax_isOfKind(v_stx_1403_, v___x_1431_);
lean_dec(v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
lean_dec(v___f_1421_);
lean_dec_ref(v___f_1420_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__3));
lean_inc_ref(v___x_1402_);
lean_inc_ref(v___x_1401_);
lean_inc_ref(v___x_1400_);
v___x_1434_ = l_Lean_Name_mkStr4(v___x_1400_, v___x_1401_, v___x_1402_, v___x_1433_);
lean_inc(v_stx_1403_);
v___x_1435_ = l_Lean_Syntax_isOfKind(v_stx_1403_, v___x_1434_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___f_1436_; lean_object* v___x_4029__overap_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v___x_1419_);
lean_dec(v___x_1418_);
lean_dec_ref(v___x_1417_);
lean_dec(v___f_1416_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_inst_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1406_);
lean_dec(v_stx_1403_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_dec(v_inst_1397_);
lean_dec(v_toPure_1396_);
lean_inc(v_ref_1422_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1436_, 0, v___f_1404_);
lean_closure_set(v___f_1436_, 1, v_ref_1422_);
v___x_4029__overap_1437_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1405_);
v___x_1438_ = lean_apply_1(v___x_4029__overap_1437_, v_ref_1422_);
lean_inc(v_toBind_1398_);
v___x_1439_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1438_, v___f_1436_);
v___x_1440_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1439_, v___f_1423_);
return v___x_1440_;
}
else
{
lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v_nsStx_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___y_1448_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
lean_inc_n(v_ref_1422_, 2);
lean_inc(v___f_1404_);
v___f_1441_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1441_, 0, v___f_1404_);
lean_closure_set(v___f_1441_, 1, v_ref_1422_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1442_, 0, v___f_1404_);
lean_closure_set(v___f_1442_, 1, v_ref_1422_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v_nsStx_1444_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1443_);
v___x_1445_ = lean_unsigned_to_nat(2u);
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1446_, 0, v___x_1400_);
lean_closure_set(v___f_1446_, 1, v___x_1401_);
lean_closure_set(v___f_1446_, 2, v___x_1402_);
lean_closure_set(v___f_1446_, 3, v___x_1443_);
lean_closure_set(v___f_1446_, 4, v___x_1445_);
v___x_1468_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1445_);
lean_dec(v_stx_1403_);
v___x_1469_ = l_Lean_Syntax_getArgs(v___x_1468_);
lean_dec(v___x_1468_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___closed__4));
v___x_1471_ = lean_array_get_size(v___x_1469_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1473_ = lean_nat_dec_lt(v___x_1443_, v___x_1471_);
if (v___x_1473_ == 0)
{
lean_dec_ref(v___x_1469_);
v___y_1448_ = v___x_1470_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; size_t v___x_1479_; size_t v___x_1480_; lean_object* v___x_1481_; lean_object* v_snd_1482_; 
v___x_1474_ = lean_box(v___x_1435_);
v___x_1475_ = lean_box(v___x_1432_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1476_, 0, v___x_1474_);
lean_closure_set(v___f_1476_, 1, v___x_1475_);
v___x_1477_ = lean_box(v___x_1473_);
v___x_1478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1470_);
v___x_1479_ = ((size_t)0ULL);
v___x_1480_ = lean_usize_of_nat(v___x_1471_);
v___x_1481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1472_, v___f_1476_, v___x_1469_, v___x_1479_, v___x_1480_, v___x_1478_);
v_snd_1482_ = lean_ctor_get(v___x_1481_, 1);
lean_inc(v_snd_1482_);
lean_dec(v___x_1481_);
v___y_1448_ = v_snd_1482_;
goto v___jp_1447_;
}
v___jp_1447_:
{
size_t v_sz_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v_sz_1449_ = lean_array_size(v___y_1448_);
v___x_1450_ = ((size_t)0ULL);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1406_, v___f_1446_, v_sz_1449_, v___x_1450_, v___y_1448_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_4041__overap_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec(v_nsStx_1444_);
lean_dec_ref(v___f_1441_);
lean_dec_ref(v___x_1419_);
lean_dec(v___x_1418_);
lean_dec_ref(v___x_1417_);
lean_dec(v___f_1416_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1412_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_inst_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec(v_inst_1397_);
lean_dec(v_toPure_1396_);
v___x_4041__overap_1452_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1405_);
v___x_1453_ = lean_apply_1(v___x_4041__overap_1452_, v_ref_1422_);
lean_inc(v_toBind_1398_);
v___x_1454_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1453_, v___f_1442_);
v___x_1455_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1454_, v___f_1423_);
return v___x_1455_;
}
else
{
lean_object* v_val_1456_; lean_object* v___x_1457_; size_t v_sz_1458_; lean_object* v_tos_1459_; lean_object* v_froms_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___f_1463_; lean_object* v___x_4057__overap_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v___f_1442_);
v_val_1456_ = lean_ctor_get(v___x_1451_, 0);
lean_inc_n(v_val_1456_, 2);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1457_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1458_ = lean_array_size(v_val_1456_);
v_tos_1459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1457_, v___f_1407_, v_sz_1458_, v___x_1450_, v_val_1456_);
v_froms_1460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1457_, v___f_1408_, v_sz_1458_, v___x_1450_, v_val_1456_);
v___x_1461_ = lean_box(0);
v___x_1462_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed__const__1));
lean_inc(v_nsStx_1444_);
lean_inc(v_ref_1422_);
lean_inc_ref(v___x_1419_);
lean_inc_ref(v___x_1413_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1410_);
lean_inc_n(v_toBind_1398_, 2);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_1463_, 0, v_froms_1460_);
lean_closure_set(v___f_1463_, 1, v_tos_1459_);
lean_closure_set(v___f_1463_, 2, v_toPure_1396_);
lean_closure_set(v___f_1463_, 3, v_inst_1409_);
lean_closure_set(v___f_1463_, 4, v_inst_1397_);
lean_closure_set(v___f_1463_, 5, v_toBind_1398_);
lean_closure_set(v___f_1463_, 6, v___x_1410_);
lean_closure_set(v___f_1463_, 7, v___x_1411_);
lean_closure_set(v___f_1463_, 8, v___x_1412_);
lean_closure_set(v___f_1463_, 9, v___x_1413_);
lean_closure_set(v___f_1463_, 10, v___x_1405_);
lean_closure_set(v___f_1463_, 11, v___x_1414_);
lean_closure_set(v___f_1463_, 12, v___x_1415_);
lean_closure_set(v___f_1463_, 13, v___f_1416_);
lean_closure_set(v___f_1463_, 14, v___x_1417_);
lean_closure_set(v___f_1463_, 15, v___x_1418_);
lean_closure_set(v___f_1463_, 16, v___x_1419_);
lean_closure_set(v___f_1463_, 17, v___x_1462_);
lean_closure_set(v___f_1463_, 18, v_ref_1422_);
lean_closure_set(v___f_1463_, 19, v___f_1441_);
lean_closure_set(v___f_1463_, 20, v___x_1461_);
lean_closure_set(v___f_1463_, 21, v_nsStx_1444_);
v___x_4057__overap_1464_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1410_, v___x_1419_, v___x_1412_, v___x_1413_, v_nsStx_1444_);
v___x_1465_ = lean_apply_1(v___x_4057__overap_1464_, v_ref_1422_);
v___x_1466_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1465_, v___f_1463_);
v___x_1467_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1466_, v___f_1423_);
return v___x_1467_;
}
}
}
}
else
{
lean_object* v___f_1483_; lean_object* v___x_1484_; lean_object* v_nsStx_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_ids_1489_; lean_object* v___f_1490_; lean_object* v___x_4086__overap_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_inc_n(v_ref_1422_, 2);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1483_, 0, v___f_1404_);
lean_closure_set(v___f_1483_, 1, v_ref_1422_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v_nsStx_1485_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1484_);
v___x_1486_ = lean_unsigned_to_nat(2u);
v___x_1487_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1486_);
lean_dec(v_stx_1403_);
v___x_1488_ = lean_box(0);
v_ids_1489_ = l_Lean_Syntax_getArgs(v___x_1487_);
lean_dec(v___x_1487_);
lean_inc(v_nsStx_1485_);
lean_inc_ref(v___x_1419_);
lean_inc_ref(v___x_1413_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1410_);
lean_inc_n(v_toBind_1398_, 2);
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed), 23, 22);
lean_closure_set(v___f_1490_, 0, v_ids_1489_);
lean_closure_set(v___f_1490_, 1, v___f_1420_);
lean_closure_set(v___f_1490_, 2, v_inst_1397_);
lean_closure_set(v___f_1490_, 3, v_ref_1422_);
lean_closure_set(v___f_1490_, 4, v_toBind_1398_);
lean_closure_set(v___f_1490_, 5, v___f_1483_);
lean_closure_set(v___f_1490_, 6, v_toPure_1396_);
lean_closure_set(v___f_1490_, 7, v_inst_1409_);
lean_closure_set(v___f_1490_, 8, v___x_1410_);
lean_closure_set(v___f_1490_, 9, v___x_1411_);
lean_closure_set(v___f_1490_, 10, v___x_1412_);
lean_closure_set(v___f_1490_, 11, v___x_1413_);
lean_closure_set(v___f_1490_, 12, v___x_1405_);
lean_closure_set(v___f_1490_, 13, v___x_1414_);
lean_closure_set(v___f_1490_, 14, v___x_1415_);
lean_closure_set(v___f_1490_, 15, v___f_1416_);
lean_closure_set(v___f_1490_, 16, v___x_1417_);
lean_closure_set(v___f_1490_, 17, v___x_1418_);
lean_closure_set(v___f_1490_, 18, v___x_1419_);
lean_closure_set(v___f_1490_, 19, v___f_1421_);
lean_closure_set(v___f_1490_, 20, v___x_1488_);
lean_closure_set(v___f_1490_, 21, v_nsStx_1485_);
v___x_4086__overap_1491_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1410_, v___x_1419_, v___x_1412_, v___x_1413_, v_nsStx_1485_);
v___x_1492_ = lean_apply_1(v___x_4086__overap_1491_, v_ref_1422_);
v___x_1493_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1492_, v___f_1490_);
v___x_1494_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1493_, v___f_1423_);
return v___x_1494_;
}
}
else
{
lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v_ns_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_ids_1500_; lean_object* v___f_1501_; lean_object* v___x_4094__overap_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v___f_1421_);
lean_dec_ref(v___f_1420_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_inc_n(v_ref_1422_, 2);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1495_, 0, v___f_1404_);
lean_closure_set(v___f_1495_, 1, v_ref_1422_);
v___x_1496_ = lean_unsigned_to_nat(0u);
v_ns_1497_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1496_);
v___x_1498_ = lean_unsigned_to_nat(2u);
v___x_1499_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1498_);
lean_dec(v_stx_1403_);
v_ids_1500_ = l_Lean_Syntax_getArgs(v___x_1499_);
lean_dec(v___x_1499_);
lean_inc(v_ns_1497_);
lean_inc_ref(v___x_1419_);
lean_inc_ref(v___x_1413_);
lean_inc_ref(v___x_1412_);
lean_inc_ref(v___x_1410_);
lean_inc_n(v_toBind_1398_, 2);
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed), 20, 19);
lean_closure_set(v___f_1501_, 0, v_toPure_1396_);
lean_closure_set(v___f_1501_, 1, v_inst_1409_);
lean_closure_set(v___f_1501_, 2, v_inst_1397_);
lean_closure_set(v___f_1501_, 3, v_toBind_1398_);
lean_closure_set(v___f_1501_, 4, v___x_1410_);
lean_closure_set(v___f_1501_, 5, v___x_1411_);
lean_closure_set(v___f_1501_, 6, v___x_1412_);
lean_closure_set(v___f_1501_, 7, v___x_1413_);
lean_closure_set(v___f_1501_, 8, v___x_1405_);
lean_closure_set(v___f_1501_, 9, v___x_1414_);
lean_closure_set(v___f_1501_, 10, v___x_1415_);
lean_closure_set(v___f_1501_, 11, v___f_1416_);
lean_closure_set(v___f_1501_, 12, v___x_1417_);
lean_closure_set(v___f_1501_, 13, v___x_1418_);
lean_closure_set(v___f_1501_, 14, v___x_1419_);
lean_closure_set(v___f_1501_, 15, v_ids_1500_);
lean_closure_set(v___f_1501_, 16, v_ref_1422_);
lean_closure_set(v___f_1501_, 17, v___f_1495_);
lean_closure_set(v___f_1501_, 18, v_ns_1497_);
v___x_4094__overap_1502_ = l_Lean_resolveNamespace___redArg(v___x_1410_, v___x_1419_, v___x_1412_, v___x_1413_, v_ns_1497_);
v___x_1503_ = lean_apply_1(v___x_4094__overap_1502_, v_ref_1422_);
v___x_1504_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1503_, v___f_1501_);
v___x_1505_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1504_, v___f_1423_);
return v___x_1505_;
}
}
else
{
lean_object* v___f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_nss_1509_; lean_object* v___x_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; size_t v_sz_1514_; size_t v___x_1515_; lean_object* v___x_4106__overap_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v___f_1420_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v_inst_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_dec(v_inst_1397_);
lean_inc(v_ref_1422_);
v___f_1506_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1506_, 0, v___f_1404_);
lean_closure_set(v___f_1506_, 1, v_ref_1422_);
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1507_);
lean_dec(v_stx_1403_);
v_nss_1509_ = l_Lean_Syntax_getArgs(v___x_1508_);
lean_dec(v___x_1508_);
v___x_1510_ = lean_box(0);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1511_, 0, v___x_1510_);
lean_closure_set(v___f_1511_, 1, v_toPure_1396_);
lean_inc_ref(v___f_1511_);
lean_inc_n(v_toBind_1398_, 3);
lean_inc_ref(v___x_1412_);
lean_inc_ref_n(v___x_1410_, 2);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed), 9, 5);
lean_closure_set(v___f_1512_, 0, v___x_1410_);
lean_closure_set(v___f_1512_, 1, v___x_1412_);
lean_closure_set(v___f_1512_, 2, v___f_1421_);
lean_closure_set(v___f_1512_, 3, v_toBind_1398_);
lean_closure_set(v___f_1512_, 4, v___f_1511_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 15, 11);
lean_closure_set(v___f_1513_, 0, v___x_1410_);
lean_closure_set(v___f_1513_, 1, v___f_1512_);
lean_closure_set(v___f_1513_, 2, v___x_1510_);
lean_closure_set(v___f_1513_, 3, v_toBind_1398_);
lean_closure_set(v___f_1513_, 4, v___f_1511_);
lean_closure_set(v___f_1513_, 5, v___x_1412_);
lean_closure_set(v___f_1513_, 6, v___x_1418_);
lean_closure_set(v___f_1513_, 7, v___x_1417_);
lean_closure_set(v___f_1513_, 8, v___f_1416_);
lean_closure_set(v___f_1513_, 9, v___x_1419_);
lean_closure_set(v___f_1513_, 10, v___x_1413_);
v_sz_1514_ = lean_array_size(v_nss_1509_);
v___x_1515_ = ((size_t)0ULL);
v___x_4106__overap_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1410_, v_nss_1509_, v___f_1513_, v_sz_1514_, v___x_1515_, v___x_1510_);
v___x_1517_ = lean_apply_1(v___x_4106__overap_1516_, v_ref_1422_);
v___x_1518_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1517_, v___f_1506_);
v___x_1519_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1518_, v___f_1423_);
return v___x_1519_;
}
}
else
{
lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_nss_1524_; lean_object* v___x_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___f_1528_; size_t v_sz_1529_; size_t v___x_1530_; lean_object* v___x_4119__overap_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v___f_1420_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1411_);
lean_dec_ref(v_inst_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v___f_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_inc(v_ref_1422_);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1520_, 0, v___f_1404_);
lean_closure_set(v___f_1520_, 1, v_ref_1422_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Lean_Syntax_getArg(v_stx_1403_, v___x_1521_);
lean_dec(v_stx_1403_);
v___x_1523_ = lean_box(0);
v_nss_1524_ = l_Lean_Syntax_getArgs(v___x_1522_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v___f_1526_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1526_, 0, v___x_1525_);
lean_closure_set(v___f_1526_, 1, v_toPure_1396_);
lean_inc_ref(v___f_1526_);
lean_inc_n(v_toBind_1398_, 3);
lean_inc_ref(v___x_1412_);
lean_inc_ref_n(v___x_1410_, 2);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed), 11, 7);
lean_closure_set(v___f_1527_, 0, v___x_1410_);
lean_closure_set(v___f_1527_, 1, v___x_1412_);
lean_closure_set(v___f_1527_, 2, v___f_1421_);
lean_closure_set(v___f_1527_, 3, v_toBind_1398_);
lean_closure_set(v___f_1527_, 4, v___f_1526_);
lean_closure_set(v___f_1527_, 5, v___x_1523_);
lean_closure_set(v___f_1527_, 6, v_inst_1397_);
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 15, 11);
lean_closure_set(v___f_1528_, 0, v___x_1410_);
lean_closure_set(v___f_1528_, 1, v___f_1527_);
lean_closure_set(v___f_1528_, 2, v___x_1525_);
lean_closure_set(v___f_1528_, 3, v_toBind_1398_);
lean_closure_set(v___f_1528_, 4, v___f_1526_);
lean_closure_set(v___f_1528_, 5, v___x_1412_);
lean_closure_set(v___f_1528_, 6, v___x_1418_);
lean_closure_set(v___f_1528_, 7, v___x_1417_);
lean_closure_set(v___f_1528_, 8, v___f_1416_);
lean_closure_set(v___f_1528_, 9, v___x_1419_);
lean_closure_set(v___f_1528_, 10, v___x_1413_);
v_sz_1529_ = lean_array_size(v_nss_1524_);
v___x_1530_ = ((size_t)0ULL);
v___x_4119__overap_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1410_, v_nss_1524_, v___f_1528_, v_sz_1529_, v___x_1530_, v___x_1525_);
v___x_1532_ = lean_apply_1(v___x_4119__overap_1531_, v_ref_1422_);
v___x_1533_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1532_, v___f_1520_);
v___x_1534_ = lean_apply_4(v_toBind_1398_, lean_box(0), lean_box(0), v___x_1533_, v___f_1423_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object** _args){
lean_object* v_toPure_1535_ = _args[0];
lean_object* v_inst_1536_ = _args[1];
lean_object* v_toBind_1537_ = _args[2];
lean_object* v___x_1538_ = _args[3];
lean_object* v___x_1539_ = _args[4];
lean_object* v___x_1540_ = _args[5];
lean_object* v___x_1541_ = _args[6];
lean_object* v_stx_1542_ = _args[7];
lean_object* v___f_1543_ = _args[8];
lean_object* v___x_1544_ = _args[9];
lean_object* v___x_1545_ = _args[10];
lean_object* v___f_1546_ = _args[11];
lean_object* v___f_1547_ = _args[12];
lean_object* v_inst_1548_ = _args[13];
lean_object* v___x_1549_ = _args[14];
lean_object* v___x_1550_ = _args[15];
lean_object* v___x_1551_ = _args[16];
lean_object* v___x_1552_ = _args[17];
lean_object* v___x_1553_ = _args[18];
lean_object* v___x_1554_ = _args[19];
lean_object* v___f_1555_ = _args[20];
lean_object* v___x_1556_ = _args[21];
lean_object* v___x_1557_ = _args[22];
lean_object* v___x_1558_ = _args[23];
lean_object* v___f_1559_ = _args[24];
lean_object* v___f_1560_ = _args[25];
lean_object* v_ref_1561_ = _args[26];
_start:
{
uint8_t v___x_5426__boxed_1562_; lean_object* v_res_1563_; 
v___x_5426__boxed_1562_ = lean_unbox(v___x_1538_);
v_res_1563_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(v_toPure_1535_, v_inst_1536_, v_toBind_1537_, v___x_5426__boxed_1562_, v___x_1539_, v___x_1540_, v___x_1541_, v_stx_1542_, v___f_1543_, v___x_1544_, v___x_1545_, v___f_1546_, v___f_1547_, v_inst_1548_, v___x_1549_, v___x_1550_, v___x_1551_, v___x_1552_, v___x_1553_, v___x_1554_, v___f_1555_, v___x_1556_, v___x_1557_, v___x_1558_, v___f_1559_, v___f_1560_, v_ref_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v_toPure_1564_, lean_object* v_____x_1565_){
_start:
{
lean_object* v_fst_1566_; lean_object* v___x_1567_; 
v_fst_1566_ = lean_ctor_get(v_____x_1565_, 0);
lean_inc(v_fst_1566_);
lean_dec_ref(v_____x_1565_);
v___x_1567_ = lean_apply_2(v_toPure_1564_, lean_box(0), v_fst_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object* v_toApplicative_1577_, lean_object* v_stx_1578_, lean_object* v_____do__lift_1579_, lean_object* v_inst_1580_, lean_object* v_toBind_1581_, lean_object* v___f_1582_, lean_object* v___x_1583_, lean_object* v___x_1584_, lean_object* v___f_1585_, lean_object* v___f_1586_, lean_object* v_inst_1587_, lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___f_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v___f_1598_, lean_object* v___f_1599_, lean_object* v_____do__lift_1600_){
_start:
{
lean_object* v_toPure_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___f_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_toPure_1601_ = lean_ctor_get(v_toApplicative_1577_, 1);
lean_inc_n(v_toPure_1601_, 2);
lean_dec_ref(v_toApplicative_1577_);
v___x_1602_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__0));
v___x_1603_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__1));
v___x_1604_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__2));
v___x_1605_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___closed__4));
lean_inc(v_stx_1578_);
v___x_1606_ = l_Lean_Syntax_isOfKind(v_stx_1578_, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_____do__lift_1579_);
lean_ctor_set(v___x_1607_, 1, v_____do__lift_1600_);
v___x_1608_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1608_, 0, lean_box(0));
lean_closure_set(v___x_1608_, 1, lean_box(0));
lean_closure_set(v___x_1608_, 2, v___x_1607_);
lean_inc(v_inst_1580_);
v___x_1609_ = lean_apply_2(v_inst_1580_, lean_box(0), v___x_1608_);
v___x_1610_ = lean_box(v___x_1606_);
lean_inc_n(v_toBind_1581_, 2);
v___f_1611_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed), 27, 26);
lean_closure_set(v___f_1611_, 0, v_toPure_1601_);
lean_closure_set(v___f_1611_, 1, v_inst_1580_);
lean_closure_set(v___f_1611_, 2, v_toBind_1581_);
lean_closure_set(v___f_1611_, 3, v___x_1610_);
lean_closure_set(v___f_1611_, 4, v___x_1602_);
lean_closure_set(v___f_1611_, 5, v___x_1603_);
lean_closure_set(v___f_1611_, 6, v___x_1604_);
lean_closure_set(v___f_1611_, 7, v_stx_1578_);
lean_closure_set(v___f_1611_, 8, v___f_1582_);
lean_closure_set(v___f_1611_, 9, v___x_1583_);
lean_closure_set(v___f_1611_, 10, v___x_1584_);
lean_closure_set(v___f_1611_, 11, v___f_1585_);
lean_closure_set(v___f_1611_, 12, v___f_1586_);
lean_closure_set(v___f_1611_, 13, v_inst_1587_);
lean_closure_set(v___f_1611_, 14, v___x_1588_);
lean_closure_set(v___f_1611_, 15, v___x_1589_);
lean_closure_set(v___f_1611_, 16, v___x_1590_);
lean_closure_set(v___f_1611_, 17, v___x_1591_);
lean_closure_set(v___f_1611_, 18, v___x_1592_);
lean_closure_set(v___f_1611_, 19, v___x_1593_);
lean_closure_set(v___f_1611_, 20, v___f_1594_);
lean_closure_set(v___f_1611_, 21, v___x_1595_);
lean_closure_set(v___f_1611_, 22, v___x_1596_);
lean_closure_set(v___f_1611_, 23, v___x_1597_);
lean_closure_set(v___f_1611_, 24, v___f_1598_);
lean_closure_set(v___f_1611_, 25, v___f_1599_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37), 2, 1);
lean_closure_set(v___f_1612_, 0, v_toPure_1601_);
v___x_1613_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1609_, v___f_1611_);
v___x_1614_ = lean_apply_4(v_toBind_1581_, lean_box(0), lean_box(0), v___x_1613_, v___f_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toApplicative_1615_ = _args[0];
lean_object* v_stx_1616_ = _args[1];
lean_object* v_____do__lift_1617_ = _args[2];
lean_object* v_inst_1618_ = _args[3];
lean_object* v_toBind_1619_ = _args[4];
lean_object* v___f_1620_ = _args[5];
lean_object* v___x_1621_ = _args[6];
lean_object* v___x_1622_ = _args[7];
lean_object* v___f_1623_ = _args[8];
lean_object* v___f_1624_ = _args[9];
lean_object* v_inst_1625_ = _args[10];
lean_object* v___x_1626_ = _args[11];
lean_object* v___x_1627_ = _args[12];
lean_object* v___x_1628_ = _args[13];
lean_object* v___x_1629_ = _args[14];
lean_object* v___x_1630_ = _args[15];
lean_object* v___x_1631_ = _args[16];
lean_object* v___f_1632_ = _args[17];
lean_object* v___x_1633_ = _args[18];
lean_object* v___x_1634_ = _args[19];
lean_object* v___x_1635_ = _args[20];
lean_object* v___f_1636_ = _args[21];
lean_object* v___f_1637_ = _args[22];
lean_object* v_____do__lift_1638_ = _args[23];
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(v_toApplicative_1615_, v_stx_1616_, v_____do__lift_1617_, v_inst_1618_, v_toBind_1619_, v___f_1620_, v___x_1621_, v___x_1622_, v___f_1623_, v___f_1624_, v_inst_1625_, v___x_1626_, v___x_1627_, v___x_1628_, v___x_1629_, v___x_1630_, v___x_1631_, v___f_1632_, v___x_1633_, v___x_1634_, v___x_1635_, v___f_1636_, v___f_1637_, v_____do__lift_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object* v_toApplicative_1640_, lean_object* v_stx_1641_, lean_object* v_inst_1642_, lean_object* v_toBind_1643_, lean_object* v___f_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v___f_1647_, lean_object* v___f_1648_, lean_object* v_inst_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, lean_object* v___x_1655_, lean_object* v___f_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v___x_1659_, lean_object* v___f_1660_, lean_object* v___f_1661_, lean_object* v_getCurrNamespace_1662_, lean_object* v_____do__lift_1663_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
lean_inc(v_toBind_1643_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed), 24, 23);
lean_closure_set(v___f_1664_, 0, v_toApplicative_1640_);
lean_closure_set(v___f_1664_, 1, v_stx_1641_);
lean_closure_set(v___f_1664_, 2, v_____do__lift_1663_);
lean_closure_set(v___f_1664_, 3, v_inst_1642_);
lean_closure_set(v___f_1664_, 4, v_toBind_1643_);
lean_closure_set(v___f_1664_, 5, v___f_1644_);
lean_closure_set(v___f_1664_, 6, v___x_1645_);
lean_closure_set(v___f_1664_, 7, v___x_1646_);
lean_closure_set(v___f_1664_, 8, v___f_1647_);
lean_closure_set(v___f_1664_, 9, v___f_1648_);
lean_closure_set(v___f_1664_, 10, v_inst_1649_);
lean_closure_set(v___f_1664_, 11, v___x_1650_);
lean_closure_set(v___f_1664_, 12, v___x_1651_);
lean_closure_set(v___f_1664_, 13, v___x_1652_);
lean_closure_set(v___f_1664_, 14, v___x_1653_);
lean_closure_set(v___f_1664_, 15, v___x_1654_);
lean_closure_set(v___f_1664_, 16, v___x_1655_);
lean_closure_set(v___f_1664_, 17, v___f_1656_);
lean_closure_set(v___f_1664_, 18, v___x_1657_);
lean_closure_set(v___f_1664_, 19, v___x_1658_);
lean_closure_set(v___f_1664_, 20, v___x_1659_);
lean_closure_set(v___f_1664_, 21, v___f_1660_);
lean_closure_set(v___f_1664_, 22, v___f_1661_);
v___x_1665_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v_getCurrNamespace_1662_, v___f_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toApplicative_1666_ = _args[0];
lean_object* v_stx_1667_ = _args[1];
lean_object* v_inst_1668_ = _args[2];
lean_object* v_toBind_1669_ = _args[3];
lean_object* v___f_1670_ = _args[4];
lean_object* v___x_1671_ = _args[5];
lean_object* v___x_1672_ = _args[6];
lean_object* v___f_1673_ = _args[7];
lean_object* v___f_1674_ = _args[8];
lean_object* v_inst_1675_ = _args[9];
lean_object* v___x_1676_ = _args[10];
lean_object* v___x_1677_ = _args[11];
lean_object* v___x_1678_ = _args[12];
lean_object* v___x_1679_ = _args[13];
lean_object* v___x_1680_ = _args[14];
lean_object* v___x_1681_ = _args[15];
lean_object* v___f_1682_ = _args[16];
lean_object* v___x_1683_ = _args[17];
lean_object* v___x_1684_ = _args[18];
lean_object* v___x_1685_ = _args[19];
lean_object* v___f_1686_ = _args[20];
lean_object* v___f_1687_ = _args[21];
lean_object* v_getCurrNamespace_1688_ = _args[22];
lean_object* v_____do__lift_1689_ = _args[23];
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(v_toApplicative_1666_, v_stx_1667_, v_inst_1668_, v_toBind_1669_, v___f_1670_, v___x_1671_, v___x_1672_, v___f_1673_, v___f_1674_, v_inst_1675_, v___x_1676_, v___x_1677_, v___x_1678_, v___x_1679_, v___x_1680_, v___x_1681_, v___f_1682_, v___x_1683_, v___x_1684_, v___x_1685_, v___f_1686_, v___f_1687_, v_getCurrNamespace_1688_, v_____do__lift_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_stx_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v_toApplicative_1727_; lean_object* v_toBind_1728_; lean_object* v_getCurrNamespace_1729_; lean_object* v_getOpenDecls_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1769_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9));
v_toApplicative_1727_ = lean_ctor_get(v_inst_1715_, 0);
lean_inc_ref(v_toApplicative_1727_);
v_toBind_1728_ = lean_ctor_get(v_inst_1715_, 1);
lean_inc(v_toBind_1728_);
v_getCurrNamespace_1729_ = lean_ctor_get(v_inst_1723_, 0);
v_getOpenDecls_1730_ = lean_ctor_get(v_inst_1723_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_inst_1723_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1732_ = v_inst_1723_;
v_isShared_1733_ = v_isSharedCheck_1769_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_getOpenDecls_1730_);
lean_inc(v_getCurrNamespace_1729_);
lean_dec(v_inst_1723_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1769_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___f_1736_; lean_object* v___x_1738_; 
lean_inc_ref(v_inst_1715_);
v___x_1734_ = l_StateRefT_x27_instMonad___redArg(v_inst_1715_);
lean_inc_ref(v_inst_1717_);
v___f_1735_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1735_, 0, v_inst_1717_);
v___f_1736_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1736_, 0, v_inst_1717_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v___f_1736_);
lean_ctor_set(v___x_1732_, 0, v___f_1735_);
v___x_1738_ = v___x_1732_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___f_1735_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___f_1736_);
v___x_1738_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v_getEnv_1740_; lean_object* v_modifyEnv_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1767_; 
lean_inc(v_inst_1720_);
v___x_1739_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1715_, v_inst_1720_);
v_getEnv_1740_ = lean_ctor_get(v_inst_1716_, 0);
v_modifyEnv_1741_ = lean_ctor_get(v_inst_1716_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_inst_1716_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1743_ = v_inst_1716_;
v_isShared_1744_ = v_isSharedCheck_1767_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_modifyEnv_1741_);
lean_inc(v_getEnv_1740_);
lean_dec(v_inst_1716_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1767_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
lean_inc_ref(v_toApplicative_1727_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1745_, 0, v_toApplicative_1727_);
lean_inc(v_toBind_1728_);
lean_inc(v_inst_1720_);
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1746_, 0, v_inst_1720_);
lean_closure_set(v___f_1746_, 1, v_toBind_1728_);
lean_closure_set(v___f_1746_, 2, v___f_1745_);
v___f_1747_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10));
v___f_1748_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11));
v___f_1749_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12));
v___x_1750_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1751_, 0, v_modifyEnv_1741_);
lean_closure_set(v___f_1751_, 1, v___x_1750_);
v___x_1752_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1752_, 0, lean_box(0));
lean_closure_set(v___x_1752_, 1, lean_box(0));
lean_closure_set(v___x_1752_, 2, lean_box(0));
lean_closure_set(v___x_1752_, 3, lean_box(0));
lean_closure_set(v___x_1752_, 4, v_getEnv_1740_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v___f_1751_);
lean_ctor_set(v___x_1743_, 0, v___x_1752_);
v___x_1754_ = v___x_1743_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v___f_1751_);
v___x_1754_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; 
v___x_1755_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_1756_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1750_, v___x_1755_, v_inst_1718_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1757_, 0, v_inst_1719_);
lean_closure_set(v___f_1757_, 1, v___x_1750_);
lean_inc_ref(v___x_1734_);
lean_inc_ref(v___f_1757_);
v___x_1758_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1757_, v___x_1734_);
lean_inc(v___x_1758_);
lean_inc_ref(v___x_1756_);
lean_inc_ref(v___x_1738_);
v___x_1759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1738_);
lean_ctor_set(v___x_1759_, 1, v___x_1756_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
v___x_1760_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1760_, 0, lean_box(0));
lean_closure_set(v___x_1760_, 1, lean_box(0));
lean_closure_set(v___x_1760_, 2, lean_box(0));
lean_closure_set(v___x_1760_, 3, lean_box(0));
lean_closure_set(v___x_1760_, 4, v_inst_1722_);
v___x_1761_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1750_, v_inst_1721_);
lean_inc_ref(v_inst_1724_);
v___x_1762_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_1750_, v_inst_1724_);
lean_inc(v_inst_1720_);
v___f_1763_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1763_, 0, v_inst_1720_);
lean_closure_set(v___f_1763_, 1, v___x_1750_);
lean_inc(v_toBind_1728_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed), 24, 23);
lean_closure_set(v___f_1764_, 0, v_toApplicative_1727_);
lean_closure_set(v___f_1764_, 1, v_stx_1725_);
lean_closure_set(v___f_1764_, 2, v_inst_1720_);
lean_closure_set(v___f_1764_, 3, v_toBind_1728_);
lean_closure_set(v___f_1764_, 4, v___f_1746_);
lean_closure_set(v___f_1764_, 5, v___x_1738_);
lean_closure_set(v___f_1764_, 6, v___x_1726_);
lean_closure_set(v___f_1764_, 7, v___f_1749_);
lean_closure_set(v___f_1764_, 8, v___f_1748_);
lean_closure_set(v___f_1764_, 9, v_inst_1724_);
lean_closure_set(v___f_1764_, 10, v___x_1734_);
lean_closure_set(v___f_1764_, 11, v___x_1762_);
lean_closure_set(v___f_1764_, 12, v___x_1754_);
lean_closure_set(v___f_1764_, 13, v___x_1759_);
lean_closure_set(v___f_1764_, 14, v___x_1756_);
lean_closure_set(v___f_1764_, 15, v___x_1758_);
lean_closure_set(v___f_1764_, 16, v___f_1757_);
lean_closure_set(v___f_1764_, 17, v___x_1761_);
lean_closure_set(v___f_1764_, 18, v___x_1760_);
lean_closure_set(v___f_1764_, 19, v___x_1739_);
lean_closure_set(v___f_1764_, 20, v___f_1747_);
lean_closure_set(v___f_1764_, 21, v___f_1763_);
lean_closure_set(v___f_1764_, 22, v_getCurrNamespace_1729_);
v___x_1765_ = lean_apply_4(v_toBind_1728_, lean_box(0), lean_box(0), v_getOpenDecls_1730_, v___f_1764_);
return v___x_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_stx_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1771_, v_inst_1772_, v_inst_1773_, v_inst_1774_, v_inst_1775_, v_inst_1776_, v_inst_1777_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_stx_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object* v_a_1783_, lean_object* v_toPure_1784_, lean_object* v_s_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_a_1783_);
lean_ctor_set(v___x_1786_, 1, v_s_1785_);
v___x_1787_ = lean_apply_2(v_toPure_1784_, lean_box(0), v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object* v_toPure_1788_, lean_object* v_ref_1789_, lean_object* v_inst_1790_, lean_object* v_toBind_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___f_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___f_1793_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1793_, 0, v_a_1792_);
lean_closure_set(v___f_1793_, 1, v_toPure_1788_);
v___x_1794_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1794_, 0, lean_box(0));
lean_closure_set(v___x_1794_, 1, lean_box(0));
lean_closure_set(v___x_1794_, 2, v_ref_1789_);
v___x_1795_ = lean_apply_2(v_inst_1790_, lean_box(0), v___x_1794_);
v___x_1796_ = lean_apply_4(v_toBind_1791_, lean_box(0), lean_box(0), v___x_1795_, v___f_1793_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object* v_toPure_1797_, lean_object* v_inst_1798_, lean_object* v_toBind_1799_, lean_object* v___x_1800_, lean_object* v___x_1801_, lean_object* v___x_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v___f_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v___x_1808_, lean_object* v_nss_1809_, lean_object* v_idStx_1810_, lean_object* v_ref_1811_){
_start:
{
lean_object* v___f_1812_; lean_object* v___x_100__overap_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_inc(v_toBind_1799_);
lean_inc(v_ref_1811_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1812_, 0, v_toPure_1797_);
lean_closure_set(v___f_1812_, 1, v_ref_1811_);
lean_closure_set(v___f_1812_, 2, v_inst_1798_);
lean_closure_set(v___f_1812_, 3, v_toBind_1799_);
v___x_100__overap_1813_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1800_, v___x_1801_, v___x_1802_, v___x_1803_, v___x_1804_, v___f_1805_, v___x_1806_, v___x_1807_, v___x_1808_, v_nss_1809_, v_idStx_1810_);
v___x_1814_ = lean_apply_1(v___x_100__overap_1813_, v_ref_1811_);
v___x_1815_ = lean_apply_4(v_toBind_1799_, lean_box(0), lean_box(0), v___x_1814_, v___f_1812_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object* v_toPure_1816_, lean_object* v_____x_1817_){
_start:
{
lean_object* v_fst_1818_; lean_object* v___x_1819_; 
v_fst_1818_ = lean_ctor_get(v_____x_1817_, 0);
lean_inc(v_fst_1818_);
lean_dec_ref(v_____x_1817_);
v___x_1819_ = lean_apply_2(v_toPure_1816_, lean_box(0), v_fst_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object* v_toApplicative_1820_, lean_object* v_____do__lift_1821_, lean_object* v_inst_1822_, lean_object* v_toBind_1823_, lean_object* v___x_1824_, lean_object* v___x_1825_, lean_object* v___x_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v___f_1829_, lean_object* v___x_1830_, lean_object* v___x_1831_, lean_object* v___x_1832_, lean_object* v_nss_1833_, lean_object* v_idStx_1834_, lean_object* v_____do__lift_1835_){
_start:
{
lean_object* v_toPure_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v_toPure_1836_ = lean_ctor_get(v_toApplicative_1820_, 1);
lean_inc_n(v_toPure_1836_, 2);
lean_dec_ref(v_toApplicative_1820_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_____do__lift_1821_);
lean_ctor_set(v___x_1837_, 1, v_____do__lift_1835_);
v___x_1838_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1838_, 0, lean_box(0));
lean_closure_set(v___x_1838_, 1, lean_box(0));
lean_closure_set(v___x_1838_, 2, v___x_1837_);
lean_inc(v_inst_1822_);
v___x_1839_ = lean_apply_2(v_inst_1822_, lean_box(0), v___x_1838_);
lean_inc_n(v_toBind_1823_, 2);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2), 15, 14);
lean_closure_set(v___f_1840_, 0, v_toPure_1836_);
lean_closure_set(v___f_1840_, 1, v_inst_1822_);
lean_closure_set(v___f_1840_, 2, v_toBind_1823_);
lean_closure_set(v___f_1840_, 3, v___x_1824_);
lean_closure_set(v___f_1840_, 4, v___x_1825_);
lean_closure_set(v___f_1840_, 5, v___x_1826_);
lean_closure_set(v___f_1840_, 6, v___x_1827_);
lean_closure_set(v___f_1840_, 7, v___x_1828_);
lean_closure_set(v___f_1840_, 8, v___f_1829_);
lean_closure_set(v___f_1840_, 9, v___x_1830_);
lean_closure_set(v___f_1840_, 10, v___x_1831_);
lean_closure_set(v___f_1840_, 11, v___x_1832_);
lean_closure_set(v___f_1840_, 12, v_nss_1833_);
lean_closure_set(v___f_1840_, 13, v_idStx_1834_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1841_, 0, v_toPure_1836_);
v___x_1842_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1839_, v___f_1840_);
v___x_1843_ = lean_apply_4(v_toBind_1823_, lean_box(0), lean_box(0), v___x_1842_, v___f_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object* v_toApplicative_1844_, lean_object* v_inst_1845_, lean_object* v_toBind_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v___x_1849_, lean_object* v___x_1850_, lean_object* v___x_1851_, lean_object* v___f_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v___x_1855_, lean_object* v_nss_1856_, lean_object* v_idStx_1857_, lean_object* v_getCurrNamespace_1858_, lean_object* v_____do__lift_1859_){
_start:
{
lean_object* v___f_1860_; lean_object* v___x_1861_; 
lean_inc(v_toBind_1846_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4), 16, 15);
lean_closure_set(v___f_1860_, 0, v_toApplicative_1844_);
lean_closure_set(v___f_1860_, 1, v_____do__lift_1859_);
lean_closure_set(v___f_1860_, 2, v_inst_1845_);
lean_closure_set(v___f_1860_, 3, v_toBind_1846_);
lean_closure_set(v___f_1860_, 4, v___x_1847_);
lean_closure_set(v___f_1860_, 5, v___x_1848_);
lean_closure_set(v___f_1860_, 6, v___x_1849_);
lean_closure_set(v___f_1860_, 7, v___x_1850_);
lean_closure_set(v___f_1860_, 8, v___x_1851_);
lean_closure_set(v___f_1860_, 9, v___f_1852_);
lean_closure_set(v___f_1860_, 10, v___x_1853_);
lean_closure_set(v___f_1860_, 11, v___x_1854_);
lean_closure_set(v___f_1860_, 12, v___x_1855_);
lean_closure_set(v___f_1860_, 13, v_nss_1856_);
lean_closure_set(v___f_1860_, 14, v_idStx_1857_);
v___x_1861_ = lean_apply_4(v_toBind_1846_, lean_box(0), lean_box(0), v_getCurrNamespace_1858_, v___f_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object* v_inst_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_nss_1871_, lean_object* v_idStx_1872_){
_start:
{
lean_object* v_toApplicative_1873_; lean_object* v_toBind_1874_; lean_object* v_getCurrNamespace_1875_; lean_object* v_getOpenDecls_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1907_; 
v_toApplicative_1873_ = lean_ctor_get(v_inst_1862_, 0);
lean_inc_ref(v_toApplicative_1873_);
v_toBind_1874_ = lean_ctor_get(v_inst_1862_, 1);
lean_inc(v_toBind_1874_);
v_getCurrNamespace_1875_ = lean_ctor_get(v_inst_1870_, 0);
v_getOpenDecls_1876_ = lean_ctor_get(v_inst_1870_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_inst_1870_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1878_ = v_inst_1870_;
v_isShared_1879_ = v_isSharedCheck_1907_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_getOpenDecls_1876_);
lean_inc(v_getCurrNamespace_1875_);
lean_dec(v_inst_1870_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1907_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v_getEnv_1881_; lean_object* v_modifyEnv_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1906_; 
lean_inc_ref(v_inst_1862_);
v___x_1880_ = l_StateRefT_x27_instMonad___redArg(v_inst_1862_);
v_getEnv_1881_ = lean_ctor_get(v_inst_1863_, 0);
v_modifyEnv_1882_ = lean_ctor_get(v_inst_1863_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_inst_1863_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1884_ = v_inst_1863_;
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_modifyEnv_1882_);
lean_inc(v_getEnv_1881_);
lean_dec(v_inst_1863_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___f_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
v___f_1887_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1887_, 0, v_modifyEnv_1882_);
lean_closure_set(v___f_1887_, 1, v___x_1886_);
v___x_1888_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1888_, 0, lean_box(0));
lean_closure_set(v___x_1888_, 1, lean_box(0));
lean_closure_set(v___x_1888_, 2, lean_box(0));
lean_closure_set(v___x_1888_, 3, lean_box(0));
lean_closure_set(v___x_1888_, 4, v_getEnv_1881_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 1, v___f_1887_);
lean_ctor_set(v___x_1884_, 0, v___x_1888_);
v___x_1890_ = v___x_1884_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___f_1887_);
v___x_1890_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___f_1891_; lean_object* v___f_1892_; lean_object* v___x_1894_; 
lean_inc_ref(v_inst_1864_);
v___f_1891_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1891_, 0, v_inst_1864_);
v___f_1892_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1892_, 0, v_inst_1864_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___f_1892_);
lean_ctor_set(v___x_1878_, 0, v___f_1891_);
v___x_1894_ = v___x_1878_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___f_1891_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___f_1892_);
v___x_1894_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; 
v___x_1895_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_1896_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1886_, v___x_1895_, v_inst_1865_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1897_, 0, v_inst_1866_);
lean_closure_set(v___f_1897_, 1, v___x_1886_);
lean_inc_ref(v___x_1880_);
lean_inc_ref(v___f_1897_);
v___x_1898_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1897_, v___x_1880_);
v___x_1899_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1886_, v_inst_1868_);
v___x_1900_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1900_, 0, lean_box(0));
lean_closure_set(v___x_1900_, 1, lean_box(0));
lean_closure_set(v___x_1900_, 2, lean_box(0));
lean_closure_set(v___x_1900_, 3, lean_box(0));
lean_closure_set(v___x_1900_, 4, v_inst_1869_);
lean_inc(v_inst_1867_);
v___x_1901_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1862_, v_inst_1867_);
lean_inc(v_toBind_1874_);
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5), 16, 15);
lean_closure_set(v___f_1902_, 0, v_toApplicative_1873_);
lean_closure_set(v___f_1902_, 1, v_inst_1867_);
lean_closure_set(v___f_1902_, 2, v_toBind_1874_);
lean_closure_set(v___f_1902_, 3, v___x_1880_);
lean_closure_set(v___f_1902_, 4, v___x_1890_);
lean_closure_set(v___f_1902_, 5, v___x_1894_);
lean_closure_set(v___f_1902_, 6, v___x_1896_);
lean_closure_set(v___f_1902_, 7, v___x_1898_);
lean_closure_set(v___f_1902_, 8, v___f_1897_);
lean_closure_set(v___f_1902_, 9, v___x_1899_);
lean_closure_set(v___f_1902_, 10, v___x_1900_);
lean_closure_set(v___f_1902_, 11, v___x_1901_);
lean_closure_set(v___f_1902_, 12, v_nss_1871_);
lean_closure_set(v___f_1902_, 13, v_idStx_1872_);
lean_closure_set(v___f_1902_, 14, v_getCurrNamespace_1875_);
v___x_1903_ = lean_apply_4(v_toBind_1874_, lean_box(0), lean_box(0), v_getOpenDecls_1876_, v___f_1902_);
return v___x_1903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object* v_m_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_inst_1914_, lean_object* v_inst_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_nss_1918_, lean_object* v_idStx_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(v_inst_1909_, v_inst_1910_, v_inst_1911_, v_inst_1912_, v_inst_1913_, v_inst_1914_, v_inst_1915_, v_inst_1916_, v_inst_1917_, v_nss_1918_, v_idStx_1919_);
return v___x_1920_;
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
