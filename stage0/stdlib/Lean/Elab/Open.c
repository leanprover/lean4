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
lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__0(lean_object*, lean_object*);
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
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_throwErrorWithNestedErrors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Option_bind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instFunctorOption___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_instMonadResolveNameM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "openOnly"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openHiding"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "openRenaming"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__5 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__5_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__6 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__6_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__7 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__7_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFunctorOption___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__8 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__8_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_map, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__9 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__9_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__9_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__8_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__10 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__10_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__10_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__5_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__6_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__7_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__11 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__11_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_bind, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__12 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__12_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__11_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__12_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__13 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__13_value;
static const lean_array_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__14 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__14_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed__const__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__3_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getId___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1(lean_object* v_declName_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_idStx_56_, lean_object* v_toBind_57_, lean_object* v_toApplicative_58_, lean_object* v_____do__lift_59_){
_start:
{
uint8_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 1;
lean_inc(v_declName_46_);
v___x_61_ = l_Lean_Environment_contains(v_____do__lift_59_, v_declName_46_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v_getRef_63_; lean_object* v_withRef_64_; lean_object* v___x_65_; lean_object* v___f_66_; lean_object* v___x_67_; 
lean_dec_ref(v_toApplicative_58_);
lean_inc_ref(v_inst_48_);
v___x_62_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_62_, 0, v_inst_47_);
lean_ctor_set(v___x_62_, 1, v_inst_48_);
lean_ctor_set(v___x_62_, 2, v_inst_49_);
v_getRef_63_ = lean_ctor_get(v_inst_48_, 0);
lean_inc(v_getRef_63_);
v_withRef_64_ = lean_ctor_get(v_inst_48_, 1);
lean_inc(v_withRef_64_);
lean_dec_ref(v_inst_48_);
v___x_65_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_50_, v_inst_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_inst_55_, v___x_62_, v_declName_46_);
v___f_66_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_66_, 0, v_idStx_56_);
lean_closure_set(v___f_66_, 1, v_withRef_64_);
lean_closure_set(v___f_66_, 2, v___x_65_);
v___x_67_ = lean_apply_4(v_toBind_57_, lean_box(0), lean_box(0), v_getRef_63_, v___f_66_);
return v___x_67_;
}
else
{
lean_object* v_toPure_68_; lean_object* v___x_69_; 
lean_dec(v_toBind_57_);
lean_dec(v_idStx_56_);
lean_dec(v_inst_55_);
lean_dec_ref(v_inst_54_);
lean_dec(v_inst_53_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
lean_dec(v_inst_49_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
v_toPure_68_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_68_);
lean_dec_ref(v_toApplicative_58_);
v___x_69_ = lean_apply_2(v_toPure_68_, lean_box(0), v_declName_46_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_ns_79_, lean_object* v_idStx_80_){
_start:
{
lean_object* v_toApplicative_81_; lean_object* v_toBind_82_; lean_object* v_getEnv_83_; lean_object* v___x_84_; lean_object* v_declName_85_; lean_object* v___f_86_; lean_object* v___x_87_; 
v_toApplicative_81_ = lean_ctor_get(v_inst_70_, 0);
lean_inc_ref(v_toApplicative_81_);
v_toBind_82_ = lean_ctor_get(v_inst_70_, 1);
lean_inc_n(v_toBind_82_, 2);
v_getEnv_83_ = lean_ctor_get(v_inst_71_, 0);
lean_inc(v_getEnv_83_);
v___x_84_ = l_Lean_Syntax_getId(v_idStx_80_);
v_declName_85_ = l_Lean_Name_append(v_ns_79_, v___x_84_);
v___f_86_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__1), 14, 13);
lean_closure_set(v___f_86_, 0, v_declName_85_);
lean_closure_set(v___f_86_, 1, v_inst_72_);
lean_closure_set(v___f_86_, 2, v_inst_73_);
lean_closure_set(v___f_86_, 3, v_inst_74_);
lean_closure_set(v___f_86_, 4, v_inst_70_);
lean_closure_set(v___f_86_, 5, v_inst_78_);
lean_closure_set(v___f_86_, 6, v_inst_71_);
lean_closure_set(v___f_86_, 7, v_inst_77_);
lean_closure_set(v___f_86_, 8, v_inst_76_);
lean_closure_set(v___f_86_, 9, v_inst_75_);
lean_closure_set(v___f_86_, 10, v_idStx_80_);
lean_closure_set(v___f_86_, 11, v_toBind_82_);
lean_closure_set(v___f_86_, 12, v_toApplicative_81_);
v___x_87_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v_getEnv_83_, v___f_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId(lean_object* v_m_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_ns_98_, lean_object* v_idStx_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v_inst_89_, v_inst_90_, v_inst_91_, v_inst_92_, v_inst_93_, v_inst_94_, v_inst_95_, v_inst_96_, v_inst_97_, v_ns_98_, v_idStx_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0(lean_object* v_decl_101_, lean_object* v_s_102_){
_start:
{
lean_object* v_openDecls_103_; lean_object* v_currNamespace_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_114_; 
v_openDecls_103_ = lean_ctor_get(v_s_102_, 0);
v_currNamespace_104_ = lean_ctor_get(v_s_102_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_s_102_);
if (v_isSharedCheck_114_ == 0)
{
v___x_106_ = v_s_102_;
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_currNamespace_104_);
lean_inc(v_openDecls_103_);
lean_dec(v_s_102_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v_decl_101_);
lean_ctor_set(v___x_109_, 1, v_openDecls_103_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_currNamespace_104_);
v___x_111_ = v_reuseFailAlloc_113_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_108_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(lean_object* v_inst_115_, lean_object* v_decl_116_, lean_object* v_a_117_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v_decl_116_);
lean_inc(v_a_117_);
v___x_119_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_119_, 0, lean_box(0));
lean_closure_set(v___x_119_, 1, lean_box(0));
lean_closure_set(v___x_119_, 2, lean_box(0));
lean_closure_set(v___x_119_, 3, v_a_117_);
lean_closure_set(v___x_119_, 4, v___f_118_);
v___x_120_ = lean_apply_2(v_inst_115_, lean_box(0), v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg___boxed(lean_object* v_inst_121_, lean_object* v_decl_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_121_, v_decl_122_, v_a_123_);
lean_dec(v_a_123_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_decl_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_126_, v_decl_127_, v_a_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___boxed(lean_object* v_m_130_, lean_object* v_inst_131_, lean_object* v_decl_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(v_m_130_, v_inst_131_, v_decl_132_, v_a_133_);
lean_dec(v_a_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(lean_object* v_x_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_mkConst(v_x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(lean_object* v_toPure_138_, lean_object* v_p_139_){
_start:
{
lean_object* v_snd_140_; lean_object* v_fst_141_; lean_object* v_snd_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_151_; 
v_snd_140_ = lean_ctor_get(v_p_139_, 1);
lean_inc(v_snd_140_);
lean_dec_ref(v_p_139_);
v_fst_141_ = lean_ctor_get(v_snd_140_, 0);
v_snd_142_ = lean_ctor_get(v_snd_140_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_snd_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_144_ = v_snd_140_;
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snd_142_);
lean_inc(v_fst_141_);
lean_dec(v_snd_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_151_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_fst_141_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_snd_142_);
v___x_147_ = v_reuseFailAlloc_150_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
v___x_149_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(lean_object* v_snd_152_, lean_object* v_fst_153_, lean_object* v_toPure_154_, lean_object* v_declName_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_array_push(v_snd_152_, v_declName_155_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v_fst_153_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(lean_object* v_fst_161_, lean_object* v_snd_162_, lean_object* v_toPure_163_, lean_object* v_ex_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = lean_array_push(v_fst_161_, v_ex_164_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set(v___x_167_, 1, v_snd_162_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_apply_2(v_toPure_163_, lean_box(0), v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(lean_object* v_inst_170_, lean_object* v_toPure_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_idStx_180_, lean_object* v_toBind_181_, lean_object* v___f_182_, lean_object* v_a_183_, lean_object* v_x_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v_tryCatch_188_; lean_object* v___f_189_; lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_fst_186_ = lean_ctor_get(v___y_185_, 0);
lean_inc_n(v_fst_186_, 2);
v_snd_187_ = lean_ctor_get(v___y_185_, 1);
lean_inc_n(v_snd_187_, 2);
lean_dec_ref(v___y_185_);
v_tryCatch_188_ = lean_ctor_get(v_inst_170_, 1);
lean_inc(v_tryCatch_188_);
lean_inc(v_toPure_171_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2), 4, 3);
lean_closure_set(v___f_189_, 0, v_snd_187_);
lean_closure_set(v___f_189_, 1, v_fst_186_);
lean_closure_set(v___f_189_, 2, v_toPure_171_);
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_190_, 0, v_fst_186_);
lean_closure_set(v___f_190_, 1, v_snd_187_);
lean_closure_set(v___f_190_, 2, v_toPure_171_);
v___x_191_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v_inst_172_, v_inst_173_, v_inst_170_, v_inst_174_, v_inst_175_, v_inst_176_, v_inst_177_, v_inst_178_, v_inst_179_, v_a_183_, v_idStx_180_);
lean_inc(v_toBind_181_);
v___x_192_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v___x_191_, v___f_189_);
v___x_193_ = lean_apply_3(v_tryCatch_188_, lean_box(0), v___x_192_, v___f_190_);
v___x_194_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v___x_193_, v___f_182_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(lean_object* v_snd_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_idStx_225_, lean_object* v___f_226_, lean_object* v_inst_227_, lean_object* v_toBind_228_, lean_object* v___x_229_, lean_object* v_toPure_230_, lean_object* v_____r_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_array_get_size(v_snd_221_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_dec_eq(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_getRef_237_; lean_object* v_withRef_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_toPure_230_);
lean_inc_ref(v_inst_223_);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v_inst_222_);
lean_ctor_set(v___x_235_, 1, v_inst_223_);
lean_ctor_set(v___x_235_, 2, v_inst_224_);
v___x_236_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_getRef_237_ = lean_ctor_get(v_inst_223_, 0);
v_withRef_238_ = lean_ctor_get(v_inst_223_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_inst_223_);
if (v_isSharedCheck_262_ == 0)
{
v___x_240_ = v_inst_223_;
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_withRef_238_);
lean_inc(v_getRef_237_);
lean_dec(v_inst_223_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
size_t v_sz_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v_sz_242_ = lean_array_size(v_snd_221_);
v___x_243_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
v___x_244_ = l_Lean_Syntax_getId(v_idStx_225_);
v___x_245_ = l_Lean_MessageData_ofName(v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 7);
lean_ctor_set(v___x_240_, 1, v___x_245_);
lean_ctor_set(v___x_240_, 0, v___x_243_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_261_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; size_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v___x_248_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((size_t)0ULL);
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_236_, v___f_226_, v_sz_242_, v___x_250_, v_snd_221_);
v___x_252_ = lean_array_to_list(v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14));
v___x_254_ = lean_box(0);
v___x_255_ = l_List_mapTR_loop___redArg(v___x_253_, v___x_252_, v___x_254_);
v___x_256_ = l_Lean_MessageData_ofList(v___x_255_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_249_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___redArg(v_inst_227_, v___x_235_, v___x_257_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_259_, 0, v_idStx_225_);
lean_closure_set(v___f_259_, 1, v_withRef_238_);
lean_closure_set(v___f_259_, 2, v___x_258_);
v___x_260_ = lean_apply_4(v_toBind_228_, lean_box(0), lean_box(0), v_getRef_237_, v___f_259_);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec(v_toBind_228_);
lean_dec_ref(v_inst_227_);
lean_dec_ref(v___f_226_);
lean_dec(v_idStx_225_);
lean_dec(v_inst_224_);
lean_dec_ref(v_inst_223_);
lean_dec_ref(v_inst_222_);
v___x_263_ = lean_array_fget(v_snd_221_, v___x_229_);
lean_dec(v_snd_221_);
v___x_264_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_263_);
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(lean_object* v_snd_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_idStx_269_, lean_object* v___f_270_, lean_object* v_inst_271_, lean_object* v_toBind_272_, lean_object* v___x_273_, lean_object* v_toPure_274_, lean_object* v_____r_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_265_, v_inst_266_, v_inst_267_, v_inst_268_, v_idStx_269_, v___f_270_, v_inst_271_, v_toBind_272_, v___x_273_, v_toPure_274_, v_____r_275_);
lean_dec(v___x_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(lean_object* v___f_277_, lean_object* v_____r_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_apply_1(v___f_277_, v_____r_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(lean_object* v_idStx_280_, lean_object* v_withRef_281_, lean_object* v___y_282_, lean_object* v_oldRef_283_){
_start:
{
lean_object* v_ref_284_; lean_object* v___x_285_; 
v_ref_284_ = l_Lean_replaceRef(v_idStx_280_, v_oldRef_283_);
v___x_285_ = lean_apply_3(v_withRef_281_, lean_box(0), v_ref_284_, v___y_282_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(lean_object* v_idStx_286_, lean_object* v_withRef_287_, lean_object* v___y_288_, lean_object* v_oldRef_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(v_idStx_286_, v_withRef_287_, v___y_288_, v_oldRef_289_);
lean_dec(v_oldRef_289_);
lean_dec(v_idStx_286_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1));
v___x_295_ = l_Lean_MessageData_ofFormat(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_idStx_299_, lean_object* v___f_300_, lean_object* v_inst_301_, lean_object* v_toBind_302_, lean_object* v___x_303_, lean_object* v_toPure_304_, lean_object* v_nss_305_, lean_object* v_inst_306_, lean_object* v_____s_307_){
_start:
{
lean_object* v_fst_308_; lean_object* v_snd_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_fst_308_ = lean_ctor_get(v_____s_307_, 0);
lean_inc(v_fst_308_);
v_snd_309_ = lean_ctor_get(v_____s_307_, 1);
lean_inc_n(v_snd_309_, 2);
lean_dec_ref(v_____s_307_);
lean_inc(v_toPure_304_);
lean_inc(v___x_303_);
lean_inc(v_toBind_302_);
lean_inc_ref(v_inst_301_);
lean_inc_ref(v___f_300_);
lean_inc(v_idStx_299_);
lean_inc(v_inst_298_);
lean_inc_ref(v_inst_297_);
lean_inc_ref(v_inst_296_);
v___f_310_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_310_, 0, v_snd_309_);
lean_closure_set(v___f_310_, 1, v_inst_296_);
lean_closure_set(v___f_310_, 2, v_inst_297_);
lean_closure_set(v___f_310_, 3, v_inst_298_);
lean_closure_set(v___f_310_, 4, v_idStx_299_);
lean_closure_set(v___f_310_, 5, v___f_300_);
lean_closure_set(v___f_310_, 6, v_inst_301_);
lean_closure_set(v___f_310_, 7, v_toBind_302_);
lean_closure_set(v___f_310_, 8, v___x_303_);
lean_closure_set(v___f_310_, 9, v_toPure_304_);
v___x_311_ = lean_array_get_size(v_fst_308_);
v___x_312_ = l_List_lengthTR___redArg(v_nss_305_);
v___x_313_ = lean_nat_dec_eq(v___x_311_, v___x_312_);
lean_dec(v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec_ref(v___f_310_);
lean_dec(v_fst_308_);
lean_dec_ref(v_inst_306_);
v___x_314_ = lean_box(0);
v___x_315_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_309_, v_inst_296_, v_inst_297_, v_inst_298_, v_idStx_299_, v___f_300_, v_inst_301_, v_toBind_302_, v___x_303_, v_toPure_304_, v___x_314_);
lean_dec(v___x_303_);
return v___x_315_;
}
else
{
lean_object* v___f_316_; lean_object* v___y_318_; lean_object* v___x_324_; uint8_t v___x_325_; 
lean_dec(v_snd_309_);
lean_dec(v_toPure_304_);
lean_dec_ref(v___f_300_);
v___f_316_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5), 2, 1);
lean_closure_set(v___f_316_, 0, v___f_310_);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_dec_eq(v___x_311_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v___x_303_);
lean_inc_ref(v_inst_297_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_inst_296_);
lean_ctor_set(v___x_326_, 1, v_inst_297_);
lean_ctor_set(v___x_326_, 2, v_inst_298_);
v___x_327_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
v___x_328_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v___x_326_, v_inst_301_, v_inst_306_, v___x_327_, v_fst_308_);
v___y_318_ = v___x_328_;
goto v___jp_317_;
}
else
{
lean_object* v_throw_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec_ref(v_inst_306_);
lean_dec_ref(v_inst_301_);
lean_dec(v_inst_298_);
v_throw_329_ = lean_ctor_get(v_inst_296_, 0);
lean_inc(v_throw_329_);
lean_dec_ref(v_inst_296_);
v___x_330_ = lean_array_fget(v_fst_308_, v___x_303_);
lean_dec(v___x_303_);
lean_dec(v_fst_308_);
v___x_331_ = lean_apply_2(v_throw_329_, lean_box(0), v___x_330_);
v___y_318_ = v___x_331_;
goto v___jp_317_;
}
v___jp_317_:
{
lean_object* v_getRef_319_; lean_object* v_withRef_320_; lean_object* v___f_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_getRef_319_ = lean_ctor_get(v_inst_297_, 0);
lean_inc(v_getRef_319_);
v_withRef_320_ = lean_ctor_get(v_inst_297_, 1);
lean_inc(v_withRef_320_);
lean_dec_ref(v_inst_297_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_321_, 0, v_idStx_299_);
lean_closure_set(v___f_321_, 1, v_withRef_320_);
lean_closure_set(v___f_321_, 2, v___y_318_);
lean_inc(v_toBind_302_);
v___x_322_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v_getRef_319_, v___f_321_);
v___x_323_ = lean_apply_4(v_toBind_302_, lean_box(0), lean_box(0), v___x_322_, v___f_316_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed(lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_idStx_335_, lean_object* v___f_336_, lean_object* v_inst_337_, lean_object* v_toBind_338_, lean_object* v___x_339_, lean_object* v_toPure_340_, lean_object* v_nss_341_, lean_object* v_inst_342_, lean_object* v_____s_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(v_inst_332_, v_inst_333_, v_inst_334_, v_idStx_335_, v___f_336_, v_inst_337_, v_toBind_338_, v___x_339_, v_toPure_340_, v_nss_341_, v_inst_342_, v_____s_343_);
lean_dec(v_nss_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_nss_359_, lean_object* v_idStx_360_){
_start:
{
lean_object* v_toApplicative_361_; lean_object* v_toBind_362_; lean_object* v_toPure_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_toApplicative_361_ = lean_ctor_get(v_inst_350_, 0);
v_toBind_362_ = lean_ctor_get(v_inst_350_, 1);
lean_inc_n(v_toBind_362_, 3);
v_toPure_363_ = lean_ctor_get(v_toApplicative_361_, 1);
v___f_364_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0));
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2));
lean_inc_n(v_toPure_363_, 3);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_367_, 0, v_toPure_363_);
lean_inc(v_idStx_360_);
lean_inc_ref(v_inst_356_);
lean_inc(v_inst_354_);
lean_inc_ref(v_inst_353_);
lean_inc_ref_n(v_inst_350_, 2);
lean_inc_ref(v_inst_352_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4), 16, 13);
lean_closure_set(v___f_368_, 0, v_inst_352_);
lean_closure_set(v___f_368_, 1, v_toPure_363_);
lean_closure_set(v___f_368_, 2, v_inst_350_);
lean_closure_set(v___f_368_, 3, v_inst_351_);
lean_closure_set(v___f_368_, 4, v_inst_353_);
lean_closure_set(v___f_368_, 5, v_inst_354_);
lean_closure_set(v___f_368_, 6, v_inst_355_);
lean_closure_set(v___f_368_, 7, v_inst_356_);
lean_closure_set(v___f_368_, 8, v_inst_357_);
lean_closure_set(v___f_368_, 9, v_inst_358_);
lean_closure_set(v___f_368_, 10, v_idStx_360_);
lean_closure_set(v___f_368_, 11, v_toBind_362_);
lean_closure_set(v___f_368_, 12, v___f_367_);
lean_inc(v_nss_359_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed), 12, 11);
lean_closure_set(v___f_369_, 0, v_inst_352_);
lean_closure_set(v___f_369_, 1, v_inst_353_);
lean_closure_set(v___f_369_, 2, v_inst_354_);
lean_closure_set(v___f_369_, 3, v_idStx_360_);
lean_closure_set(v___f_369_, 4, v___f_364_);
lean_closure_set(v___f_369_, 5, v_inst_350_);
lean_closure_set(v___f_369_, 6, v_toBind_362_);
lean_closure_set(v___f_369_, 7, v___x_365_);
lean_closure_set(v___f_369_, 8, v_toPure_363_);
lean_closure_set(v___f_369_, 9, v_nss_359_);
lean_closure_set(v___f_369_, 10, v_inst_356_);
v___x_370_ = l_List_forIn_x27_loop___redArg(v_inst_350_, v___f_368_, v_nss_359_, v___x_366_);
lean_dec(v_nss_359_);
v___x_371_ = lean_apply_4(v_toBind_362_, lean_box(0), lean_box(0), v___x_370_, v___f_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(lean_object* v_m_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_nss_382_, lean_object* v_idStx_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v_inst_373_, v_inst_374_, v_inst_375_, v_inst_376_, v_inst_377_, v_inst_378_, v_inst_379_, v_inst_380_, v_inst_381_, v_nss_382_, v_idStx_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0(lean_object* v_toApplicative_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_openDecls_387_; lean_object* v_toPure_388_; lean_object* v___x_389_; 
v_openDecls_387_ = lean_ctor_get(v_a_386_, 0);
lean_inc(v_openDecls_387_);
lean_dec_ref(v_a_386_);
v_toPure_388_ = lean_ctor_get(v_toApplicative_385_, 1);
lean_inc(v_toPure_388_);
lean_dec_ref(v_toApplicative_385_);
v___x_389_ = lean_apply_2(v_toPure_388_, lean_box(0), v_openDecls_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(lean_object* v_inst_390_, lean_object* v_toBind_391_, lean_object* v___f_392_, lean_object* v_____r_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc(v___y_394_);
v___x_395_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_395_, 0, lean_box(0));
lean_closure_set(v___x_395_, 1, lean_box(0));
lean_closure_set(v___x_395_, 2, v___y_394_);
v___x_396_ = lean_apply_2(v_inst_390_, lean_box(0), v___x_395_);
v___x_397_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v___x_396_, v___f_392_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed(lean_object* v_inst_398_, lean_object* v_toBind_399_, lean_object* v___f_400_, lean_object* v_____r_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(v_inst_398_, v_toBind_399_, v___f_400_, v_____r_401_, v___y_402_);
lean_dec(v___y_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(lean_object* v_x_404_){
_start:
{
lean_object* v_snd_405_; 
v_snd_405_ = lean_ctor_get(v_x_404_, 1);
lean_inc(v_snd_405_);
return v_snd_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_406_);
lean_dec_ref(v_x_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(lean_object* v_x_408_){
_start:
{
lean_object* v_fst_409_; 
v_fst_409_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_fst_409_);
return v_fst_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_410_);
lean_dec_ref(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(lean_object* v_a_412_, lean_object* v_toPure_413_, lean_object* v_s_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_a_412_);
lean_ctor_set(v___x_415_, 1, v_s_414_);
v___x_416_ = lean_apply_2(v_toPure_413_, lean_box(0), v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(lean_object* v_toPure_417_, lean_object* v_ref_418_, lean_object* v_inst_419_, lean_object* v_toBind_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4), 3, 2);
lean_closure_set(v___f_422_, 0, v_a_421_);
lean_closure_set(v___f_422_, 1, v_toPure_417_);
v___x_423_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_423_, 0, lean_box(0));
lean_closure_set(v___x_423_, 1, lean_box(0));
lean_closure_set(v___x_423_, 2, v_ref_418_);
v___x_424_ = lean_apply_2(v_inst_419_, lean_box(0), v___x_423_);
v___x_425_ = lean_apply_4(v_toBind_420_, lean_box(0), lean_box(0), v___x_424_, v___f_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(lean_object* v___f_426_, lean_object* v_ref_427_, lean_object* v_a_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_apply_2(v___f_426_, v_a_428_, v_ref_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(lean_object* v___f_430_, lean_object* v_ref_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_2(v___f_430_, v___x_433_, v_ref_431_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0));
v___x_443_ = l_Lean_Name_mkStr4(v___x_436_, v___x_437_, v___x_438_, v___x_442_);
lean_inc(v_x_441_);
v___x_444_ = l_Lean_Syntax_isOfKind(v_x_441_, v___x_443_);
lean_dec(v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_x_441_);
v___x_445_ = lean_box(0);
return v___x_445_;
}
else
{
lean_object* v_froms_446_; lean_object* v_tos_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_froms_446_ = l_Lean_Syntax_getArg(v_x_441_, v___x_439_);
v_tos_447_ = l_Lean_Syntax_getArg(v_x_441_, v___x_440_);
lean_dec(v_x_441_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_froms_446_);
lean_ctor_set(v___x_448_, 1, v_tos_447_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v___x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(v___x_450_, v___x_451_, v___x_452_, v___x_453_, v___x_454_, v_x_455_);
lean_dec(v___x_454_);
lean_dec(v___x_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(lean_object* v___x_457_, lean_object* v_toPure_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_457_);
v___x_461_ = lean_apply_2(v_toPure_458_, lean_box(0), v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(lean_object* v_snd_462_, lean_object* v_a_463_, lean_object* v_inst_464_, lean_object* v_toBind_465_, lean_object* v___f_466_, lean_object* v_____r_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = l_Lean_Syntax_getId(v_snd_462_);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_a_463_);
v___x_471_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_464_, v___x_470_, v___y_468_);
v___x_472_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_471_, v___f_466_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(lean_object* v_snd_473_, lean_object* v_a_474_, lean_object* v_inst_475_, lean_object* v_toBind_476_, lean_object* v___f_477_, lean_object* v_____r_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(v_snd_473_, v_a_474_, v_inst_475_, v_toBind_476_, v___f_477_, v_____r_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec(v_snd_473_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object* v___f_481_, lean_object* v___y_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_484_; 
lean_inc(v___y_482_);
v___x_484_ = lean_apply_2(v___f_481_, v_a_483_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(lean_object* v___f_485_, lean_object* v___y_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v___f_485_, v___y_486_, v_a_487_);
lean_dec(v___y_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v_snd_493_, lean_object* v_a_494_, lean_object* v___x_495_, lean_object* v___y_496_, lean_object* v_toBind_497_, lean_object* v___f_498_, lean_object* v_a_499_){
_start:
{
lean_object* v___x_7212__overap_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_7212__overap_500_ = l_Lean_Elab_addConstInfo___redArg(v___x_489_, v___x_490_, v___x_491_, v___x_492_, v_snd_493_, v_a_494_, v___x_495_);
lean_inc(v___y_496_);
v___x_501_ = lean_apply_1(v___x_7212__overap_500_, v___y_496_);
v___x_502_ = lean_apply_4(v_toBind_497_, lean_box(0), lean_box(0), v___x_501_, v___f_498_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v___x_506_, lean_object* v_snd_507_, lean_object* v_a_508_, lean_object* v___x_509_, lean_object* v___y_510_, lean_object* v_toBind_511_, lean_object* v___f_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(v___x_503_, v___x_504_, v___x_505_, v___x_506_, v_snd_507_, v_a_508_, v___x_509_, v___y_510_, v_toBind_511_, v___f_512_, v_a_513_);
lean_dec(v___y_510_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object* v___f_515_, lean_object* v___x_516_, lean_object* v___y_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_snd_522_, lean_object* v_a_523_, lean_object* v_toBind_524_, lean_object* v___f_525_, lean_object* v_fst_526_, lean_object* v_a_527_){
_start:
{
uint8_t v_enabled_528_; 
v_enabled_528_ = lean_ctor_get_uint8(v_a_527_, sizeof(void*)*3);
if (v_enabled_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v_fst_526_);
lean_dec(v___f_525_);
lean_dec(v_toBind_524_);
lean_dec(v_a_523_);
lean_dec(v_snd_522_);
lean_dec_ref(v___x_521_);
lean_dec_ref(v___x_520_);
lean_dec_ref(v___x_519_);
lean_dec_ref(v___x_518_);
lean_inc(v___y_517_);
v___x_529_ = lean_apply_2(v___f_515_, v___x_516_, v___y_517_);
return v___x_529_;
}
else
{
lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_7227__overap_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v___f_515_);
v___x_530_ = lean_box(0);
lean_inc(v_toBind_524_);
lean_inc_n(v___y_517_, 2);
lean_inc(v_a_523_);
lean_inc_ref(v___x_521_);
lean_inc_ref(v___x_520_);
lean_inc_ref(v___x_519_);
lean_inc_ref(v___x_518_);
v___f_531_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed), 11, 10);
lean_closure_set(v___f_531_, 0, v___x_518_);
lean_closure_set(v___f_531_, 1, v___x_519_);
lean_closure_set(v___f_531_, 2, v___x_520_);
lean_closure_set(v___f_531_, 3, v___x_521_);
lean_closure_set(v___f_531_, 4, v_snd_522_);
lean_closure_set(v___f_531_, 5, v_a_523_);
lean_closure_set(v___f_531_, 6, v___x_530_);
lean_closure_set(v___f_531_, 7, v___y_517_);
lean_closure_set(v___f_531_, 8, v_toBind_524_);
lean_closure_set(v___f_531_, 9, v___f_525_);
v___x_7227__overap_532_ = l_Lean_Elab_addConstInfo___redArg(v___x_518_, v___x_519_, v___x_520_, v___x_521_, v_fst_526_, v_a_523_, v___x_530_);
v___x_533_ = lean_apply_1(v___x_7227__overap_532_, v___y_517_);
v___x_534_ = lean_apply_4(v_toBind_524_, lean_box(0), lean_box(0), v___x_533_, v___f_531_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object* v___f_535_, lean_object* v___x_536_, lean_object* v___y_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v_snd_542_, lean_object* v_a_543_, lean_object* v_toBind_544_, lean_object* v___f_545_, lean_object* v_fst_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(v___f_535_, v___x_536_, v___y_537_, v___x_538_, v___x_539_, v___x_540_, v___x_541_, v_snd_542_, v_a_543_, v_toBind_544_, v___f_545_, v_fst_546_, v_a_547_);
lean_dec_ref(v_a_547_);
lean_dec(v___y_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object* v___x_549_, lean_object* v_inst_550_, lean_object* v_snd_551_, lean_object* v_inst_552_, lean_object* v_toBind_553_, lean_object* v___f_554_, lean_object* v___y_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_fst_560_, lean_object* v_a_561_){
_start:
{
lean_object* v___x_562_; lean_object* v_getInfoState_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; 
lean_inc_ref(v_inst_550_);
v___x_562_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_549_, v_inst_550_);
v_getInfoState_563_ = lean_ctor_get(v_inst_550_, 0);
lean_inc(v_getInfoState_563_);
lean_dec_ref(v_inst_550_);
lean_inc_n(v_toBind_553_, 2);
lean_inc(v_a_561_);
lean_inc(v_snd_551_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_564_, 0, v_snd_551_);
lean_closure_set(v___f_564_, 1, v_a_561_);
lean_closure_set(v___f_564_, 2, v_inst_552_);
lean_closure_set(v___f_564_, 3, v_toBind_553_);
lean_closure_set(v___f_564_, 4, v___f_554_);
lean_inc_n(v___y_555_, 2);
lean_inc_ref(v___f_564_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_565_, 0, v___f_564_);
lean_closure_set(v___f_565_, 1, v___y_555_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_566_, 0, v___f_564_);
lean_closure_set(v___f_566_, 1, v___x_556_);
lean_closure_set(v___f_566_, 2, v___y_555_);
lean_closure_set(v___f_566_, 3, v___x_557_);
lean_closure_set(v___f_566_, 4, v___x_562_);
lean_closure_set(v___f_566_, 5, v___x_558_);
lean_closure_set(v___f_566_, 6, v___x_559_);
lean_closure_set(v___f_566_, 7, v_snd_551_);
lean_closure_set(v___f_566_, 8, v_a_561_);
lean_closure_set(v___f_566_, 9, v_toBind_553_);
lean_closure_set(v___f_566_, 10, v___f_565_);
lean_closure_set(v___f_566_, 11, v_fst_560_);
v___x_567_ = lean_apply_4(v_toBind_553_, lean_box(0), lean_box(0), v_getInfoState_563_, v___f_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(lean_object* v___x_568_, lean_object* v_inst_569_, lean_object* v_snd_570_, lean_object* v_inst_571_, lean_object* v_toBind_572_, lean_object* v___f_573_, lean_object* v___y_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v___x_577_, lean_object* v___x_578_, lean_object* v_fst_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(v___x_568_, v_inst_569_, v_snd_570_, v_inst_571_, v_toBind_572_, v___f_573_, v___y_574_, v___x_575_, v___x_576_, v___x_577_, v___x_578_, v_fst_579_, v_a_580_);
lean_dec(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v___x_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_toBind_585_, lean_object* v___f_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___f_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___f_605_; lean_object* v___x_7266__overap_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
lean_inc_n(v_fst_603_, 2);
v_snd_604_ = lean_ctor_get(v_a_599_, 1);
lean_inc(v_snd_604_);
lean_dec_ref(v_a_599_);
lean_inc_ref(v___x_589_);
lean_inc_ref(v___x_588_);
lean_inc_n(v___y_602_, 2);
lean_inc(v_toBind_585_);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_605_, 0, v___x_582_);
lean_closure_set(v___f_605_, 1, v_inst_583_);
lean_closure_set(v___f_605_, 2, v_snd_604_);
lean_closure_set(v___f_605_, 3, v_inst_584_);
lean_closure_set(v___f_605_, 4, v_toBind_585_);
lean_closure_set(v___f_605_, 5, v___f_586_);
lean_closure_set(v___f_605_, 6, v___y_602_);
lean_closure_set(v___f_605_, 7, v___x_587_);
lean_closure_set(v___f_605_, 8, v___x_588_);
lean_closure_set(v___f_605_, 9, v___x_589_);
lean_closure_set(v___f_605_, 10, v___x_590_);
lean_closure_set(v___f_605_, 11, v_fst_603_);
v___x_7266__overap_606_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_588_, v___x_589_, v___x_591_, v___x_592_, v___x_593_, v___f_594_, v___x_595_, v___x_596_, v___x_597_, v_a_598_, v_fst_603_);
v___x_607_ = lean_apply_1(v___x_7266__overap_606_, v___y_602_);
v___x_608_ = lean_apply_4(v_toBind_585_, lean_box(0), lean_box(0), v___x_607_, v___f_605_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_609_ = _args[0];
lean_object* v_inst_610_ = _args[1];
lean_object* v_inst_611_ = _args[2];
lean_object* v_toBind_612_ = _args[3];
lean_object* v___f_613_ = _args[4];
lean_object* v___x_614_ = _args[5];
lean_object* v___x_615_ = _args[6];
lean_object* v___x_616_ = _args[7];
lean_object* v___x_617_ = _args[8];
lean_object* v___x_618_ = _args[9];
lean_object* v___x_619_ = _args[10];
lean_object* v___x_620_ = _args[11];
lean_object* v___f_621_ = _args[12];
lean_object* v___x_622_ = _args[13];
lean_object* v___x_623_ = _args[14];
lean_object* v___x_624_ = _args[15];
lean_object* v_a_625_ = _args[16];
lean_object* v_a_626_ = _args[17];
lean_object* v_x_627_ = _args[18];
lean_object* v___y_628_ = _args[19];
lean_object* v___y_629_ = _args[20];
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v___x_609_, v_inst_610_, v_inst_611_, v_toBind_612_, v___f_613_, v___x_614_, v___x_615_, v___x_616_, v___x_617_, v___x_618_, v___x_619_, v___x_620_, v___f_621_, v___x_622_, v___x_623_, v___x_624_, v_a_625_, v_a_626_, v_x_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_froms_631_, lean_object* v_tos_632_, lean_object* v_toPure_633_, lean_object* v___x_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_toBind_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v___f_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_a_648_, size_t v___x_649_, lean_object* v_ref_650_, lean_object* v___f_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___f_655_; lean_object* v___f_656_; size_t v_sz_657_; lean_object* v___x_7287__overap_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_653_ = l_Array_zip___redArg(v_froms_631_, v_tos_632_);
v___x_654_ = lean_box(0);
v___f_655_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_655_, 0, v___x_654_);
lean_closure_set(v___f_655_, 1, v_toPure_633_);
lean_inc_ref(v___x_638_);
lean_inc(v_toBind_637_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 21, 17);
lean_closure_set(v___f_656_, 0, v___x_634_);
lean_closure_set(v___f_656_, 1, v_inst_635_);
lean_closure_set(v___f_656_, 2, v_inst_636_);
lean_closure_set(v___f_656_, 3, v_toBind_637_);
lean_closure_set(v___f_656_, 4, v___f_655_);
lean_closure_set(v___f_656_, 5, v___x_654_);
lean_closure_set(v___f_656_, 6, v___x_638_);
lean_closure_set(v___f_656_, 7, v___x_639_);
lean_closure_set(v___f_656_, 8, v___x_640_);
lean_closure_set(v___f_656_, 9, v___x_641_);
lean_closure_set(v___f_656_, 10, v___x_642_);
lean_closure_set(v___f_656_, 11, v___x_643_);
lean_closure_set(v___f_656_, 12, v___f_644_);
lean_closure_set(v___f_656_, 13, v___x_645_);
lean_closure_set(v___f_656_, 14, v___x_646_);
lean_closure_set(v___f_656_, 15, v___x_647_);
lean_closure_set(v___f_656_, 16, v_a_648_);
v_sz_657_ = lean_array_size(v___x_653_);
v___x_7287__overap_658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_638_, v___x_653_, v___f_656_, v_sz_657_, v___x_649_, v___x_654_);
v___x_659_ = lean_apply_1(v___x_7287__overap_658_, v_ref_650_);
v___x_660_ = lean_apply_4(v_toBind_637_, lean_box(0), lean_box(0), v___x_659_, v___f_651_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_froms_661_ = _args[0];
lean_object* v_tos_662_ = _args[1];
lean_object* v_toPure_663_ = _args[2];
lean_object* v___x_664_ = _args[3];
lean_object* v_inst_665_ = _args[4];
lean_object* v_inst_666_ = _args[5];
lean_object* v_toBind_667_ = _args[6];
lean_object* v___x_668_ = _args[7];
lean_object* v___x_669_ = _args[8];
lean_object* v___x_670_ = _args[9];
lean_object* v___x_671_ = _args[10];
lean_object* v___x_672_ = _args[11];
lean_object* v___x_673_ = _args[12];
lean_object* v___f_674_ = _args[13];
lean_object* v___x_675_ = _args[14];
lean_object* v___x_676_ = _args[15];
lean_object* v___x_677_ = _args[16];
lean_object* v_a_678_ = _args[17];
lean_object* v___x_679_ = _args[18];
lean_object* v_ref_680_ = _args[19];
lean_object* v___f_681_ = _args[20];
lean_object* v_a_682_ = _args[21];
_start:
{
size_t v___x_8249__boxed_683_; lean_object* v_res_684_; 
v___x_8249__boxed_683_ = lean_unbox_usize(v___x_679_);
lean_dec(v___x_679_);
v_res_684_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_661_, v_tos_662_, v_toPure_663_, v___x_664_, v_inst_665_, v_inst_666_, v_toBind_667_, v___x_668_, v___x_669_, v___x_670_, v___x_671_, v___x_672_, v___x_673_, v___f_674_, v___x_675_, v___x_676_, v___x_677_, v_a_678_, v___x_8249__boxed_683_, v_ref_680_, v___f_681_, v_a_682_);
lean_dec_ref(v_tos_662_);
lean_dec_ref(v_froms_661_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object* v_inst_685_, lean_object* v___x_686_, lean_object* v_inst_687_, lean_object* v_froms_688_, lean_object* v_tos_689_, lean_object* v_toPure_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_toBind_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v___f_700_, lean_object* v___x_701_, size_t v___x_702_, lean_object* v_ref_703_, lean_object* v___f_704_, lean_object* v___x_705_, lean_object* v_nsStx_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_7309__overap_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_708_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_708_, 0, lean_box(0));
lean_closure_set(v___x_708_, 1, lean_box(0));
lean_closure_set(v___x_708_, 2, lean_box(0));
lean_closure_set(v___x_708_, 3, lean_box(0));
lean_closure_set(v___x_708_, 4, v_inst_685_);
lean_inc(v___x_686_);
v___x_709_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_686_, v_inst_687_);
v___x_710_ = lean_box_usize(v___x_702_);
lean_inc(v_ref_703_);
lean_inc(v_a_707_);
lean_inc_ref(v___x_701_);
lean_inc_ref(v___x_708_);
lean_inc_ref(v___x_709_);
lean_inc(v___f_700_);
lean_inc_ref(v___x_695_);
lean_inc_ref(v___x_694_);
lean_inc(v_toBind_693_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 22, 21);
lean_closure_set(v___f_711_, 0, v_froms_688_);
lean_closure_set(v___f_711_, 1, v_tos_689_);
lean_closure_set(v___f_711_, 2, v_toPure_690_);
lean_closure_set(v___f_711_, 3, v___x_686_);
lean_closure_set(v___f_711_, 4, v_inst_691_);
lean_closure_set(v___f_711_, 5, v_inst_692_);
lean_closure_set(v___f_711_, 6, v_toBind_693_);
lean_closure_set(v___f_711_, 7, v___x_694_);
lean_closure_set(v___f_711_, 8, v___x_695_);
lean_closure_set(v___f_711_, 9, v___x_696_);
lean_closure_set(v___f_711_, 10, v___x_697_);
lean_closure_set(v___f_711_, 11, v___x_698_);
lean_closure_set(v___f_711_, 12, v___x_699_);
lean_closure_set(v___f_711_, 13, v___f_700_);
lean_closure_set(v___f_711_, 14, v___x_709_);
lean_closure_set(v___f_711_, 15, v___x_708_);
lean_closure_set(v___f_711_, 16, v___x_701_);
lean_closure_set(v___f_711_, 17, v_a_707_);
lean_closure_set(v___f_711_, 18, v___x_710_);
lean_closure_set(v___f_711_, 19, v_ref_703_);
lean_closure_set(v___f_711_, 20, v___f_704_);
v___x_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_707_);
lean_ctor_set(v___x_712_, 1, v___x_705_);
v___x_7309__overap_713_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_694_, v___x_695_, v___x_708_, v___x_709_, v___f_700_, v___x_701_, v_nsStx_706_, v___x_712_);
v___x_714_ = lean_apply_1(v___x_7309__overap_713_, v_ref_703_);
v___x_715_ = lean_apply_4(v_toBind_693_, lean_box(0), lean_box(0), v___x_714_, v___f_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_inst_716_ = _args[0];
lean_object* v___x_717_ = _args[1];
lean_object* v_inst_718_ = _args[2];
lean_object* v_froms_719_ = _args[3];
lean_object* v_tos_720_ = _args[4];
lean_object* v_toPure_721_ = _args[5];
lean_object* v_inst_722_ = _args[6];
lean_object* v_inst_723_ = _args[7];
lean_object* v_toBind_724_ = _args[8];
lean_object* v___x_725_ = _args[9];
lean_object* v___x_726_ = _args[10];
lean_object* v___x_727_ = _args[11];
lean_object* v___x_728_ = _args[12];
lean_object* v___x_729_ = _args[13];
lean_object* v___x_730_ = _args[14];
lean_object* v___f_731_ = _args[15];
lean_object* v___x_732_ = _args[16];
lean_object* v___x_733_ = _args[17];
lean_object* v_ref_734_ = _args[18];
lean_object* v___f_735_ = _args[19];
lean_object* v___x_736_ = _args[20];
lean_object* v_nsStx_737_ = _args[21];
lean_object* v_a_738_ = _args[22];
_start:
{
size_t v___x_8306__boxed_739_; lean_object* v_res_740_; 
v___x_8306__boxed_739_ = lean_unbox_usize(v___x_733_);
lean_dec(v___x_733_);
v_res_740_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v_inst_716_, v___x_717_, v_inst_718_, v_froms_719_, v_tos_720_, v_toPure_721_, v_inst_722_, v_inst_723_, v_toBind_724_, v___x_725_, v___x_726_, v___x_727_, v___x_728_, v___x_729_, v___x_730_, v___f_731_, v___x_732_, v___x_8306__boxed_739_, v_ref_734_, v___f_735_, v___x_736_, v_nsStx_737_, v_a_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(uint8_t v___x_741_, uint8_t v___x_742_, lean_object* v_x1_743_, lean_object* v_x2_744_){
_start:
{
lean_object* v_fst_745_; uint8_t v___x_746_; 
v_fst_745_ = lean_ctor_get(v_x1_743_, 0);
v___x_746_ = lean_unbox(v_fst_745_);
if (v___x_746_ == 0)
{
lean_object* v_snd_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_x2_744_);
v_snd_747_ = lean_ctor_get(v_x1_743_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x1_743_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_x1_743_, 0);
lean_dec(v_unused_756_);
v___x_749_ = v_x1_743_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_snd_747_);
lean_dec(v_x1_743_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = lean_box(v___x_741_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_snd_747_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_766_; 
v_snd_757_ = lean_ctor_get(v_x1_743_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_x1_743_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_x1_743_, 0);
lean_dec(v_unused_767_);
v___x_759_ = v_x1_743_;
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_dec(v_x1_743_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = lean_array_push(v_snd_757_, v_x2_744_);
v___x_762_ = lean_box(v___x_742_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_761_);
lean_ctor_set(v___x_759_, 0, v___x_762_);
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_761_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v_x1_770_, lean_object* v_x2_771_){
_start:
{
uint8_t v___x_8355__boxed_772_; uint8_t v___x_8356__boxed_773_; lean_object* v_res_774_; 
v___x_8355__boxed_772_ = lean_unbox(v___x_768_);
v___x_8356__boxed_773_ = lean_unbox(v___x_769_);
v_res_774_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v___x_8355__boxed_772_, v___x_8356__boxed_773_, v_x1_770_, v_x2_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v_ids_775_, lean_object* v___f_776_, lean_object* v_a_777_, lean_object* v_inst_778_, lean_object* v_ref_779_, lean_object* v_toBind_780_, lean_object* v___f_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; size_t v_sz_784_; size_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_783_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_784_ = lean_array_size(v_ids_775_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_783_, v___f_776_, v_sz_784_, v___x_785_, v_ids_775_);
v___x_787_ = lean_array_to_list(v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_777_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_778_, v___x_788_, v_ref_779_);
v___x_790_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v___x_789_, v___f_781_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v_ids_791_, lean_object* v___f_792_, lean_object* v_a_793_, lean_object* v_inst_794_, lean_object* v_ref_795_, lean_object* v_toBind_796_, lean_object* v___f_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v_ids_791_, v___f_792_, v_a_793_, v_inst_794_, v_ref_795_, v_toBind_796_, v___f_797_, v_a_798_);
lean_dec(v_ref_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v___x_800_, lean_object* v_toPure_801_, lean_object* v___x_802_, lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v___y_808_, lean_object* v_toBind_809_, lean_object* v___f_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_enabled_812_; 
v_enabled_812_ = lean_ctor_get_uint8(v_a_811_, sizeof(void*)*3);
if (v_enabled_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v___f_810_);
lean_dec(v_toBind_809_);
lean_dec(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v___x_805_);
lean_dec_ref(v___x_804_);
lean_dec_ref(v___x_803_);
lean_dec_ref(v___x_802_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___x_800_);
v___x_814_ = lean_apply_2(v_toPure_801_, lean_box(0), v___x_813_);
return v___x_814_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_7354__overap_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v_toPure_801_);
v___x_815_ = lean_box(0);
v___x_7354__overap_816_ = l_Lean_Elab_addConstInfo___redArg(v___x_802_, v___x_803_, v___x_804_, v___x_805_, v_a_806_, v_a_807_, v___x_815_);
lean_inc(v___y_808_);
v___x_817_ = lean_apply_1(v___x_7354__overap_816_, v___y_808_);
v___x_818_ = lean_apply_4(v_toBind_809_, lean_box(0), lean_box(0), v___x_817_, v___f_810_);
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object* v___x_819_, lean_object* v_toPure_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v___y_827_, lean_object* v_toBind_828_, lean_object* v___f_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v___x_819_, v_toPure_820_, v___x_821_, v___x_822_, v___x_823_, v___x_824_, v_a_825_, v_a_826_, v___y_827_, v_toBind_828_, v___f_829_, v_a_830_);
lean_dec_ref(v_a_830_);
lean_dec(v___y_827_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object* v___x_832_, lean_object* v_inst_833_, lean_object* v___x_834_, lean_object* v_toPure_835_, lean_object* v___x_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v_toBind_841_, lean_object* v___f_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_844_; lean_object* v_getInfoState_845_; lean_object* v___f_846_; lean_object* v___x_847_; 
lean_inc_ref(v_inst_833_);
v___x_844_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_832_, v_inst_833_);
v_getInfoState_845_ = lean_ctor_get(v_inst_833_, 0);
lean_inc(v_getInfoState_845_);
lean_dec_ref(v_inst_833_);
lean_inc(v_toBind_841_);
lean_inc(v___y_840_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 12, 11);
lean_closure_set(v___f_846_, 0, v___x_834_);
lean_closure_set(v___f_846_, 1, v_toPure_835_);
lean_closure_set(v___f_846_, 2, v___x_836_);
lean_closure_set(v___f_846_, 3, v___x_844_);
lean_closure_set(v___f_846_, 4, v___x_837_);
lean_closure_set(v___f_846_, 5, v___x_838_);
lean_closure_set(v___f_846_, 6, v_a_839_);
lean_closure_set(v___f_846_, 7, v_a_843_);
lean_closure_set(v___f_846_, 8, v___y_840_);
lean_closure_set(v___f_846_, 9, v_toBind_841_);
lean_closure_set(v___f_846_, 10, v___f_842_);
v___x_847_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v_getInfoState_845_, v___f_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object* v___x_848_, lean_object* v_inst_849_, lean_object* v___x_850_, lean_object* v_toPure_851_, lean_object* v___x_852_, lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v_a_855_, lean_object* v___y_856_, lean_object* v_toBind_857_, lean_object* v___f_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(v___x_848_, v_inst_849_, v___x_850_, v_toPure_851_, v___x_852_, v___x_853_, v___x_854_, v_a_855_, v___y_856_, v_toBind_857_, v___f_858_, v_a_859_);
lean_dec(v___y_856_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v___x_861_, lean_object* v_inst_862_, lean_object* v___x_863_, lean_object* v_toPure_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v_toBind_868_, lean_object* v___f_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___f_873_, lean_object* v___x_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___f_882_; lean_object* v___x_7385__overap_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_inc(v_toBind_868_);
lean_inc_n(v___y_881_, 2);
lean_inc(v_a_878_);
lean_inc_ref(v___x_866_);
lean_inc_ref(v___x_865_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed), 12, 11);
lean_closure_set(v___f_882_, 0, v___x_861_);
lean_closure_set(v___f_882_, 1, v_inst_862_);
lean_closure_set(v___f_882_, 2, v___x_863_);
lean_closure_set(v___f_882_, 3, v_toPure_864_);
lean_closure_set(v___f_882_, 4, v___x_865_);
lean_closure_set(v___f_882_, 5, v___x_866_);
lean_closure_set(v___f_882_, 6, v___x_867_);
lean_closure_set(v___f_882_, 7, v_a_878_);
lean_closure_set(v___f_882_, 8, v___y_881_);
lean_closure_set(v___f_882_, 9, v_toBind_868_);
lean_closure_set(v___f_882_, 10, v___f_869_);
v___x_7385__overap_883_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_865_, v___x_866_, v___x_870_, v___x_871_, v___x_872_, v___f_873_, v___x_874_, v___x_875_, v___x_876_, v_a_877_, v_a_878_);
v___x_884_ = lean_apply_1(v___x_7385__overap_883_, v___y_881_);
v___x_885_ = lean_apply_4(v_toBind_868_, lean_box(0), lean_box(0), v___x_884_, v___f_882_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object** _args){
lean_object* v___x_886_ = _args[0];
lean_object* v_inst_887_ = _args[1];
lean_object* v___x_888_ = _args[2];
lean_object* v_toPure_889_ = _args[3];
lean_object* v___x_890_ = _args[4];
lean_object* v___x_891_ = _args[5];
lean_object* v___x_892_ = _args[6];
lean_object* v_toBind_893_ = _args[7];
lean_object* v___f_894_ = _args[8];
lean_object* v___x_895_ = _args[9];
lean_object* v___x_896_ = _args[10];
lean_object* v___x_897_ = _args[11];
lean_object* v___f_898_ = _args[12];
lean_object* v___x_899_ = _args[13];
lean_object* v___x_900_ = _args[14];
lean_object* v___x_901_ = _args[15];
lean_object* v_a_902_ = _args[16];
lean_object* v_a_903_ = _args[17];
lean_object* v_x_904_ = _args[18];
lean_object* v___y_905_ = _args[19];
lean_object* v___y_906_ = _args[20];
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v___x_886_, v_inst_887_, v___x_888_, v_toPure_889_, v___x_890_, v___x_891_, v___x_892_, v_toBind_893_, v___f_894_, v___x_895_, v___x_896_, v___x_897_, v___f_898_, v___x_899_, v___x_900_, v___x_901_, v_a_902_, v_a_903_, v_x_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_toPure_908_, lean_object* v___x_909_, lean_object* v_inst_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_toBind_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v___f_918_, lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_a_922_, lean_object* v_ids_923_, lean_object* v_ref_924_, lean_object* v___f_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___f_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v___x_7404__overap_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_927_ = lean_box(0);
lean_inc(v_toPure_908_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_928_, 0, v___x_927_);
lean_closure_set(v___f_928_, 1, v_toPure_908_);
lean_inc(v_toBind_914_);
lean_inc_ref(v___x_911_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 21, 17);
lean_closure_set(v___f_929_, 0, v___x_909_);
lean_closure_set(v___f_929_, 1, v_inst_910_);
lean_closure_set(v___f_929_, 2, v___x_927_);
lean_closure_set(v___f_929_, 3, v_toPure_908_);
lean_closure_set(v___f_929_, 4, v___x_911_);
lean_closure_set(v___f_929_, 5, v___x_912_);
lean_closure_set(v___f_929_, 6, v___x_913_);
lean_closure_set(v___f_929_, 7, v_toBind_914_);
lean_closure_set(v___f_929_, 8, v___f_928_);
lean_closure_set(v___f_929_, 9, v___x_915_);
lean_closure_set(v___f_929_, 10, v___x_916_);
lean_closure_set(v___f_929_, 11, v___x_917_);
lean_closure_set(v___f_929_, 12, v___f_918_);
lean_closure_set(v___f_929_, 13, v___x_919_);
lean_closure_set(v___f_929_, 14, v___x_920_);
lean_closure_set(v___f_929_, 15, v___x_921_);
lean_closure_set(v___f_929_, 16, v_a_922_);
v_sz_930_ = lean_array_size(v_ids_923_);
v___x_931_ = ((size_t)0ULL);
v___x_7404__overap_932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_911_, v_ids_923_, v___f_929_, v_sz_930_, v___x_931_, v___x_927_);
v___x_933_ = lean_apply_1(v___x_7404__overap_932_, v_ref_924_);
v___x_934_ = lean_apply_4(v_toBind_914_, lean_box(0), lean_box(0), v___x_933_, v___f_925_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_toPure_935_ = _args[0];
lean_object* v___x_936_ = _args[1];
lean_object* v_inst_937_ = _args[2];
lean_object* v___x_938_ = _args[3];
lean_object* v___x_939_ = _args[4];
lean_object* v___x_940_ = _args[5];
lean_object* v_toBind_941_ = _args[6];
lean_object* v___x_942_ = _args[7];
lean_object* v___x_943_ = _args[8];
lean_object* v___x_944_ = _args[9];
lean_object* v___f_945_ = _args[10];
lean_object* v___x_946_ = _args[11];
lean_object* v___x_947_ = _args[12];
lean_object* v___x_948_ = _args[13];
lean_object* v_a_949_ = _args[14];
lean_object* v_ids_950_ = _args[15];
lean_object* v_ref_951_ = _args[16];
lean_object* v___f_952_ = _args[17];
lean_object* v_a_953_ = _args[18];
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_toPure_935_, v___x_936_, v_inst_937_, v___x_938_, v___x_939_, v___x_940_, v_toBind_941_, v___x_942_, v___x_943_, v___x_944_, v___f_945_, v___x_946_, v___x_947_, v___x_948_, v_a_949_, v_ids_950_, v_ref_951_, v___f_952_, v_a_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v_inst_955_, lean_object* v___x_956_, lean_object* v___x_957_, lean_object* v___x_958_, lean_object* v_a_959_, lean_object* v_ref_960_, lean_object* v_toBind_961_, lean_object* v___f_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___f_964_; lean_object* v___x_7412__overap_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___f_964_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_964_, 0, v_inst_955_);
lean_closure_set(v___f_964_, 1, v___x_956_);
v___x_7412__overap_965_ = l_Lean_activateScoped___redArg(v___x_957_, v___x_958_, v___f_964_, v_a_959_);
v___x_966_ = lean_apply_1(v___x_7412__overap_965_, v_ref_960_);
v___x_967_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v___x_966_, v___f_962_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v_ids_968_, lean_object* v___f_969_, lean_object* v_inst_970_, lean_object* v_ref_971_, lean_object* v_toBind_972_, lean_object* v___f_973_, lean_object* v_inst_974_, lean_object* v___x_975_, lean_object* v_inst_976_, lean_object* v_toPure_977_, lean_object* v_inst_978_, lean_object* v___x_979_, lean_object* v___x_980_, lean_object* v___x_981_, lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v___f_985_, lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v_nsStx_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___x_995_; lean_object* v___x_7436__overap_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc_n(v_toBind_972_, 3);
lean_inc_n(v_ref_971_, 3);
lean_inc(v_inst_970_);
lean_inc_n(v_a_989_, 3);
lean_inc_ref(v_ids_968_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 8, 7);
lean_closure_set(v___f_990_, 0, v_ids_968_);
lean_closure_set(v___f_990_, 1, v___f_969_);
lean_closure_set(v___f_990_, 2, v_a_989_);
lean_closure_set(v___f_990_, 3, v_inst_970_);
lean_closure_set(v___f_990_, 4, v_ref_971_);
lean_closure_set(v___f_990_, 5, v_toBind_972_);
lean_closure_set(v___f_990_, 6, v___f_973_);
v___x_991_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_991_, 0, lean_box(0));
lean_closure_set(v___x_991_, 1, lean_box(0));
lean_closure_set(v___x_991_, 2, lean_box(0));
lean_closure_set(v___x_991_, 3, lean_box(0));
lean_closure_set(v___x_991_, 4, v_inst_974_);
lean_inc_n(v___x_975_, 2);
v___x_992_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_975_, v_inst_976_);
lean_inc_ref(v___x_986_);
lean_inc_ref(v___x_991_);
lean_inc_ref(v___x_992_);
lean_inc(v___f_985_);
lean_inc_ref_n(v___x_980_, 2);
lean_inc_ref_n(v___x_979_, 2);
v___f_993_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 19, 18);
lean_closure_set(v___f_993_, 0, v_toPure_977_);
lean_closure_set(v___f_993_, 1, v___x_975_);
lean_closure_set(v___f_993_, 2, v_inst_978_);
lean_closure_set(v___f_993_, 3, v___x_979_);
lean_closure_set(v___f_993_, 4, v___x_980_);
lean_closure_set(v___f_993_, 5, v___x_981_);
lean_closure_set(v___f_993_, 6, v_toBind_972_);
lean_closure_set(v___f_993_, 7, v___x_982_);
lean_closure_set(v___f_993_, 8, v___x_983_);
lean_closure_set(v___f_993_, 9, v___x_984_);
lean_closure_set(v___f_993_, 10, v___f_985_);
lean_closure_set(v___f_993_, 11, v___x_992_);
lean_closure_set(v___f_993_, 12, v___x_991_);
lean_closure_set(v___f_993_, 13, v___x_986_);
lean_closure_set(v___f_993_, 14, v_a_989_);
lean_closure_set(v___f_993_, 15, v_ids_968_);
lean_closure_set(v___f_993_, 16, v_ref_971_);
lean_closure_set(v___f_993_, 17, v___f_990_);
v___f_994_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24), 9, 8);
lean_closure_set(v___f_994_, 0, v_inst_970_);
lean_closure_set(v___f_994_, 1, v___x_975_);
lean_closure_set(v___f_994_, 2, v___x_979_);
lean_closure_set(v___f_994_, 3, v___x_980_);
lean_closure_set(v___f_994_, 4, v_a_989_);
lean_closure_set(v___f_994_, 5, v_ref_971_);
lean_closure_set(v___f_994_, 6, v_toBind_972_);
lean_closure_set(v___f_994_, 7, v___f_993_);
v___x_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_995_, 0, v_a_989_);
lean_ctor_set(v___x_995_, 1, v___x_987_);
v___x_7436__overap_996_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_979_, v___x_980_, v___x_991_, v___x_992_, v___f_985_, v___x_986_, v_nsStx_988_, v___x_995_);
v___x_997_ = lean_apply_1(v___x_7436__overap_996_, v_ref_971_);
v___x_998_ = lean_apply_4(v_toBind_972_, lean_box(0), lean_box(0), v___x_997_, v___f_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object** _args){
lean_object* v_ids_999_ = _args[0];
lean_object* v___f_1000_ = _args[1];
lean_object* v_inst_1001_ = _args[2];
lean_object* v_ref_1002_ = _args[3];
lean_object* v_toBind_1003_ = _args[4];
lean_object* v___f_1004_ = _args[5];
lean_object* v_inst_1005_ = _args[6];
lean_object* v___x_1006_ = _args[7];
lean_object* v_inst_1007_ = _args[8];
lean_object* v_toPure_1008_ = _args[9];
lean_object* v_inst_1009_ = _args[10];
lean_object* v___x_1010_ = _args[11];
lean_object* v___x_1011_ = _args[12];
lean_object* v___x_1012_ = _args[13];
lean_object* v___x_1013_ = _args[14];
lean_object* v___x_1014_ = _args[15];
lean_object* v___x_1015_ = _args[16];
lean_object* v___f_1016_ = _args[17];
lean_object* v___x_1017_ = _args[18];
lean_object* v___x_1018_ = _args[19];
lean_object* v_nsStx_1019_ = _args[20];
lean_object* v_a_1020_ = _args[21];
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v_ids_999_, v___f_1000_, v_inst_1001_, v_ref_1002_, v_toBind_1003_, v___f_1004_, v_inst_1005_, v___x_1006_, v_inst_1007_, v_toPure_1008_, v_inst_1009_, v___x_1010_, v___x_1011_, v___x_1012_, v___x_1013_, v___x_1014_, v___x_1015_, v___f_1016_, v___x_1017_, v___x_1018_, v_nsStx_1019_, v_a_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_inst_1024_, lean_object* v_toBind_1025_, lean_object* v___f_1026_, lean_object* v_____r_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = l_Lean_TSyntax_getId(v_a_1022_);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v_a_1023_);
v___x_1031_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1024_, v___x_1030_, v___y_1028_);
v___x_1032_ = lean_apply_4(v_toBind_1025_, lean_box(0), lean_box(0), v___x_1031_, v___f_1026_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_inst_1035_, lean_object* v_toBind_1036_, lean_object* v___f_1037_, lean_object* v_____r_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_a_1033_, v_a_1034_, v_inst_1035_, v_toBind_1036_, v___f_1037_, v_____r_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec(v_a_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v___f_1041_, lean_object* v___x_1042_, lean_object* v___y_1043_, lean_object* v___x_1044_, lean_object* v___x_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_toBind_1050_, lean_object* v___f_1051_, lean_object* v_a_1052_){
_start:
{
uint8_t v_enabled_1053_; 
v_enabled_1053_ = lean_ctor_get_uint8(v_a_1052_, sizeof(void*)*3);
if (v_enabled_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v___f_1051_);
lean_dec(v_toBind_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___x_1044_);
lean_inc(v___y_1043_);
v___x_1054_ = lean_apply_2(v___f_1041_, v___x_1042_, v___y_1043_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; lean_object* v___x_7465__overap_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v___f_1041_);
v___x_1055_ = lean_box(0);
v___x_7465__overap_1056_ = l_Lean_Elab_addConstInfo___redArg(v___x_1044_, v___x_1045_, v___x_1046_, v___x_1047_, v_a_1048_, v_a_1049_, v___x_1055_);
lean_inc(v___y_1043_);
v___x_1057_ = lean_apply_1(v___x_7465__overap_1056_, v___y_1043_);
v___x_1058_ = lean_apply_4(v_toBind_1050_, lean_box(0), lean_box(0), v___x_1057_, v___f_1051_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object* v___f_1059_, lean_object* v___x_1060_, lean_object* v___y_1061_, lean_object* v___x_1062_, lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_toBind_1068_, lean_object* v___f_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v___f_1059_, v___x_1060_, v___y_1061_, v___x_1062_, v___x_1063_, v___x_1064_, v___x_1065_, v_a_1066_, v_a_1067_, v_toBind_1068_, v___f_1069_, v_a_1070_);
lean_dec_ref(v_a_1070_);
lean_dec(v___y_1061_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v___x_1072_, lean_object* v_inst_1073_, lean_object* v_a_1074_, lean_object* v_inst_1075_, lean_object* v_toBind_1076_, lean_object* v___f_1077_, lean_object* v___y_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v___x_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v_getInfoState_1085_; lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; 
lean_inc_ref(v_inst_1073_);
v___x_1084_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_1072_, v_inst_1073_);
v_getInfoState_1085_ = lean_ctor_get(v_inst_1073_, 0);
lean_inc(v_getInfoState_1085_);
lean_dec_ref(v_inst_1073_);
lean_inc_n(v_toBind_1076_, 2);
lean_inc(v_a_1083_);
lean_inc(v_a_1074_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 7, 5);
lean_closure_set(v___f_1086_, 0, v_a_1074_);
lean_closure_set(v___f_1086_, 1, v_a_1083_);
lean_closure_set(v___f_1086_, 2, v_inst_1075_);
lean_closure_set(v___f_1086_, 3, v_toBind_1076_);
lean_closure_set(v___f_1086_, 4, v___f_1077_);
lean_inc_n(v___y_1078_, 2);
lean_inc_ref(v___f_1086_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_1087_, 0, v___f_1086_);
lean_closure_set(v___f_1087_, 1, v___y_1078_);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 12, 11);
lean_closure_set(v___f_1088_, 0, v___f_1086_);
lean_closure_set(v___f_1088_, 1, v___x_1079_);
lean_closure_set(v___f_1088_, 2, v___y_1078_);
lean_closure_set(v___f_1088_, 3, v___x_1080_);
lean_closure_set(v___f_1088_, 4, v___x_1084_);
lean_closure_set(v___f_1088_, 5, v___x_1081_);
lean_closure_set(v___f_1088_, 6, v___x_1082_);
lean_closure_set(v___f_1088_, 7, v_a_1074_);
lean_closure_set(v___f_1088_, 8, v_a_1083_);
lean_closure_set(v___f_1088_, 9, v_toBind_1076_);
lean_closure_set(v___f_1088_, 10, v___f_1087_);
v___x_1089_ = lean_apply_4(v_toBind_1076_, lean_box(0), lean_box(0), v_getInfoState_1085_, v___f_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object* v___x_1090_, lean_object* v_inst_1091_, lean_object* v_a_1092_, lean_object* v_inst_1093_, lean_object* v_toBind_1094_, lean_object* v___f_1095_, lean_object* v___y_1096_, lean_object* v___x_1097_, lean_object* v___x_1098_, lean_object* v___x_1099_, lean_object* v___x_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v___x_1090_, v_inst_1091_, v_a_1092_, v_inst_1093_, v_toBind_1094_, v___f_1095_, v___y_1096_, v___x_1097_, v___x_1098_, v___x_1099_, v___x_1100_, v_a_1101_);
lean_dec(v___y_1096_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v___x_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_toBind_1106_, lean_object* v___f_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v___x_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v___f_1115_, lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___f_1124_; lean_object* v___x_7500__overap_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_inc_ref(v___x_1110_);
lean_inc_ref(v___x_1109_);
lean_inc_n(v___y_1123_, 2);
lean_inc(v_toBind_1106_);
lean_inc(v_a_1120_);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 12, 11);
lean_closure_set(v___f_1124_, 0, v___x_1103_);
lean_closure_set(v___f_1124_, 1, v_inst_1104_);
lean_closure_set(v___f_1124_, 2, v_a_1120_);
lean_closure_set(v___f_1124_, 3, v_inst_1105_);
lean_closure_set(v___f_1124_, 4, v_toBind_1106_);
lean_closure_set(v___f_1124_, 5, v___f_1107_);
lean_closure_set(v___f_1124_, 6, v___y_1123_);
lean_closure_set(v___f_1124_, 7, v___x_1108_);
lean_closure_set(v___f_1124_, 8, v___x_1109_);
lean_closure_set(v___f_1124_, 9, v___x_1110_);
lean_closure_set(v___f_1124_, 10, v___x_1111_);
v___x_7500__overap_1125_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1109_, v___x_1110_, v___x_1112_, v___x_1113_, v___x_1114_, v___f_1115_, v___x_1116_, v___x_1117_, v___x_1118_, v_a_1119_, v_a_1120_);
v___x_1126_ = lean_apply_1(v___x_7500__overap_1125_, v___y_1123_);
v___x_1127_ = lean_apply_4(v_toBind_1106_, lean_box(0), lean_box(0), v___x_1126_, v___f_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_1128_ = _args[0];
lean_object* v_inst_1129_ = _args[1];
lean_object* v_inst_1130_ = _args[2];
lean_object* v_toBind_1131_ = _args[3];
lean_object* v___f_1132_ = _args[4];
lean_object* v___x_1133_ = _args[5];
lean_object* v___x_1134_ = _args[6];
lean_object* v___x_1135_ = _args[7];
lean_object* v___x_1136_ = _args[8];
lean_object* v___x_1137_ = _args[9];
lean_object* v___x_1138_ = _args[10];
lean_object* v___x_1139_ = _args[11];
lean_object* v___f_1140_ = _args[12];
lean_object* v___x_1141_ = _args[13];
lean_object* v___x_1142_ = _args[14];
lean_object* v___x_1143_ = _args[15];
lean_object* v_a_1144_ = _args[16];
lean_object* v_a_1145_ = _args[17];
lean_object* v_x_1146_ = _args[18];
lean_object* v___y_1147_ = _args[19];
lean_object* v___y_1148_ = _args[20];
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v___x_1128_, v_inst_1129_, v_inst_1130_, v_toBind_1131_, v___f_1132_, v___x_1133_, v___x_1134_, v___x_1135_, v___x_1136_, v___x_1137_, v___x_1138_, v___x_1139_, v___f_1140_, v___x_1141_, v___x_1142_, v___x_1143_, v_a_1144_, v_a_1145_, v_x_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v_toPure_1150_, lean_object* v___x_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_toBind_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v___x_1160_, lean_object* v___f_1161_, lean_object* v___x_1162_, lean_object* v___x_1163_, lean_object* v___x_1164_, lean_object* v_a_1165_, lean_object* v_ids_1166_, lean_object* v_ref_1167_, lean_object* v___f_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_7520__overap_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1170_ = lean_box(0);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1171_, 0, v___x_1170_);
lean_closure_set(v___f_1171_, 1, v_toPure_1150_);
lean_inc_ref(v___x_1155_);
lean_inc(v_toBind_1154_);
v___f_1172_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 21, 17);
lean_closure_set(v___f_1172_, 0, v___x_1151_);
lean_closure_set(v___f_1172_, 1, v_inst_1152_);
lean_closure_set(v___f_1172_, 2, v_inst_1153_);
lean_closure_set(v___f_1172_, 3, v_toBind_1154_);
lean_closure_set(v___f_1172_, 4, v___f_1171_);
lean_closure_set(v___f_1172_, 5, v___x_1170_);
lean_closure_set(v___f_1172_, 6, v___x_1155_);
lean_closure_set(v___f_1172_, 7, v___x_1156_);
lean_closure_set(v___f_1172_, 8, v___x_1157_);
lean_closure_set(v___f_1172_, 9, v___x_1158_);
lean_closure_set(v___f_1172_, 10, v___x_1159_);
lean_closure_set(v___f_1172_, 11, v___x_1160_);
lean_closure_set(v___f_1172_, 12, v___f_1161_);
lean_closure_set(v___f_1172_, 13, v___x_1162_);
lean_closure_set(v___f_1172_, 14, v___x_1163_);
lean_closure_set(v___f_1172_, 15, v___x_1164_);
lean_closure_set(v___f_1172_, 16, v_a_1165_);
v_sz_1173_ = lean_array_size(v_ids_1166_);
v___x_1174_ = ((size_t)0ULL);
v___x_7520__overap_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1155_, v_ids_1166_, v___f_1172_, v_sz_1173_, v___x_1174_, v___x_1170_);
v___x_1176_ = lean_apply_1(v___x_7520__overap_1175_, v_ref_1167_);
v___x_1177_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1176_, v___f_1168_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object** _args){
lean_object* v_toPure_1178_ = _args[0];
lean_object* v___x_1179_ = _args[1];
lean_object* v_inst_1180_ = _args[2];
lean_object* v_inst_1181_ = _args[3];
lean_object* v_toBind_1182_ = _args[4];
lean_object* v___x_1183_ = _args[5];
lean_object* v___x_1184_ = _args[6];
lean_object* v___x_1185_ = _args[7];
lean_object* v___x_1186_ = _args[8];
lean_object* v___x_1187_ = _args[9];
lean_object* v___x_1188_ = _args[10];
lean_object* v___f_1189_ = _args[11];
lean_object* v___x_1190_ = _args[12];
lean_object* v___x_1191_ = _args[13];
lean_object* v___x_1192_ = _args[14];
lean_object* v_a_1193_ = _args[15];
lean_object* v_ids_1194_ = _args[16];
lean_object* v_ref_1195_ = _args[17];
lean_object* v___f_1196_ = _args[18];
lean_object* v_a_1197_ = _args[19];
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v_toPure_1178_, v___x_1179_, v_inst_1180_, v_inst_1181_, v_toBind_1182_, v___x_1183_, v___x_1184_, v___x_1185_, v___x_1186_, v___x_1187_, v___x_1188_, v___f_1189_, v___x_1190_, v___x_1191_, v___x_1192_, v_a_1193_, v_ids_1194_, v_ref_1195_, v___f_1196_, v_a_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_inst_1199_, lean_object* v___x_1200_, lean_object* v_inst_1201_, lean_object* v_toPure_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_toBind_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v___f_1212_, lean_object* v___x_1213_, lean_object* v_ids_1214_, lean_object* v_ref_1215_, lean_object* v___f_1216_, lean_object* v_ns_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___f_1221_; lean_object* v___x_7539__overap_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1219_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1219_, 0, lean_box(0));
lean_closure_set(v___x_1219_, 1, lean_box(0));
lean_closure_set(v___x_1219_, 2, lean_box(0));
lean_closure_set(v___x_1219_, 3, lean_box(0));
lean_closure_set(v___x_1219_, 4, v_inst_1199_);
lean_inc(v___x_1200_);
v___x_1220_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1200_, v_inst_1201_);
lean_inc(v_ref_1215_);
lean_inc(v_a_1218_);
lean_inc_ref(v___x_1213_);
lean_inc_ref(v___x_1219_);
lean_inc_ref(v___x_1220_);
lean_inc(v___f_1212_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v___x_1206_);
lean_inc(v_toBind_1205_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed), 20, 19);
lean_closure_set(v___f_1221_, 0, v_toPure_1202_);
lean_closure_set(v___f_1221_, 1, v___x_1200_);
lean_closure_set(v___f_1221_, 2, v_inst_1203_);
lean_closure_set(v___f_1221_, 3, v_inst_1204_);
lean_closure_set(v___f_1221_, 4, v_toBind_1205_);
lean_closure_set(v___f_1221_, 5, v___x_1206_);
lean_closure_set(v___f_1221_, 6, v___x_1207_);
lean_closure_set(v___f_1221_, 7, v___x_1208_);
lean_closure_set(v___f_1221_, 8, v___x_1209_);
lean_closure_set(v___f_1221_, 9, v___x_1210_);
lean_closure_set(v___f_1221_, 10, v___x_1211_);
lean_closure_set(v___f_1221_, 11, v___f_1212_);
lean_closure_set(v___f_1221_, 12, v___x_1220_);
lean_closure_set(v___f_1221_, 13, v___x_1219_);
lean_closure_set(v___f_1221_, 14, v___x_1213_);
lean_closure_set(v___f_1221_, 15, v_a_1218_);
lean_closure_set(v___f_1221_, 16, v_ids_1214_);
lean_closure_set(v___f_1221_, 17, v_ref_1215_);
lean_closure_set(v___f_1221_, 18, v___f_1216_);
v___x_7539__overap_1222_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1206_, v___x_1207_, v___x_1219_, v___x_1220_, v___f_1212_, v___x_1213_, v_ns_1217_, v_a_1218_);
v___x_1223_ = lean_apply_1(v___x_7539__overap_1222_, v_ref_1215_);
v___x_1224_ = lean_apply_4(v_toBind_1205_, lean_box(0), lean_box(0), v___x_1223_, v___f_1221_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_inst_1225_ = _args[0];
lean_object* v___x_1226_ = _args[1];
lean_object* v_inst_1227_ = _args[2];
lean_object* v_toPure_1228_ = _args[3];
lean_object* v_inst_1229_ = _args[4];
lean_object* v_inst_1230_ = _args[5];
lean_object* v_toBind_1231_ = _args[6];
lean_object* v___x_1232_ = _args[7];
lean_object* v___x_1233_ = _args[8];
lean_object* v___x_1234_ = _args[9];
lean_object* v___x_1235_ = _args[10];
lean_object* v___x_1236_ = _args[11];
lean_object* v___x_1237_ = _args[12];
lean_object* v___f_1238_ = _args[13];
lean_object* v___x_1239_ = _args[14];
lean_object* v_ids_1240_ = _args[15];
lean_object* v_ref_1241_ = _args[16];
lean_object* v___f_1242_ = _args[17];
lean_object* v_ns_1243_ = _args[18];
lean_object* v_a_1244_ = _args[19];
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_inst_1225_, v___x_1226_, v_inst_1227_, v_toPure_1228_, v_inst_1229_, v_inst_1230_, v_toBind_1231_, v___x_1232_, v___x_1233_, v___x_1234_, v___x_1235_, v___x_1236_, v___x_1237_, v___f_1238_, v___x_1239_, v_ids_1240_, v_ref_1241_, v___f_1242_, v_ns_1243_, v_a_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v_inst_1246_, lean_object* v___x_1247_, lean_object* v___x_1248_, lean_object* v___x_1249_, lean_object* v_toBind_1250_, lean_object* v___f_1251_, lean_object* v_a_1252_, lean_object* v_x_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___f_1256_; lean_object* v___x_7559__overap_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___f_1256_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1256_, 0, v_inst_1246_);
lean_closure_set(v___f_1256_, 1, v___x_1247_);
v___x_7559__overap_1257_ = l_Lean_activateScoped___redArg(v___x_1248_, v___x_1249_, v___f_1256_, v_a_1252_);
lean_inc(v___y_1255_);
v___x_1258_ = lean_apply_1(v___x_7559__overap_1257_, v___y_1255_);
v___x_1259_ = lean_apply_4(v_toBind_1250_, lean_box(0), lean_box(0), v___x_1258_, v___f_1251_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object* v_inst_1260_, lean_object* v___x_1261_, lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v_toBind_1264_, lean_object* v___f_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(v_inst_1260_, v___x_1261_, v___x_1262_, v___x_1263_, v_toBind_1264_, v___f_1265_, v_a_1266_, v_x_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v___x_1271_, lean_object* v___f_1272_, lean_object* v_a_1273_, lean_object* v___x_1274_, lean_object* v___y_1275_, lean_object* v_toBind_1276_, lean_object* v___f_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_7566__overap_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_7566__overap_1279_ = l_List_forIn_x27_loop___redArg(v___x_1271_, v___f_1272_, v_a_1273_, v___x_1274_);
lean_inc(v___y_1275_);
v___x_1280_ = lean_apply_1(v___x_7566__overap_1279_, v___y_1275_);
v___x_1281_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v___x_1280_, v___f_1277_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object* v___x_1282_, lean_object* v___f_1283_, lean_object* v_a_1284_, lean_object* v___x_1285_, lean_object* v___y_1286_, lean_object* v_toBind_1287_, lean_object* v___f_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(v___x_1282_, v___f_1283_, v_a_1284_, v___x_1285_, v___y_1286_, v_toBind_1287_, v___f_1288_, v_a_1289_);
lean_dec(v___y_1286_);
lean_dec(v_a_1284_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v___x_1291_, lean_object* v___f_1292_, lean_object* v___x_1293_, lean_object* v___y_1294_, lean_object* v_toBind_1295_, lean_object* v___f_1296_, lean_object* v_inst_1297_, lean_object* v___x_1298_, lean_object* v_inst_1299_, lean_object* v___x_1300_, lean_object* v___f_1301_, lean_object* v___x_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_7582__overap_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_inc(v_toBind_1295_);
lean_inc_n(v___y_1294_, 2);
lean_inc(v_a_1304_);
lean_inc_ref(v___x_1291_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed), 8, 7);
lean_closure_set(v___f_1305_, 0, v___x_1291_);
lean_closure_set(v___f_1305_, 1, v___f_1292_);
lean_closure_set(v___f_1305_, 2, v_a_1304_);
lean_closure_set(v___f_1305_, 3, v___x_1293_);
lean_closure_set(v___f_1305_, 4, v___y_1294_);
lean_closure_set(v___f_1305_, 5, v_toBind_1295_);
lean_closure_set(v___f_1305_, 6, v___f_1296_);
v___x_1306_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1306_, 0, lean_box(0));
lean_closure_set(v___x_1306_, 1, lean_box(0));
lean_closure_set(v___x_1306_, 2, lean_box(0));
lean_closure_set(v___x_1306_, 3, lean_box(0));
lean_closure_set(v___x_1306_, 4, v_inst_1297_);
v___x_1307_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1298_, v_inst_1299_);
v___x_7582__overap_1308_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1291_, v___x_1300_, v___x_1306_, v___x_1307_, v___f_1301_, v___x_1302_, v_a_1303_, v_a_1304_);
v___x_1309_ = lean_apply_1(v___x_7582__overap_1308_, v___y_1294_);
v___x_1310_ = lean_apply_4(v_toBind_1295_, lean_box(0), lean_box(0), v___x_1309_, v___f_1305_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object* v___x_1311_, lean_object* v___f_1312_, lean_object* v___x_1313_, lean_object* v___y_1314_, lean_object* v_toBind_1315_, lean_object* v___f_1316_, lean_object* v_inst_1317_, lean_object* v___x_1318_, lean_object* v_inst_1319_, lean_object* v___x_1320_, lean_object* v___f_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v___x_1311_, v___f_1312_, v___x_1313_, v___y_1314_, v_toBind_1315_, v___f_1316_, v_inst_1317_, v___x_1318_, v_inst_1319_, v___x_1320_, v___f_1321_, v___x_1322_, v_a_1323_, v_a_1324_);
lean_dec(v___y_1314_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v___x_1331_, lean_object* v_toBind_1332_, lean_object* v___f_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v___x_1337_, lean_object* v___f_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1345_; lean_object* v_getEnv_1346_; lean_object* v_modifyEnv_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1370_; 
lean_inc(v_inst_1329_);
v___x_1345_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1328_, v_inst_1329_);
v_getEnv_1346_ = lean_ctor_get(v_inst_1330_, 0);
v_modifyEnv_1347_ = lean_ctor_get(v_inst_1330_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_inst_1330_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1349_ = v_inst_1330_;
v_isShared_1350_ = v_isSharedCheck_1370_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_modifyEnv_1347_);
lean_inc(v_getEnv_1346_);
lean_dec(v_inst_1330_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1370_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___f_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1351_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1352_, 0, v_modifyEnv_1347_);
lean_closure_set(v___f_1352_, 1, v___x_1351_);
v___x_1353_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1353_, 0, lean_box(0));
lean_closure_set(v___x_1353_, 1, lean_box(0));
lean_closure_set(v___x_1353_, 2, lean_box(0));
lean_closure_set(v___x_1353_, 3, lean_box(0));
lean_closure_set(v___x_1353_, 4, v_getEnv_1346_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___f_1352_);
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___f_1352_);
v___x_1355_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_7614__overap_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
lean_inc_n(v_toBind_1332_, 2);
lean_inc_ref_n(v___x_1355_, 2);
lean_inc_ref_n(v___x_1331_, 3);
v___f_1356_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 10, 6);
lean_closure_set(v___f_1356_, 0, v_inst_1329_);
lean_closure_set(v___f_1356_, 1, v___x_1351_);
lean_closure_set(v___f_1356_, 2, v___x_1331_);
lean_closure_set(v___f_1356_, 3, v___x_1355_);
lean_closure_set(v___f_1356_, 4, v_toBind_1332_);
lean_closure_set(v___f_1356_, 5, v___f_1333_);
lean_inc_ref(v_inst_1334_);
v___f_1357_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1357_, 0, v_inst_1334_);
v___f_1358_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1358_, 0, v_inst_1334_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___f_1357_);
lean_ctor_set(v___x_1359_, 1, v___f_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_1361_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1351_, v___x_1360_, v_inst_1335_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1362_, 0, v_inst_1336_);
lean_closure_set(v___f_1362_, 1, v___x_1351_);
lean_inc(v_a_1341_);
lean_inc_ref(v___x_1345_);
lean_inc_ref(v___f_1362_);
lean_inc_n(v___y_1344_, 2);
v___f_1363_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 14, 13);
lean_closure_set(v___f_1363_, 0, v___x_1331_);
lean_closure_set(v___f_1363_, 1, v___f_1356_);
lean_closure_set(v___f_1363_, 2, v___x_1337_);
lean_closure_set(v___f_1363_, 3, v___y_1344_);
lean_closure_set(v___f_1363_, 4, v_toBind_1332_);
lean_closure_set(v___f_1363_, 5, v___f_1338_);
lean_closure_set(v___f_1363_, 6, v_inst_1339_);
lean_closure_set(v___f_1363_, 7, v___x_1351_);
lean_closure_set(v___f_1363_, 8, v_inst_1340_);
lean_closure_set(v___f_1363_, 9, v___x_1355_);
lean_closure_set(v___f_1363_, 10, v___f_1362_);
lean_closure_set(v___f_1363_, 11, v___x_1345_);
lean_closure_set(v___f_1363_, 12, v_a_1341_);
v___x_1364_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1362_, v___x_1331_);
v___x_1365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1359_);
lean_ctor_set(v___x_1365_, 1, v___x_1361_);
lean_ctor_set(v___x_1365_, 2, v___x_1364_);
v___x_7614__overap_1366_ = l_Lean_resolveNamespace___redArg(v___x_1331_, v___x_1345_, v___x_1355_, v___x_1365_, v_a_1341_);
v___x_1367_ = lean_apply_1(v___x_7614__overap_1366_, v___y_1344_);
v___x_1368_ = lean_apply_4(v_toBind_1332_, lean_box(0), lean_box(0), v___x_1367_, v___f_1363_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object** _args){
lean_object* v_inst_1371_ = _args[0];
lean_object* v_inst_1372_ = _args[1];
lean_object* v_inst_1373_ = _args[2];
lean_object* v___x_1374_ = _args[3];
lean_object* v_toBind_1375_ = _args[4];
lean_object* v___f_1376_ = _args[5];
lean_object* v_inst_1377_ = _args[6];
lean_object* v_inst_1378_ = _args[7];
lean_object* v_inst_1379_ = _args[8];
lean_object* v___x_1380_ = _args[9];
lean_object* v___f_1381_ = _args[10];
lean_object* v_inst_1382_ = _args[11];
lean_object* v_inst_1383_ = _args[12];
lean_object* v_a_1384_ = _args[13];
lean_object* v_x_1385_ = _args[14];
lean_object* v___y_1386_ = _args[15];
lean_object* v___y_1387_ = _args[16];
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(v_inst_1371_, v_inst_1372_, v_inst_1373_, v___x_1374_, v_toBind_1375_, v___f_1376_, v_inst_1377_, v_inst_1378_, v_inst_1379_, v___x_1380_, v___f_1381_, v_inst_1382_, v_inst_1383_, v_a_1384_, v_x_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object* v_inst_1389_, lean_object* v___x_1390_, lean_object* v___x_1391_, lean_object* v___x_1392_, lean_object* v_a_1393_, lean_object* v___y_1394_, lean_object* v_toBind_1395_, lean_object* v___f_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_7632__overap_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___f_1398_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1398_, 0, v_inst_1389_);
lean_closure_set(v___f_1398_, 1, v___x_1390_);
v___x_7632__overap_1399_ = l_Lean_activateScoped___redArg(v___x_1391_, v___x_1392_, v___f_1398_, v_a_1393_);
lean_inc(v___y_1394_);
v___x_1400_ = lean_apply_1(v___x_7632__overap_1399_, v___y_1394_);
v___x_1401_ = lean_apply_4(v_toBind_1395_, lean_box(0), lean_box(0), v___x_1400_, v___f_1396_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed(lean_object* v_inst_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v_toBind_1408_, lean_object* v___f_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(v_inst_1402_, v___x_1403_, v___x_1404_, v___x_1405_, v_a_1406_, v___y_1407_, v_toBind_1408_, v___f_1409_, v_a_1410_);
lean_dec(v___y_1407_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v_inst_1412_, lean_object* v___x_1413_, lean_object* v___x_1414_, lean_object* v___x_1415_, lean_object* v_toBind_1416_, lean_object* v___f_1417_, lean_object* v___x_1418_, lean_object* v_a_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_inc(v_toBind_1416_);
lean_inc(v___y_1422_);
lean_inc(v_a_1419_);
lean_inc(v_inst_1412_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39___boxed), 9, 8);
lean_closure_set(v___f_1423_, 0, v_inst_1412_);
lean_closure_set(v___f_1423_, 1, v___x_1413_);
lean_closure_set(v___f_1423_, 2, v___x_1414_);
lean_closure_set(v___f_1423_, 3, v___x_1415_);
lean_closure_set(v___f_1423_, 4, v_a_1419_);
lean_closure_set(v___f_1423_, 5, v___y_1422_);
lean_closure_set(v___f_1423_, 6, v_toBind_1416_);
lean_closure_set(v___f_1423_, 7, v___f_1417_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1419_);
lean_ctor_set(v___x_1424_, 1, v___x_1418_);
v___x_1425_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1412_, v___x_1424_, v___y_1422_);
v___x_1426_ = lean_apply_4(v_toBind_1416_, lean_box(0), lean_box(0), v___x_1425_, v___f_1423_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object* v_inst_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_toBind_1431_, lean_object* v___f_1432_, lean_object* v___x_1433_, lean_object* v_a_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(v_inst_1427_, v___x_1428_, v___x_1429_, v___x_1430_, v_toBind_1431_, v___f_1432_, v___x_1433_, v_a_1434_, v_x_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v___x_1442_, lean_object* v_toBind_1443_, lean_object* v___f_1444_, lean_object* v___x_1445_, lean_object* v_inst_1446_, lean_object* v_inst_1447_, lean_object* v_inst_1448_, lean_object* v___x_1449_, lean_object* v___f_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_a_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v_getEnv_1458_; lean_object* v_modifyEnv_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1482_; 
lean_inc(v_inst_1440_);
v___x_1457_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1439_, v_inst_1440_);
v_getEnv_1458_ = lean_ctor_get(v_inst_1441_, 0);
v_modifyEnv_1459_ = lean_ctor_get(v_inst_1441_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_inst_1441_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1461_ = v_inst_1441_;
v_isShared_1462_ = v_isSharedCheck_1482_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_modifyEnv_1459_);
lean_inc(v_getEnv_1458_);
lean_dec(v_inst_1441_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1482_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___f_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1463_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_1464_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1464_, 0, v_modifyEnv_1459_);
lean_closure_set(v___f_1464_, 1, v___x_1463_);
v___x_1465_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1465_, 0, lean_box(0));
lean_closure_set(v___x_1465_, 1, lean_box(0));
lean_closure_set(v___x_1465_, 2, lean_box(0));
lean_closure_set(v___x_1465_, 3, lean_box(0));
lean_closure_set(v___x_1465_, 4, v_getEnv_1458_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___f_1464_);
lean_ctor_set(v___x_1461_, 0, v___x_1465_);
v___x_1467_ = v___x_1461_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___f_1464_);
v___x_1467_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_7701__overap_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_inc_n(v_toBind_1443_, 2);
lean_inc_ref_n(v___x_1467_, 2);
lean_inc_ref_n(v___x_1442_, 3);
v___f_1468_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed), 11, 7);
lean_closure_set(v___f_1468_, 0, v_inst_1440_);
lean_closure_set(v___f_1468_, 1, v___x_1463_);
lean_closure_set(v___f_1468_, 2, v___x_1442_);
lean_closure_set(v___f_1468_, 3, v___x_1467_);
lean_closure_set(v___f_1468_, 4, v_toBind_1443_);
lean_closure_set(v___f_1468_, 5, v___f_1444_);
lean_closure_set(v___f_1468_, 6, v___x_1445_);
lean_inc_ref(v_inst_1446_);
v___f_1469_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1469_, 0, v_inst_1446_);
v___f_1470_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1470_, 0, v_inst_1446_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___f_1469_);
lean_ctor_set(v___x_1471_, 1, v___f_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_1473_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1463_, v___x_1472_, v_inst_1447_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1474_, 0, v_inst_1448_);
lean_closure_set(v___f_1474_, 1, v___x_1463_);
lean_inc(v_a_1453_);
lean_inc_ref(v___x_1457_);
lean_inc_ref(v___f_1474_);
lean_inc_n(v___y_1456_, 2);
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 14, 13);
lean_closure_set(v___f_1475_, 0, v___x_1442_);
lean_closure_set(v___f_1475_, 1, v___f_1468_);
lean_closure_set(v___f_1475_, 2, v___x_1449_);
lean_closure_set(v___f_1475_, 3, v___y_1456_);
lean_closure_set(v___f_1475_, 4, v_toBind_1443_);
lean_closure_set(v___f_1475_, 5, v___f_1450_);
lean_closure_set(v___f_1475_, 6, v_inst_1451_);
lean_closure_set(v___f_1475_, 7, v___x_1463_);
lean_closure_set(v___f_1475_, 8, v_inst_1452_);
lean_closure_set(v___f_1475_, 9, v___x_1467_);
lean_closure_set(v___f_1475_, 10, v___f_1474_);
lean_closure_set(v___f_1475_, 11, v___x_1457_);
lean_closure_set(v___f_1475_, 12, v_a_1453_);
v___x_1476_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1474_, v___x_1442_);
v___x_1477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1471_);
lean_ctor_set(v___x_1477_, 1, v___x_1473_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
v___x_7701__overap_1478_ = l_Lean_resolveNamespace___redArg(v___x_1442_, v___x_1457_, v___x_1467_, v___x_1477_, v_a_1453_);
v___x_1479_ = lean_apply_1(v___x_7701__overap_1478_, v___y_1456_);
v___x_1480_ = lean_apply_4(v_toBind_1443_, lean_box(0), lean_box(0), v___x_1479_, v___f_1475_);
return v___x_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_inst_1483_ = _args[0];
lean_object* v_inst_1484_ = _args[1];
lean_object* v_inst_1485_ = _args[2];
lean_object* v___x_1486_ = _args[3];
lean_object* v_toBind_1487_ = _args[4];
lean_object* v___f_1488_ = _args[5];
lean_object* v___x_1489_ = _args[6];
lean_object* v_inst_1490_ = _args[7];
lean_object* v_inst_1491_ = _args[8];
lean_object* v_inst_1492_ = _args[9];
lean_object* v___x_1493_ = _args[10];
lean_object* v___f_1494_ = _args[11];
lean_object* v_inst_1495_ = _args[12];
lean_object* v_inst_1496_ = _args[13];
lean_object* v_a_1497_ = _args[14];
lean_object* v_x_1498_ = _args[15];
lean_object* v___y_1499_ = _args[16];
lean_object* v___y_1500_ = _args[17];
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(v_inst_1483_, v_inst_1484_, v_inst_1485_, v___x_1486_, v_toBind_1487_, v___f_1488_, v___x_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v___x_1493_, v___f_1494_, v_inst_1495_, v_inst_1496_, v_a_1497_, v_x_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v_toPure_1529_, lean_object* v_inst_1530_, lean_object* v_toBind_1531_, uint8_t v___x_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v___x_1535_, lean_object* v_stx_1536_, lean_object* v___f_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v___f_1541_, lean_object* v___f_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v___x_1545_, lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v___f_1549_, lean_object* v_ref_1550_){
_start:
{
lean_object* v___f_1551_; 
lean_inc(v_toBind_1531_);
lean_inc(v_inst_1530_);
lean_inc(v_ref_1550_);
lean_inc(v_toPure_1529_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1551_, 0, v_toPure_1529_);
lean_closure_set(v___f_1551_, 1, v_ref_1550_);
lean_closure_set(v___f_1551_, 2, v_inst_1530_);
lean_closure_set(v___f_1551_, 3, v_toBind_1531_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0));
lean_inc_ref(v___x_1535_);
lean_inc_ref(v___x_1534_);
lean_inc_ref(v___x_1533_);
v___x_1553_ = l_Lean_Name_mkStr4(v___x_1533_, v___x_1534_, v___x_1535_, v___x_1552_);
lean_inc(v_stx_1536_);
v___x_1554_ = l_Lean_Syntax_isOfKind(v_stx_1536_, v___x_1553_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1));
lean_inc_ref(v___x_1535_);
lean_inc_ref(v___x_1534_);
lean_inc_ref(v___x_1533_);
v___x_1556_ = l_Lean_Name_mkStr4(v___x_1533_, v___x_1534_, v___x_1535_, v___x_1555_);
lean_inc(v_stx_1536_);
v___x_1557_ = l_Lean_Syntax_isOfKind(v_stx_1536_, v___x_1556_);
lean_dec(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1558_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2));
lean_inc_ref(v___x_1535_);
lean_inc_ref(v___x_1534_);
lean_inc_ref(v___x_1533_);
v___x_1559_ = l_Lean_Name_mkStr4(v___x_1533_, v___x_1534_, v___x_1535_, v___x_1558_);
lean_inc(v_stx_1536_);
v___x_1560_ = l_Lean_Syntax_isOfKind(v_stx_1536_, v___x_1559_);
lean_dec(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
lean_dec_ref(v___f_1549_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3));
lean_inc_ref(v___x_1535_);
lean_inc_ref(v___x_1534_);
lean_inc_ref(v___x_1533_);
v___x_1562_ = l_Lean_Name_mkStr4(v___x_1533_, v___x_1534_, v___x_1535_, v___x_1561_);
lean_inc(v_stx_1536_);
v___x_1563_ = l_Lean_Syntax_isOfKind(v_stx_1536_, v___x_1562_);
lean_dec(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___f_1564_; lean_object* v___f_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; lean_object* v___x_7738__overap_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v_inst_1548_);
lean_dec_ref(v_inst_1547_);
lean_dec(v_inst_1546_);
lean_dec_ref(v___x_1545_);
lean_dec(v_inst_1544_);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
lean_dec(v_stx_1536_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1533_);
lean_dec(v_inst_1530_);
lean_dec(v_toPure_1529_);
lean_inc(v_ref_1550_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1564_, 0, v___f_1537_);
lean_closure_set(v___f_1564_, 1, v_ref_1550_);
lean_inc_ref(v_inst_1538_);
v___f_1565_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1565_, 0, v_inst_1538_);
v___f_1566_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1566_, 0, v_inst_1538_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___f_1565_);
lean_ctor_set(v___x_1567_, 1, v___f_1566_);
v___x_7738__overap_1568_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1567_);
v___x_1569_ = lean_apply_1(v___x_7738__overap_1568_, v_ref_1550_);
lean_inc(v_toBind_1531_);
v___x_1570_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1569_, v___f_1564_);
v___x_1571_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1570_, v___f_1551_);
return v___x_1571_;
}
else
{
lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v_nsStx_1575_; lean_object* v___x_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___y_1581_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
lean_inc_n(v_ref_1550_, 2);
lean_inc(v___f_1537_);
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1572_, 0, v___f_1537_);
lean_closure_set(v___f_1572_, 1, v_ref_1550_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1573_, 0, v___f_1537_);
lean_closure_set(v___f_1573_, 1, v_ref_1550_);
v___x_1574_ = lean_unsigned_to_nat(0u);
v_nsStx_1575_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1574_);
v___x_1576_ = lean_unsigned_to_nat(2u);
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1577_, 0, v___x_1533_);
lean_closure_set(v___f_1577_, 1, v___x_1534_);
lean_closure_set(v___f_1577_, 2, v___x_1535_);
lean_closure_set(v___f_1577_, 3, v___x_1574_);
lean_closure_set(v___f_1577_, 4, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1576_);
lean_dec(v_stx_1536_);
v___x_1579_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__13));
v___x_1625_ = l_Lean_Syntax_getArgs(v___x_1578_);
lean_dec(v___x_1578_);
v___x_1626_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__14));
v___x_1627_ = lean_array_get_size(v___x_1625_);
v___x_1628_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1629_ = lean_nat_dec_lt(v___x_1574_, v___x_1627_);
if (v___x_1629_ == 0)
{
lean_dec_ref(v___x_1625_);
v___y_1581_ = v___x_1626_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1630_ = lean_box(v___x_1563_);
v___x_1631_ = lean_box(v___x_1560_);
v___f_1632_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_1632_, 0, v___x_1630_);
lean_closure_set(v___f_1632_, 1, v___x_1631_);
v___x_1633_ = lean_box(v___x_1563_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v___x_1626_);
v___x_1635_ = lean_nat_dec_le(v___x_1627_, v___x_1627_);
if (v___x_1635_ == 0)
{
if (v___x_1629_ == 0)
{
lean_dec_ref_known(v___x_1634_, 2);
lean_dec_ref(v___f_1632_);
lean_dec_ref(v___x_1625_);
v___y_1581_ = v___x_1626_;
goto v___jp_1580_;
}
else
{
size_t v___x_1636_; size_t v___x_1637_; lean_object* v___x_1638_; lean_object* v_snd_1639_; 
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = lean_usize_of_nat(v___x_1627_);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1628_, v___f_1632_, v___x_1625_, v___x_1636_, v___x_1637_, v___x_1634_);
v_snd_1639_ = lean_ctor_get(v___x_1638_, 1);
lean_inc(v_snd_1639_);
lean_dec(v___x_1638_);
v___y_1581_ = v_snd_1639_;
goto v___jp_1580_;
}
}
else
{
size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; lean_object* v_snd_1643_; 
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = lean_usize_of_nat(v___x_1627_);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1628_, v___f_1632_, v___x_1625_, v___x_1640_, v___x_1641_, v___x_1634_);
v_snd_1643_ = lean_ctor_get(v___x_1642_, 1);
lean_inc(v_snd_1643_);
lean_dec(v___x_1642_);
v___y_1581_ = v_snd_1643_;
goto v___jp_1580_;
}
}
v___jp_1580_:
{
size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v_sz_1582_ = lean_array_size(v___y_1581_);
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1579_, v___f_1577_, v_sz_1582_, v___x_1583_, v___y_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_7764__overap_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v_nsStx_1575_);
lean_dec_ref(v___f_1572_);
lean_dec_ref(v_inst_1548_);
lean_dec_ref(v_inst_1547_);
lean_dec(v_inst_1546_);
lean_dec_ref(v___x_1545_);
lean_dec(v_inst_1544_);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
lean_dec(v_inst_1530_);
lean_dec(v_toPure_1529_);
lean_inc_ref(v_inst_1538_);
v___f_1585_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1585_, 0, v_inst_1538_);
v___f_1586_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1586_, 0, v_inst_1538_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___f_1585_);
lean_ctor_set(v___x_1587_, 1, v___f_1586_);
v___x_7764__overap_1588_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1587_);
v___x_1589_ = lean_apply_1(v___x_7764__overap_1588_, v_ref_1550_);
lean_inc(v_toBind_1531_);
v___x_1590_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1589_, v___f_1573_);
v___x_1591_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1590_, v___f_1551_);
return v___x_1591_;
}
else
{
lean_object* v_val_1592_; lean_object* v___x_1593_; size_t v_sz_1594_; lean_object* v___x_1595_; lean_object* v_getEnv_1596_; lean_object* v_modifyEnv_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v___f_1573_);
v_val_1592_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1593_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1594_ = lean_array_size(v_val_1592_);
lean_inc(v_inst_1530_);
v___x_1595_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1539_, v_inst_1530_);
v_getEnv_1596_ = lean_ctor_get(v_inst_1540_, 0);
v_modifyEnv_1597_ = lean_ctor_get(v_inst_1540_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_inst_1540_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1599_ = v_inst_1540_;
v_isShared_1600_ = v_isSharedCheck_1624_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_modifyEnv_1597_);
lean_inc(v_getEnv_1596_);
lean_dec(v_inst_1540_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1624_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v_tos_1601_; lean_object* v_froms_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
lean_inc(v_val_1592_);
v_tos_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1593_, v___f_1541_, v_sz_1594_, v___x_1583_, v_val_1592_);
v_froms_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1593_, v___f_1542_, v_sz_1594_, v___x_1583_, v_val_1592_);
v___x_1603_ = lean_box(0);
v___x_1604_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1605_, 0, v_modifyEnv_1597_);
lean_closure_set(v___f_1605_, 1, v___x_1604_);
v___x_1606_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1606_, 0, lean_box(0));
lean_closure_set(v___x_1606_, 1, lean_box(0));
lean_closure_set(v___x_1606_, 2, lean_box(0));
lean_closure_set(v___x_1606_, 3, lean_box(0));
lean_closure_set(v___x_1606_, 4, v_getEnv_1596_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 1, v___f_1605_);
lean_ctor_set(v___x_1599_, 0, v___x_1606_);
v___x_1608_ = v___x_1599_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___f_1605_);
v___x_1608_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___f_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; lean_object* v___x_7793__overap_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc_ref(v_inst_1538_);
v___f_1609_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1609_, 0, v_inst_1538_);
v___f_1610_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1610_, 0, v_inst_1538_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___f_1609_);
lean_ctor_set(v___x_1611_, 1, v___f_1610_);
v___x_1612_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_1613_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1604_, v___x_1612_, v_inst_1543_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1614_, 0, v_inst_1544_);
lean_closure_set(v___f_1614_, 1, v___x_1604_);
lean_inc_ref_n(v___x_1545_, 2);
lean_inc_ref(v___f_1614_);
v___x_1615_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1614_, v___x_1545_);
lean_inc(v___x_1615_);
lean_inc_ref(v___x_1613_);
lean_inc_ref(v___x_1611_);
v___x_1616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1611_);
lean_ctor_set(v___x_1616_, 1, v___x_1613_);
lean_ctor_set(v___x_1616_, 2, v___x_1615_);
v___x_1617_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed__const__1));
lean_inc(v_nsStx_1575_);
lean_inc(v_ref_1550_);
lean_inc_ref(v___x_1595_);
lean_inc_ref(v___x_1616_);
lean_inc_ref(v___x_1608_);
lean_inc_n(v_toBind_1531_, 2);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_1618_, 0, v_inst_1546_);
lean_closure_set(v___f_1618_, 1, v___x_1604_);
lean_closure_set(v___f_1618_, 2, v_inst_1547_);
lean_closure_set(v___f_1618_, 3, v_froms_1602_);
lean_closure_set(v___f_1618_, 4, v_tos_1601_);
lean_closure_set(v___f_1618_, 5, v_toPure_1529_);
lean_closure_set(v___f_1618_, 6, v_inst_1548_);
lean_closure_set(v___f_1618_, 7, v_inst_1530_);
lean_closure_set(v___f_1618_, 8, v_toBind_1531_);
lean_closure_set(v___f_1618_, 9, v___x_1545_);
lean_closure_set(v___f_1618_, 10, v___x_1608_);
lean_closure_set(v___f_1618_, 11, v___x_1616_);
lean_closure_set(v___f_1618_, 12, v___x_1611_);
lean_closure_set(v___f_1618_, 13, v___x_1613_);
lean_closure_set(v___f_1618_, 14, v___x_1615_);
lean_closure_set(v___f_1618_, 15, v___f_1614_);
lean_closure_set(v___f_1618_, 16, v___x_1595_);
lean_closure_set(v___f_1618_, 17, v___x_1617_);
lean_closure_set(v___f_1618_, 18, v_ref_1550_);
lean_closure_set(v___f_1618_, 19, v___f_1572_);
lean_closure_set(v___f_1618_, 20, v___x_1603_);
lean_closure_set(v___f_1618_, 21, v_nsStx_1575_);
v___x_7793__overap_1619_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1545_, v___x_1595_, v___x_1608_, v___x_1616_, v_nsStx_1575_);
v___x_1620_ = lean_apply_1(v___x_7793__overap_1619_, v_ref_1550_);
v___x_1621_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1620_, v___f_1618_);
v___x_1622_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1621_, v___f_1551_);
return v___x_1622_;
}
}
}
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v_getEnv_1645_; lean_object* v_modifyEnv_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1676_; 
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1533_);
lean_inc(v_inst_1530_);
v___x_1644_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1539_, v_inst_1530_);
v_getEnv_1645_ = lean_ctor_get(v_inst_1540_, 0);
v_modifyEnv_1646_ = lean_ctor_get(v_inst_1540_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_inst_1540_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1648_ = v_inst_1540_;
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_modifyEnv_1646_);
lean_inc(v_getEnv_1645_);
lean_dec(v_inst_1540_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1676_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v_nsStx_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_ids_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_inc(v_ref_1550_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1650_, 0, v___f_1537_);
lean_closure_set(v___f_1650_, 1, v_ref_1550_);
v___x_1651_ = lean_unsigned_to_nat(0u);
v_nsStx_1652_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1651_);
v___x_1653_ = lean_unsigned_to_nat(2u);
v___x_1654_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1653_);
lean_dec(v_stx_1536_);
v___x_1655_ = lean_box(0);
v_ids_1656_ = l_Lean_Syntax_getArgs(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1657_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1658_, 0, v_modifyEnv_1646_);
lean_closure_set(v___f_1658_, 1, v___x_1657_);
v___x_1659_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1659_, 0, lean_box(0));
lean_closure_set(v___x_1659_, 1, lean_box(0));
lean_closure_set(v___x_1659_, 2, lean_box(0));
lean_closure_set(v___x_1659_, 3, lean_box(0));
lean_closure_set(v___x_1659_, 4, v_getEnv_1645_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___f_1658_);
lean_ctor_set(v___x_1648_, 0, v___x_1659_);
v___x_1661_ = v___x_1648_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___f_1658_);
v___x_1661_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; lean_object* v___x_7838__overap_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_inc_ref(v_inst_1538_);
v___f_1662_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1662_, 0, v_inst_1538_);
v___f_1663_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1663_, 0, v_inst_1538_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___f_1662_);
lean_ctor_set(v___x_1664_, 1, v___f_1663_);
v___x_1665_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_1666_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1657_, v___x_1665_, v_inst_1543_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1667_, 0, v_inst_1544_);
lean_closure_set(v___f_1667_, 1, v___x_1657_);
lean_inc_ref_n(v___x_1545_, 2);
lean_inc_ref(v___f_1667_);
v___x_1668_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1667_, v___x_1545_);
lean_inc(v___x_1668_);
lean_inc_ref(v___x_1666_);
lean_inc_ref(v___x_1664_);
v___x_1669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1664_);
lean_ctor_set(v___x_1669_, 1, v___x_1666_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
lean_inc(v_nsStx_1652_);
lean_inc_ref(v___x_1644_);
lean_inc_ref(v___x_1669_);
lean_inc_ref(v___x_1661_);
lean_inc_n(v_toBind_1531_, 2);
lean_inc(v_ref_1550_);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed), 22, 21);
lean_closure_set(v___f_1670_, 0, v_ids_1656_);
lean_closure_set(v___f_1670_, 1, v___f_1549_);
lean_closure_set(v___f_1670_, 2, v_inst_1530_);
lean_closure_set(v___f_1670_, 3, v_ref_1550_);
lean_closure_set(v___f_1670_, 4, v_toBind_1531_);
lean_closure_set(v___f_1670_, 5, v___f_1650_);
lean_closure_set(v___f_1670_, 6, v_inst_1546_);
lean_closure_set(v___f_1670_, 7, v___x_1657_);
lean_closure_set(v___f_1670_, 8, v_inst_1547_);
lean_closure_set(v___f_1670_, 9, v_toPure_1529_);
lean_closure_set(v___f_1670_, 10, v_inst_1548_);
lean_closure_set(v___f_1670_, 11, v___x_1545_);
lean_closure_set(v___f_1670_, 12, v___x_1661_);
lean_closure_set(v___f_1670_, 13, v___x_1669_);
lean_closure_set(v___f_1670_, 14, v___x_1664_);
lean_closure_set(v___f_1670_, 15, v___x_1666_);
lean_closure_set(v___f_1670_, 16, v___x_1668_);
lean_closure_set(v___f_1670_, 17, v___f_1667_);
lean_closure_set(v___f_1670_, 18, v___x_1644_);
lean_closure_set(v___f_1670_, 19, v___x_1655_);
lean_closure_set(v___f_1670_, 20, v_nsStx_1652_);
v___x_7838__overap_1671_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1545_, v___x_1644_, v___x_1661_, v___x_1669_, v_nsStx_1652_);
v___x_1672_ = lean_apply_1(v___x_7838__overap_1671_, v_ref_1550_);
v___x_1673_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1672_, v___f_1670_);
v___x_1674_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1673_, v___f_1551_);
return v___x_1674_;
}
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v_getEnv_1678_; lean_object* v_modifyEnv_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v___f_1549_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1533_);
lean_inc(v_inst_1530_);
v___x_1677_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1539_, v_inst_1530_);
v_getEnv_1678_ = lean_ctor_get(v_inst_1540_, 0);
v_modifyEnv_1679_ = lean_ctor_get(v_inst_1540_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_inst_1540_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1681_ = v_inst_1540_;
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_modifyEnv_1679_);
lean_inc(v_getEnv_1678_);
lean_dec(v_inst_1540_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1708_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v_ns_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_ids_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_inc(v_ref_1550_);
v___f_1683_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1683_, 0, v___f_1537_);
lean_closure_set(v___f_1683_, 1, v_ref_1550_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_ns_1685_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1684_);
v___x_1686_ = lean_unsigned_to_nat(2u);
v___x_1687_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1686_);
lean_dec(v_stx_1536_);
v_ids_1688_ = l_Lean_Syntax_getArgs(v___x_1687_);
lean_dec(v___x_1687_);
v___x_1689_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1690_, 0, v_modifyEnv_1679_);
lean_closure_set(v___f_1690_, 1, v___x_1689_);
v___x_1691_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1691_, 0, lean_box(0));
lean_closure_set(v___x_1691_, 1, lean_box(0));
lean_closure_set(v___x_1691_, 2, lean_box(0));
lean_closure_set(v___x_1691_, 3, lean_box(0));
lean_closure_set(v___x_1691_, 4, v_getEnv_1678_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___f_1690_);
lean_ctor_set(v___x_1681_, 0, v___x_1691_);
v___x_1693_ = v___x_1681_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___f_1690_);
v___x_1693_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_7859__overap_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_inc_ref(v_inst_1538_);
v___f_1694_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1694_, 0, v_inst_1538_);
v___f_1695_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1695_, 0, v_inst_1538_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___f_1694_);
lean_ctor_set(v___x_1696_, 1, v___f_1695_);
v___x_1697_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_1698_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1689_, v___x_1697_, v_inst_1543_);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1699_, 0, v_inst_1544_);
lean_closure_set(v___f_1699_, 1, v___x_1689_);
lean_inc_ref_n(v___x_1545_, 2);
lean_inc_ref(v___f_1699_);
v___x_1700_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1699_, v___x_1545_);
lean_inc(v___x_1700_);
lean_inc_ref(v___x_1698_);
lean_inc_ref(v___x_1696_);
v___x_1701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1696_);
lean_ctor_set(v___x_1701_, 1, v___x_1698_);
lean_ctor_set(v___x_1701_, 2, v___x_1700_);
lean_inc(v_ns_1685_);
lean_inc(v_ref_1550_);
lean_inc_ref(v___x_1677_);
lean_inc_ref(v___x_1701_);
lean_inc_ref(v___x_1693_);
lean_inc_n(v_toBind_1531_, 2);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed), 20, 19);
lean_closure_set(v___f_1702_, 0, v_inst_1546_);
lean_closure_set(v___f_1702_, 1, v___x_1689_);
lean_closure_set(v___f_1702_, 2, v_inst_1547_);
lean_closure_set(v___f_1702_, 3, v_toPure_1529_);
lean_closure_set(v___f_1702_, 4, v_inst_1548_);
lean_closure_set(v___f_1702_, 5, v_inst_1530_);
lean_closure_set(v___f_1702_, 6, v_toBind_1531_);
lean_closure_set(v___f_1702_, 7, v___x_1545_);
lean_closure_set(v___f_1702_, 8, v___x_1693_);
lean_closure_set(v___f_1702_, 9, v___x_1701_);
lean_closure_set(v___f_1702_, 10, v___x_1696_);
lean_closure_set(v___f_1702_, 11, v___x_1698_);
lean_closure_set(v___f_1702_, 12, v___x_1700_);
lean_closure_set(v___f_1702_, 13, v___f_1699_);
lean_closure_set(v___f_1702_, 14, v___x_1677_);
lean_closure_set(v___f_1702_, 15, v_ids_1688_);
lean_closure_set(v___f_1702_, 16, v_ref_1550_);
lean_closure_set(v___f_1702_, 17, v___f_1683_);
lean_closure_set(v___f_1702_, 18, v_ns_1685_);
v___x_7859__overap_1703_ = l_Lean_resolveNamespace___redArg(v___x_1545_, v___x_1677_, v___x_1693_, v___x_1701_, v_ns_1685_);
v___x_1704_ = lean_apply_1(v___x_7859__overap_1703_, v_ref_1550_);
v___x_1705_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1704_, v___f_1702_);
v___x_1706_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1705_, v___f_1551_);
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v_nss_1712_; lean_object* v___x_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; size_t v_sz_1716_; size_t v___x_1717_; lean_object* v___x_7870__overap_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___f_1549_);
lean_dec_ref(v_inst_1548_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1533_);
lean_inc(v_ref_1550_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1709_, 0, v___f_1537_);
lean_closure_set(v___f_1709_, 1, v_ref_1550_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1710_);
lean_dec(v_stx_1536_);
v_nss_1712_ = l_Lean_Syntax_getArgs(v___x_1711_);
lean_dec(v___x_1711_);
v___x_1713_ = lean_box(0);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1714_, 0, v___x_1713_);
lean_closure_set(v___f_1714_, 1, v_toPure_1529_);
lean_inc_ref(v___f_1714_);
lean_inc_n(v_toBind_1531_, 2);
lean_inc_ref(v___x_1545_);
v___f_1715_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed), 17, 13);
lean_closure_set(v___f_1715_, 0, v_inst_1539_);
lean_closure_set(v___f_1715_, 1, v_inst_1530_);
lean_closure_set(v___f_1715_, 2, v_inst_1540_);
lean_closure_set(v___f_1715_, 3, v___x_1545_);
lean_closure_set(v___f_1715_, 4, v_toBind_1531_);
lean_closure_set(v___f_1715_, 5, v___f_1714_);
lean_closure_set(v___f_1715_, 6, v_inst_1538_);
lean_closure_set(v___f_1715_, 7, v_inst_1543_);
lean_closure_set(v___f_1715_, 8, v_inst_1544_);
lean_closure_set(v___f_1715_, 9, v___x_1713_);
lean_closure_set(v___f_1715_, 10, v___f_1714_);
lean_closure_set(v___f_1715_, 11, v_inst_1546_);
lean_closure_set(v___f_1715_, 12, v_inst_1547_);
v_sz_1716_ = lean_array_size(v_nss_1712_);
v___x_1717_ = ((size_t)0ULL);
v___x_7870__overap_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1545_, v_nss_1712_, v___f_1715_, v_sz_1716_, v___x_1717_, v___x_1713_);
v___x_1719_ = lean_apply_1(v___x_7870__overap_1718_, v_ref_1550_);
v___x_1720_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1719_, v___f_1709_);
v___x_1721_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1720_, v___f_1551_);
return v___x_1721_;
}
}
else
{
lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_nss_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___f_1729_; size_t v_sz_1730_; size_t v___x_1731_; lean_object* v___x_7882__overap_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v___f_1549_);
lean_dec_ref(v_inst_1548_);
lean_dec_ref(v___f_1542_);
lean_dec_ref(v___f_1541_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1534_);
lean_dec_ref(v___x_1533_);
lean_inc(v_ref_1550_);
v___f_1722_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1722_, 0, v___f_1537_);
lean_closure_set(v___f_1722_, 1, v_ref_1550_);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = l_Lean_Syntax_getArg(v_stx_1536_, v___x_1723_);
lean_dec(v_stx_1536_);
v___x_1725_ = lean_box(0);
v_nss_1726_ = l_Lean_Syntax_getArgs(v___x_1724_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v___f_1728_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1728_, 0, v___x_1727_);
lean_closure_set(v___f_1728_, 1, v_toPure_1529_);
lean_inc_ref(v___f_1728_);
lean_inc_n(v_toBind_1531_, 2);
lean_inc_ref(v___x_1545_);
v___f_1729_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed), 18, 14);
lean_closure_set(v___f_1729_, 0, v_inst_1539_);
lean_closure_set(v___f_1729_, 1, v_inst_1530_);
lean_closure_set(v___f_1729_, 2, v_inst_1540_);
lean_closure_set(v___f_1729_, 3, v___x_1545_);
lean_closure_set(v___f_1729_, 4, v_toBind_1531_);
lean_closure_set(v___f_1729_, 5, v___f_1728_);
lean_closure_set(v___f_1729_, 6, v___x_1725_);
lean_closure_set(v___f_1729_, 7, v_inst_1538_);
lean_closure_set(v___f_1729_, 8, v_inst_1543_);
lean_closure_set(v___f_1729_, 9, v_inst_1544_);
lean_closure_set(v___f_1729_, 10, v___x_1727_);
lean_closure_set(v___f_1729_, 11, v___f_1728_);
lean_closure_set(v___f_1729_, 12, v_inst_1546_);
lean_closure_set(v___f_1729_, 13, v_inst_1547_);
v_sz_1730_ = lean_array_size(v_nss_1726_);
v___x_1731_ = ((size_t)0ULL);
v___x_7882__overap_1732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1545_, v_nss_1726_, v___f_1729_, v_sz_1730_, v___x_1731_, v___x_1727_);
v___x_1733_ = lean_apply_1(v___x_7882__overap_1732_, v_ref_1550_);
v___x_1734_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1733_, v___f_1722_);
v___x_1735_ = lean_apply_4(v_toBind_1531_, lean_box(0), lean_box(0), v___x_1734_, v___f_1551_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object** _args){
lean_object* v_toPure_1736_ = _args[0];
lean_object* v_inst_1737_ = _args[1];
lean_object* v_toBind_1738_ = _args[2];
lean_object* v___x_1739_ = _args[3];
lean_object* v___x_1740_ = _args[4];
lean_object* v___x_1741_ = _args[5];
lean_object* v___x_1742_ = _args[6];
lean_object* v_stx_1743_ = _args[7];
lean_object* v___f_1744_ = _args[8];
lean_object* v_inst_1745_ = _args[9];
lean_object* v_inst_1746_ = _args[10];
lean_object* v_inst_1747_ = _args[11];
lean_object* v___f_1748_ = _args[12];
lean_object* v___f_1749_ = _args[13];
lean_object* v_inst_1750_ = _args[14];
lean_object* v_inst_1751_ = _args[15];
lean_object* v___x_1752_ = _args[16];
lean_object* v_inst_1753_ = _args[17];
lean_object* v_inst_1754_ = _args[18];
lean_object* v_inst_1755_ = _args[19];
lean_object* v___f_1756_ = _args[20];
lean_object* v_ref_1757_ = _args[21];
_start:
{
uint8_t v___x_9407__boxed_1758_; lean_object* v_res_1759_; 
v___x_9407__boxed_1758_ = lean_unbox(v___x_1739_);
v_res_1759_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(v_toPure_1736_, v_inst_1737_, v_toBind_1738_, v___x_9407__boxed_1758_, v___x_1740_, v___x_1741_, v___x_1742_, v_stx_1743_, v___f_1744_, v_inst_1745_, v_inst_1746_, v_inst_1747_, v___f_1748_, v___f_1749_, v_inst_1750_, v_inst_1751_, v___x_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v___f_1756_, v_ref_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v_toPure_1760_, lean_object* v_____x_1761_){
_start:
{
lean_object* v_fst_1762_; lean_object* v___x_1763_; 
v_fst_1762_ = lean_ctor_get(v_____x_1761_, 0);
lean_inc(v_fst_1762_);
lean_dec_ref(v_____x_1761_);
v___x_1763_ = lean_apply_2(v_toPure_1760_, lean_box(0), v_fst_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(lean_object* v_toApplicative_1773_, lean_object* v_stx_1774_, lean_object* v_____do__lift_1775_, lean_object* v_inst_1776_, lean_object* v_toBind_1777_, lean_object* v___f_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v___f_1782_, lean_object* v___f_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v___x_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v___f_1790_, lean_object* v_____do__lift_1791_){
_start:
{
lean_object* v_toPure_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___f_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_toPure_1792_ = lean_ctor_get(v_toApplicative_1773_, 1);
lean_inc_n(v_toPure_1792_, 2);
lean_dec_ref(v_toApplicative_1773_);
v___x_1793_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0));
v___x_1794_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1));
v___x_1795_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2));
v___x_1796_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4));
lean_inc(v_stx_1774_);
v___x_1797_ = l_Lean_Syntax_isOfKind(v_stx_1774_, v___x_1796_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_____do__lift_1775_);
lean_ctor_set(v___x_1798_, 1, v_____do__lift_1791_);
v___x_1799_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1799_, 0, lean_box(0));
lean_closure_set(v___x_1799_, 1, lean_box(0));
lean_closure_set(v___x_1799_, 2, v___x_1798_);
lean_inc(v_inst_1776_);
v___x_1800_ = lean_apply_2(v_inst_1776_, lean_box(0), v___x_1799_);
v___x_1801_ = lean_box(v___x_1797_);
lean_inc_n(v_toBind_1777_, 2);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed), 22, 21);
lean_closure_set(v___f_1802_, 0, v_toPure_1792_);
lean_closure_set(v___f_1802_, 1, v_inst_1776_);
lean_closure_set(v___f_1802_, 2, v_toBind_1777_);
lean_closure_set(v___f_1802_, 3, v___x_1801_);
lean_closure_set(v___f_1802_, 4, v___x_1793_);
lean_closure_set(v___f_1802_, 5, v___x_1794_);
lean_closure_set(v___f_1802_, 6, v___x_1795_);
lean_closure_set(v___f_1802_, 7, v_stx_1774_);
lean_closure_set(v___f_1802_, 8, v___f_1778_);
lean_closure_set(v___f_1802_, 9, v_inst_1779_);
lean_closure_set(v___f_1802_, 10, v_inst_1780_);
lean_closure_set(v___f_1802_, 11, v_inst_1781_);
lean_closure_set(v___f_1802_, 12, v___f_1782_);
lean_closure_set(v___f_1802_, 13, v___f_1783_);
lean_closure_set(v___f_1802_, 14, v_inst_1784_);
lean_closure_set(v___f_1802_, 15, v_inst_1785_);
lean_closure_set(v___f_1802_, 16, v___x_1786_);
lean_closure_set(v___f_1802_, 17, v_inst_1787_);
lean_closure_set(v___f_1802_, 18, v_inst_1788_);
lean_closure_set(v___f_1802_, 19, v_inst_1789_);
lean_closure_set(v___f_1802_, 20, v___f_1790_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38), 2, 1);
lean_closure_set(v___f_1803_, 0, v_toPure_1792_);
v___x_1804_ = lean_apply_4(v_toBind_1777_, lean_box(0), lean_box(0), v___x_1800_, v___f_1802_);
v___x_1805_ = lean_apply_4(v_toBind_1777_, lean_box(0), lean_box(0), v___x_1804_, v___f_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed(lean_object** _args){
lean_object* v_toApplicative_1806_ = _args[0];
lean_object* v_stx_1807_ = _args[1];
lean_object* v_____do__lift_1808_ = _args[2];
lean_object* v_inst_1809_ = _args[3];
lean_object* v_toBind_1810_ = _args[4];
lean_object* v___f_1811_ = _args[5];
lean_object* v_inst_1812_ = _args[6];
lean_object* v_inst_1813_ = _args[7];
lean_object* v_inst_1814_ = _args[8];
lean_object* v___f_1815_ = _args[9];
lean_object* v___f_1816_ = _args[10];
lean_object* v_inst_1817_ = _args[11];
lean_object* v_inst_1818_ = _args[12];
lean_object* v___x_1819_ = _args[13];
lean_object* v_inst_1820_ = _args[14];
lean_object* v_inst_1821_ = _args[15];
lean_object* v_inst_1822_ = _args[16];
lean_object* v___f_1823_ = _args[17];
lean_object* v_____do__lift_1824_ = _args[18];
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(v_toApplicative_1806_, v_stx_1807_, v_____do__lift_1808_, v_inst_1809_, v_toBind_1810_, v___f_1811_, v_inst_1812_, v_inst_1813_, v_inst_1814_, v___f_1815_, v___f_1816_, v_inst_1817_, v_inst_1818_, v___x_1819_, v_inst_1820_, v_inst_1821_, v_inst_1822_, v___f_1823_, v_____do__lift_1824_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object* v_toApplicative_1826_, lean_object* v_stx_1827_, lean_object* v_inst_1828_, lean_object* v_toBind_1829_, lean_object* v___f_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v___f_1834_, lean_object* v___f_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v___x_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v___f_1842_, lean_object* v_getCurrNamespace_1843_, lean_object* v_____do__lift_1844_){
_start:
{
lean_object* v___f_1845_; lean_object* v___x_1846_; 
lean_inc(v_toBind_1829_);
v___f_1845_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed), 19, 18);
lean_closure_set(v___f_1845_, 0, v_toApplicative_1826_);
lean_closure_set(v___f_1845_, 1, v_stx_1827_);
lean_closure_set(v___f_1845_, 2, v_____do__lift_1844_);
lean_closure_set(v___f_1845_, 3, v_inst_1828_);
lean_closure_set(v___f_1845_, 4, v_toBind_1829_);
lean_closure_set(v___f_1845_, 5, v___f_1830_);
lean_closure_set(v___f_1845_, 6, v_inst_1831_);
lean_closure_set(v___f_1845_, 7, v_inst_1832_);
lean_closure_set(v___f_1845_, 8, v_inst_1833_);
lean_closure_set(v___f_1845_, 9, v___f_1834_);
lean_closure_set(v___f_1845_, 10, v___f_1835_);
lean_closure_set(v___f_1845_, 11, v_inst_1836_);
lean_closure_set(v___f_1845_, 12, v_inst_1837_);
lean_closure_set(v___f_1845_, 13, v___x_1838_);
lean_closure_set(v___f_1845_, 14, v_inst_1839_);
lean_closure_set(v___f_1845_, 15, v_inst_1840_);
lean_closure_set(v___f_1845_, 16, v_inst_1841_);
lean_closure_set(v___f_1845_, 17, v___f_1842_);
v___x_1846_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v_getCurrNamespace_1843_, v___f_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object** _args){
lean_object* v_toApplicative_1847_ = _args[0];
lean_object* v_stx_1848_ = _args[1];
lean_object* v_inst_1849_ = _args[2];
lean_object* v_toBind_1850_ = _args[3];
lean_object* v___f_1851_ = _args[4];
lean_object* v_inst_1852_ = _args[5];
lean_object* v_inst_1853_ = _args[6];
lean_object* v_inst_1854_ = _args[7];
lean_object* v___f_1855_ = _args[8];
lean_object* v___f_1856_ = _args[9];
lean_object* v_inst_1857_ = _args[10];
lean_object* v_inst_1858_ = _args[11];
lean_object* v___x_1859_ = _args[12];
lean_object* v_inst_1860_ = _args[13];
lean_object* v_inst_1861_ = _args[14];
lean_object* v_inst_1862_ = _args[15];
lean_object* v___f_1863_ = _args[16];
lean_object* v_getCurrNamespace_1864_ = _args[17];
lean_object* v_____do__lift_1865_ = _args[18];
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(v_toApplicative_1847_, v_stx_1848_, v_inst_1849_, v_toBind_1850_, v___f_1851_, v_inst_1852_, v_inst_1853_, v_inst_1854_, v___f_1855_, v___f_1856_, v_inst_1857_, v_inst_1858_, v___x_1859_, v_inst_1860_, v_inst_1861_, v_inst_1862_, v___f_1863_, v_getCurrNamespace_1864_, v_____do__lift_1865_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_inst_1878_, lean_object* v_inst_1879_, lean_object* v_stx_1880_){
_start:
{
lean_object* v_toApplicative_1881_; lean_object* v_toBind_1882_; lean_object* v_getCurrNamespace_1883_; lean_object* v_getOpenDecls_1884_; lean_object* v___f_1885_; lean_object* v___f_1886_; lean_object* v___f_1887_; lean_object* v___f_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
v_toApplicative_1881_ = lean_ctor_get(v_inst_1870_, 0);
lean_inc_ref_n(v_toApplicative_1881_, 2);
v_toBind_1882_ = lean_ctor_get(v_inst_1870_, 1);
lean_inc_n(v_toBind_1882_, 3);
v_getCurrNamespace_1883_ = lean_ctor_get(v_inst_1878_, 0);
lean_inc(v_getCurrNamespace_1883_);
v_getOpenDecls_1884_ = lean_ctor_get(v_inst_1878_, 1);
lean_inc(v_getOpenDecls_1884_);
lean_dec_ref(v_inst_1878_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1885_, 0, v_toApplicative_1881_);
lean_inc(v_inst_1875_);
v___f_1886_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1886_, 0, v_inst_1875_);
lean_closure_set(v___f_1886_, 1, v_toBind_1882_);
lean_closure_set(v___f_1886_, 2, v___f_1885_);
v___f_1887_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0));
v___f_1888_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1));
v___f_1889_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2));
lean_inc_ref(v_inst_1870_);
v___x_1890_ = l_StateRefT_x27_instMonad___redArg(v_inst_1870_);
v___f_1891_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed), 19, 18);
lean_closure_set(v___f_1891_, 0, v_toApplicative_1881_);
lean_closure_set(v___f_1891_, 1, v_stx_1880_);
lean_closure_set(v___f_1891_, 2, v_inst_1875_);
lean_closure_set(v___f_1891_, 3, v_toBind_1882_);
lean_closure_set(v___f_1891_, 4, v___f_1886_);
lean_closure_set(v___f_1891_, 5, v_inst_1872_);
lean_closure_set(v___f_1891_, 6, v_inst_1870_);
lean_closure_set(v___f_1891_, 7, v_inst_1871_);
lean_closure_set(v___f_1891_, 8, v___f_1887_);
lean_closure_set(v___f_1891_, 9, v___f_1888_);
lean_closure_set(v___f_1891_, 10, v_inst_1873_);
lean_closure_set(v___f_1891_, 11, v_inst_1874_);
lean_closure_set(v___f_1891_, 12, v___x_1890_);
lean_closure_set(v___f_1891_, 13, v_inst_1877_);
lean_closure_set(v___f_1891_, 14, v_inst_1876_);
lean_closure_set(v___f_1891_, 15, v_inst_1879_);
lean_closure_set(v___f_1891_, 16, v___f_1889_);
lean_closure_set(v___f_1891_, 17, v_getCurrNamespace_1883_);
v___x_1892_ = lean_apply_4(v_toBind_1882_, lean_box(0), lean_box(0), v_getOpenDecls_1884_, v___f_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1893_, lean_object* v_inst_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_stx_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1894_, v_inst_1895_, v_inst_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_inst_1900_, v_inst_1901_, v_inst_1902_, v_inst_1903_, v_stx_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object* v_a_1906_, lean_object* v_toPure_1907_, lean_object* v_s_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_a_1906_);
lean_ctor_set(v___x_1909_, 1, v_s_1908_);
v___x_1910_ = lean_apply_2(v_toPure_1907_, lean_box(0), v___x_1909_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object* v_toPure_1911_, lean_object* v_ref_1912_, lean_object* v_inst_1913_, lean_object* v_toBind_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1916_, 0, v_a_1915_);
lean_closure_set(v___f_1916_, 1, v_toPure_1911_);
v___x_1917_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1917_, 0, lean_box(0));
lean_closure_set(v___x_1917_, 1, lean_box(0));
lean_closure_set(v___x_1917_, 2, v_ref_1912_);
v___x_1918_ = lean_apply_2(v_inst_1913_, lean_box(0), v___x_1917_);
v___x_1919_ = lean_apply_4(v_toBind_1914_, lean_box(0), lean_box(0), v___x_1918_, v___f_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object* v_toPure_1920_, lean_object* v_inst_1921_, lean_object* v_toBind_1922_, lean_object* v___x_1923_, lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v___x_1926_, lean_object* v___x_1927_, lean_object* v___f_1928_, lean_object* v___x_1929_, lean_object* v___x_1930_, lean_object* v___x_1931_, lean_object* v_nss_1932_, lean_object* v_idStx_1933_, lean_object* v_ref_1934_){
_start:
{
lean_object* v___f_1935_; lean_object* v___x_100__overap_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_inc(v_toBind_1922_);
lean_inc(v_ref_1934_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1935_, 0, v_toPure_1920_);
lean_closure_set(v___f_1935_, 1, v_ref_1934_);
lean_closure_set(v___f_1935_, 2, v_inst_1921_);
lean_closure_set(v___f_1935_, 3, v_toBind_1922_);
v___x_100__overap_1936_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1923_, v___x_1924_, v___x_1925_, v___x_1926_, v___x_1927_, v___f_1928_, v___x_1929_, v___x_1930_, v___x_1931_, v_nss_1932_, v_idStx_1933_);
v___x_1937_ = lean_apply_1(v___x_100__overap_1936_, v_ref_1934_);
v___x_1938_ = lean_apply_4(v_toBind_1922_, lean_box(0), lean_box(0), v___x_1937_, v___f_1935_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object* v_toPure_1939_, lean_object* v_____x_1940_){
_start:
{
lean_object* v_fst_1941_; lean_object* v___x_1942_; 
v_fst_1941_ = lean_ctor_get(v_____x_1940_, 0);
lean_inc(v_fst_1941_);
lean_dec_ref(v_____x_1940_);
v___x_1942_ = lean_apply_2(v_toPure_1939_, lean_box(0), v_fst_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object* v_toApplicative_1943_, lean_object* v_____do__lift_1944_, lean_object* v_inst_1945_, lean_object* v_toBind_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v___x_1950_, lean_object* v___x_1951_, lean_object* v___f_1952_, lean_object* v___x_1953_, lean_object* v___x_1954_, lean_object* v___x_1955_, lean_object* v_nss_1956_, lean_object* v_idStx_1957_, lean_object* v_____do__lift_1958_){
_start:
{
lean_object* v_toPure_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_toPure_1959_ = lean_ctor_get(v_toApplicative_1943_, 1);
lean_inc_n(v_toPure_1959_, 2);
lean_dec_ref(v_toApplicative_1943_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_____do__lift_1944_);
lean_ctor_set(v___x_1960_, 1, v_____do__lift_1958_);
v___x_1961_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1961_, 0, lean_box(0));
lean_closure_set(v___x_1961_, 1, lean_box(0));
lean_closure_set(v___x_1961_, 2, v___x_1960_);
lean_inc(v_inst_1945_);
v___x_1962_ = lean_apply_2(v_inst_1945_, lean_box(0), v___x_1961_);
lean_inc_n(v_toBind_1946_, 2);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2), 15, 14);
lean_closure_set(v___f_1963_, 0, v_toPure_1959_);
lean_closure_set(v___f_1963_, 1, v_inst_1945_);
lean_closure_set(v___f_1963_, 2, v_toBind_1946_);
lean_closure_set(v___f_1963_, 3, v___x_1947_);
lean_closure_set(v___f_1963_, 4, v___x_1948_);
lean_closure_set(v___f_1963_, 5, v___x_1949_);
lean_closure_set(v___f_1963_, 6, v___x_1950_);
lean_closure_set(v___f_1963_, 7, v___x_1951_);
lean_closure_set(v___f_1963_, 8, v___f_1952_);
lean_closure_set(v___f_1963_, 9, v___x_1953_);
lean_closure_set(v___f_1963_, 10, v___x_1954_);
lean_closure_set(v___f_1963_, 11, v___x_1955_);
lean_closure_set(v___f_1963_, 12, v_nss_1956_);
lean_closure_set(v___f_1963_, 13, v_idStx_1957_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1964_, 0, v_toPure_1959_);
v___x_1965_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1962_, v___f_1963_);
v___x_1966_ = lean_apply_4(v_toBind_1946_, lean_box(0), lean_box(0), v___x_1965_, v___f_1964_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object* v_toApplicative_1967_, lean_object* v_inst_1968_, lean_object* v_toBind_1969_, lean_object* v___x_1970_, lean_object* v___x_1971_, lean_object* v___x_1972_, lean_object* v___x_1973_, lean_object* v___x_1974_, lean_object* v___f_1975_, lean_object* v___x_1976_, lean_object* v___x_1977_, lean_object* v___x_1978_, lean_object* v_nss_1979_, lean_object* v_idStx_1980_, lean_object* v_getCurrNamespace_1981_, lean_object* v_____do__lift_1982_){
_start:
{
lean_object* v___f_1983_; lean_object* v___x_1984_; 
lean_inc(v_toBind_1969_);
v___f_1983_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4), 16, 15);
lean_closure_set(v___f_1983_, 0, v_toApplicative_1967_);
lean_closure_set(v___f_1983_, 1, v_____do__lift_1982_);
lean_closure_set(v___f_1983_, 2, v_inst_1968_);
lean_closure_set(v___f_1983_, 3, v_toBind_1969_);
lean_closure_set(v___f_1983_, 4, v___x_1970_);
lean_closure_set(v___f_1983_, 5, v___x_1971_);
lean_closure_set(v___f_1983_, 6, v___x_1972_);
lean_closure_set(v___f_1983_, 7, v___x_1973_);
lean_closure_set(v___f_1983_, 8, v___x_1974_);
lean_closure_set(v___f_1983_, 9, v___f_1975_);
lean_closure_set(v___f_1983_, 10, v___x_1976_);
lean_closure_set(v___f_1983_, 11, v___x_1977_);
lean_closure_set(v___f_1983_, 12, v___x_1978_);
lean_closure_set(v___f_1983_, 13, v_nss_1979_);
lean_closure_set(v___f_1983_, 14, v_idStx_1980_);
v___x_1984_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v_getCurrNamespace_1981_, v___f_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_nss_1994_, lean_object* v_idStx_1995_){
_start:
{
lean_object* v_toApplicative_1996_; lean_object* v_toBind_1997_; lean_object* v_getCurrNamespace_1998_; lean_object* v_getOpenDecls_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2030_; 
v_toApplicative_1996_ = lean_ctor_get(v_inst_1985_, 0);
lean_inc_ref(v_toApplicative_1996_);
v_toBind_1997_ = lean_ctor_get(v_inst_1985_, 1);
lean_inc(v_toBind_1997_);
v_getCurrNamespace_1998_ = lean_ctor_get(v_inst_1993_, 0);
v_getOpenDecls_1999_ = lean_ctor_get(v_inst_1993_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_inst_1993_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2001_ = v_inst_1993_;
v_isShared_2002_ = v_isSharedCheck_2030_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_getOpenDecls_1999_);
lean_inc(v_getCurrNamespace_1998_);
lean_dec(v_inst_1993_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2030_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v_getEnv_2004_; lean_object* v_modifyEnv_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2029_; 
lean_inc_ref(v_inst_1985_);
v___x_2003_ = l_StateRefT_x27_instMonad___redArg(v_inst_1985_);
v_getEnv_2004_ = lean_ctor_get(v_inst_1986_, 0);
v_modifyEnv_2005_ = lean_ctor_get(v_inst_1986_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_inst_1986_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2007_ = v_inst_1986_;
v_isShared_2008_ = v_isSharedCheck_2029_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_modifyEnv_2005_);
lean_inc(v_getEnv_2004_);
lean_dec(v_inst_1986_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2029_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2009_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__0));
v___f_2010_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2010_, 0, v_modifyEnv_2005_);
lean_closure_set(v___f_2010_, 1, v___x_2009_);
v___x_2011_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_2011_, 0, lean_box(0));
lean_closure_set(v___x_2011_, 1, lean_box(0));
lean_closure_set(v___x_2011_, 2, lean_box(0));
lean_closure_set(v___x_2011_, 3, lean_box(0));
lean_closure_set(v___x_2011_, 4, v_getEnv_2004_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 1, v___f_2010_);
lean_ctor_set(v___x_2007_, 0, v___x_2011_);
v___x_2013_ = v___x_2007_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___f_2010_);
v___x_2013_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___x_2017_; 
lean_inc_ref(v_inst_1987_);
v___f_2014_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2014_, 0, v_inst_1987_);
v___f_2015_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_2015_, 0, v_inst_1987_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___f_2015_);
lean_ctor_set(v___x_2001_, 0, v___f_2014_);
v___x_2017_ = v___x_2001_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___f_2014_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___f_2015_);
v___x_2017_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; 
v___x_2018_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___closed__1));
v___x_2019_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_2009_, v___x_2018_, v_inst_1988_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2020_, 0, v_inst_1989_);
lean_closure_set(v___f_2020_, 1, v___x_2009_);
lean_inc_ref(v___x_2003_);
lean_inc_ref(v___f_2020_);
v___x_2021_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2020_, v___x_2003_);
v___x_2022_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2009_, v_inst_1991_);
v___x_2023_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_2023_, 0, lean_box(0));
lean_closure_set(v___x_2023_, 1, lean_box(0));
lean_closure_set(v___x_2023_, 2, lean_box(0));
lean_closure_set(v___x_2023_, 3, lean_box(0));
lean_closure_set(v___x_2023_, 4, v_inst_1992_);
lean_inc(v_inst_1990_);
v___x_2024_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1985_, v_inst_1990_);
lean_inc(v_toBind_1997_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5), 16, 15);
lean_closure_set(v___f_2025_, 0, v_toApplicative_1996_);
lean_closure_set(v___f_2025_, 1, v_inst_1990_);
lean_closure_set(v___f_2025_, 2, v_toBind_1997_);
lean_closure_set(v___f_2025_, 3, v___x_2003_);
lean_closure_set(v___f_2025_, 4, v___x_2013_);
lean_closure_set(v___f_2025_, 5, v___x_2017_);
lean_closure_set(v___f_2025_, 6, v___x_2019_);
lean_closure_set(v___f_2025_, 7, v___x_2021_);
lean_closure_set(v___f_2025_, 8, v___f_2020_);
lean_closure_set(v___f_2025_, 9, v___x_2022_);
lean_closure_set(v___f_2025_, 10, v___x_2023_);
lean_closure_set(v___f_2025_, 11, v___x_2024_);
lean_closure_set(v___f_2025_, 12, v_nss_1994_);
lean_closure_set(v___f_2025_, 13, v_idStx_1995_);
lean_closure_set(v___f_2025_, 14, v_getCurrNamespace_1998_);
v___x_2026_ = lean_apply_4(v_toBind_1997_, lean_box(0), lean_box(0), v_getOpenDecls_1999_, v___f_2025_);
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object* v_m_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_nss_2041_, lean_object* v_idStx_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(v_inst_2032_, v_inst_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_inst_2040_, v_nss_2041_, v_idStx_2042_);
return v___x_2043_;
}
}
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Open(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
