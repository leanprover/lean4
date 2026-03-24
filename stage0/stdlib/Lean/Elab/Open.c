// Lean compiler output
// Module: Lean.Elab.Open
// Imports: public import Lean.Elab.Util public import Lean.Parser.Command meta import Lean.Parser.Command import Init.Omega
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
lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Option_bind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__0(lean_object*, lean_object*);
lean_object* l_instFunctorOption___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "openOnly"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openHiding"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "openRenaming"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadOption___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instFunctorOption___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_map, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__9_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__8_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__10_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__4_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__5_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__6_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__7_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_bind, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__11_value),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__12_value)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13_value;
static const lean_array_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openSimple"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__3_value),LEAN_SCALAR_PTR_LITERAL(171, 238, 134, 92, 162, 110, 43, 67)}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object**);
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
lean_inc_ref(v_inst_23_);
v___f_25_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_25_, 0, v_inst_23_);
lean_inc_ref(v_inst_23_);
v___f_26_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_26_, 0, v_inst_23_);
v___x_27_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_27_, 0, lean_box(0));
lean_closure_set(v___x_27_, 1, lean_box(0));
lean_closure_set(v___x_27_, 2, lean_box(0));
lean_closure_set(v___x_27_, 3, v_inst_24_);
lean_inc_ref(v___x_27_);
lean_inc_ref(v_inst_23_);
v___x_28_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_28_, 0, lean_box(0));
lean_closure_set(v___x_28_, 1, lean_box(0));
lean_closure_set(v___x_28_, 2, lean_box(0));
lean_closure_set(v___x_28_, 3, v_inst_23_);
lean_closure_set(v___x_28_, 4, lean_box(0));
lean_closure_set(v___x_28_, 5, lean_box(0));
lean_closure_set(v___x_28_, 6, v___x_27_);
lean_closure_set(v___x_28_, 7, v___f_25_);
v___x_29_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_29_, 0, lean_box(0));
lean_closure_set(v___x_29_, 1, lean_box(0));
lean_closure_set(v___x_29_, 2, lean_box(0));
lean_closure_set(v___x_29_, 3, v_inst_23_);
lean_closure_set(v___x_29_, 4, lean_box(0));
lean_closure_set(v___x_29_, 5, lean_box(0));
lean_closure_set(v___x_29_, 6, v___x_27_);
lean_closure_set(v___x_29_, 7, v___f_26_);
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
lean_inc(v_toBind_82_);
v_getEnv_83_ = lean_ctor_get(v_inst_71_, 0);
lean_inc(v_getEnv_83_);
v___x_84_ = l_Lean_Syntax_getId(v_idStx_80_);
v_declName_85_ = l_Lean_Name_append(v_ns_79_, v___x_84_);
lean_inc(v_toBind_82_);
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
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v___y_185_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v___y_185_);
v_tryCatch_188_ = lean_ctor_get(v_inst_170_, 1);
lean_inc(v_tryCatch_188_);
lean_inc(v_toPure_171_);
lean_inc(v_fst_186_);
lean_inc(v_snd_187_);
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
lean_inc(v_snd_309_);
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
lean_inc(v_snd_309_);
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
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2(void){
_start:
{
lean_object* v_exs_348_; lean_object* v___x_349_; 
v_exs_348_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1));
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_exs_348_);
lean_ctor_set(v___x_349_, 1, v_exs_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_nss_359_, lean_object* v_idStx_360_){
_start:
{
lean_object* v_toApplicative_361_; lean_object* v_toBind_362_; lean_object* v_toPure_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_toApplicative_361_ = lean_ctor_get(v_inst_350_, 0);
v_toBind_362_ = lean_ctor_get(v_inst_350_, 1);
lean_inc(v_toBind_362_);
v_toPure_363_ = lean_ctor_get(v_toApplicative_361_, 1);
v___f_364_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0));
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2);
lean_inc(v_toPure_363_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_367_, 0, v_toPure_363_);
lean_inc(v_toBind_362_);
lean_inc(v_idStx_360_);
lean_inc_ref(v_inst_356_);
lean_inc(v_inst_354_);
lean_inc_ref(v_inst_353_);
lean_inc_ref(v_inst_350_);
lean_inc(v_toPure_363_);
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
lean_inc(v_toPure_363_);
lean_inc(v_toBind_362_);
lean_inc_ref(v_inst_350_);
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
lean_object* v___x_6636__overap_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_6636__overap_500_ = l_Lean_Elab_addConstInfo___redArg(v___x_489_, v___x_490_, v___x_491_, v___x_492_, v_snd_493_, v_a_494_, v___x_495_);
lean_inc(v___y_496_);
v___x_501_ = lean_apply_1(v___x_6636__overap_500_, v___y_496_);
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
lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_6651__overap_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v___f_515_);
v___x_530_ = lean_box(0);
lean_inc(v_toBind_524_);
lean_inc(v___y_517_);
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
v___x_6651__overap_532_ = l_Lean_Elab_addConstInfo___redArg(v___x_518_, v___x_519_, v___x_520_, v___x_521_, v_fst_526_, v_a_523_, v___x_530_);
lean_inc(v___y_517_);
v___x_533_ = lean_apply_1(v___x_6651__overap_532_, v___y_517_);
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
lean_inc(v_toBind_553_);
lean_inc(v_a_561_);
lean_inc(v_snd_551_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_564_, 0, v_snd_551_);
lean_closure_set(v___f_564_, 1, v_a_561_);
lean_closure_set(v___f_564_, 2, v_inst_552_);
lean_closure_set(v___f_564_, 3, v_toBind_553_);
lean_closure_set(v___f_564_, 4, v___f_554_);
lean_inc(v___y_555_);
lean_inc_ref(v___f_564_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_565_, 0, v___f_564_);
lean_closure_set(v___f_565_, 1, v___y_555_);
lean_inc(v_toBind_553_);
lean_inc(v___y_555_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v___x_582_, lean_object* v_inst_583_, lean_object* v_inst_584_, lean_object* v_toBind_585_, lean_object* v___f_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v___x_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___f_596_, lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_x_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_6692__overap_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
lean_inc(v_fst_603_);
v_snd_604_ = lean_ctor_get(v_a_599_, 1);
lean_inc(v_snd_604_);
lean_dec_ref(v_a_599_);
lean_inc(v_fst_603_);
lean_inc_ref(v___x_589_);
lean_inc_ref(v___x_588_);
lean_inc(v___y_602_);
lean_inc(v_toBind_585_);
lean_inc(v___x_582_);
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
v___x_606_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_582_, v_inst_591_);
v___x_607_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_607_, 0, lean_box(0));
lean_closure_set(v___x_607_, 1, lean_box(0));
lean_closure_set(v___x_607_, 2, lean_box(0));
lean_closure_set(v___x_607_, 3, lean_box(0));
lean_closure_set(v___x_607_, 4, v_inst_592_);
v___x_6692__overap_608_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_588_, v___x_589_, v___x_593_, v___x_594_, v___x_595_, v___f_596_, v___x_606_, v___x_607_, v___x_597_, v_a_598_, v_fst_603_);
lean_inc(v___y_602_);
v___x_609_ = lean_apply_1(v___x_6692__overap_608_, v___y_602_);
v___x_610_ = lean_apply_4(v_toBind_585_, lean_box(0), lean_box(0), v___x_609_, v___f_605_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_611_ = _args[0];
lean_object* v_inst_612_ = _args[1];
lean_object* v_inst_613_ = _args[2];
lean_object* v_toBind_614_ = _args[3];
lean_object* v___f_615_ = _args[4];
lean_object* v___x_616_ = _args[5];
lean_object* v___x_617_ = _args[6];
lean_object* v___x_618_ = _args[7];
lean_object* v___x_619_ = _args[8];
lean_object* v_inst_620_ = _args[9];
lean_object* v_inst_621_ = _args[10];
lean_object* v___x_622_ = _args[11];
lean_object* v___x_623_ = _args[12];
lean_object* v___x_624_ = _args[13];
lean_object* v___f_625_ = _args[14];
lean_object* v___x_626_ = _args[15];
lean_object* v_a_627_ = _args[16];
lean_object* v_a_628_ = _args[17];
lean_object* v_x_629_ = _args[18];
lean_object* v___y_630_ = _args[19];
lean_object* v___y_631_ = _args[20];
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v___x_611_, v_inst_612_, v_inst_613_, v_toBind_614_, v___f_615_, v___x_616_, v___x_617_, v___x_618_, v___x_619_, v_inst_620_, v_inst_621_, v___x_622_, v___x_623_, v___x_624_, v___f_625_, v___x_626_, v_a_627_, v_a_628_, v_x_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_froms_633_, lean_object* v_tos_634_, lean_object* v_toPure_635_, lean_object* v___x_636_, lean_object* v_inst_637_, lean_object* v_inst_638_, lean_object* v_toBind_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v___f_648_, lean_object* v___x_649_, size_t v___x_650_, lean_object* v_ref_651_, lean_object* v___f_652_, lean_object* v_a_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___f_656_; lean_object* v___f_657_; size_t v_sz_658_; lean_object* v___x_6713__overap_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_654_ = l_Array_zip___redArg(v_froms_633_, v_tos_634_);
v___x_655_ = lean_box(0);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_656_, 0, v___x_655_);
lean_closure_set(v___f_656_, 1, v_toPure_635_);
lean_inc_ref(v___x_640_);
lean_inc(v_toBind_639_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 21, 17);
lean_closure_set(v___f_657_, 0, v___x_636_);
lean_closure_set(v___f_657_, 1, v_inst_637_);
lean_closure_set(v___f_657_, 2, v_inst_638_);
lean_closure_set(v___f_657_, 3, v_toBind_639_);
lean_closure_set(v___f_657_, 4, v___f_656_);
lean_closure_set(v___f_657_, 5, v___x_655_);
lean_closure_set(v___f_657_, 6, v___x_640_);
lean_closure_set(v___f_657_, 7, v___x_641_);
lean_closure_set(v___f_657_, 8, v___x_642_);
lean_closure_set(v___f_657_, 9, v_inst_643_);
lean_closure_set(v___f_657_, 10, v_inst_644_);
lean_closure_set(v___f_657_, 11, v___x_645_);
lean_closure_set(v___f_657_, 12, v___x_646_);
lean_closure_set(v___f_657_, 13, v___x_647_);
lean_closure_set(v___f_657_, 14, v___f_648_);
lean_closure_set(v___f_657_, 15, v___x_649_);
lean_closure_set(v___f_657_, 16, v_a_653_);
v_sz_658_ = lean_array_size(v___x_654_);
v___x_6713__overap_659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_640_, v___x_654_, v___f_657_, v_sz_658_, v___x_650_, v___x_655_);
v___x_660_ = lean_apply_1(v___x_6713__overap_659_, v_ref_651_);
v___x_661_ = lean_apply_4(v_toBind_639_, lean_box(0), lean_box(0), v___x_660_, v___f_652_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_froms_662_ = _args[0];
lean_object* v_tos_663_ = _args[1];
lean_object* v_toPure_664_ = _args[2];
lean_object* v___x_665_ = _args[3];
lean_object* v_inst_666_ = _args[4];
lean_object* v_inst_667_ = _args[5];
lean_object* v_toBind_668_ = _args[6];
lean_object* v___x_669_ = _args[7];
lean_object* v___x_670_ = _args[8];
lean_object* v___x_671_ = _args[9];
lean_object* v_inst_672_ = _args[10];
lean_object* v_inst_673_ = _args[11];
lean_object* v___x_674_ = _args[12];
lean_object* v___x_675_ = _args[13];
lean_object* v___x_676_ = _args[14];
lean_object* v___f_677_ = _args[15];
lean_object* v___x_678_ = _args[16];
lean_object* v___x_679_ = _args[17];
lean_object* v_ref_680_ = _args[18];
lean_object* v___f_681_ = _args[19];
lean_object* v_a_682_ = _args[20];
_start:
{
size_t v___x_7592__boxed_683_; lean_object* v_res_684_; 
v___x_7592__boxed_683_ = lean_unbox_usize(v___x_679_);
lean_dec(v___x_679_);
v_res_684_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_662_, v_tos_663_, v_toPure_664_, v___x_665_, v_inst_666_, v_inst_667_, v_toBind_668_, v___x_669_, v___x_670_, v___x_671_, v_inst_672_, v_inst_673_, v___x_674_, v___x_675_, v___x_676_, v___f_677_, v___x_678_, v___x_7592__boxed_683_, v_ref_680_, v___f_681_, v_a_682_);
lean_dec_ref(v_tos_663_);
lean_dec_ref(v_froms_662_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(uint8_t v___x_685_, uint8_t v___x_686_, lean_object* v_x1_687_, lean_object* v_x2_688_){
_start:
{
lean_object* v_fst_689_; uint8_t v___x_690_; 
v_fst_689_ = lean_ctor_get(v_x1_687_, 0);
v___x_690_ = lean_unbox(v_fst_689_);
if (v___x_690_ == 0)
{
lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_x2_688_);
v_snd_691_ = lean_ctor_get(v_x1_687_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x1_687_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_x1_687_, 0);
lean_dec(v_unused_700_);
v___x_693_ = v_x1_687_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_dec(v_x1_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_box(v___x_685_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_691_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v_snd_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_710_; 
v_snd_701_ = lean_ctor_get(v_x1_687_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x1_687_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_x1_687_, 0);
lean_dec(v_unused_711_);
v___x_703_ = v_x1_687_;
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snd_701_);
lean_dec(v_x1_687_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_710_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_705_ = lean_array_push(v_snd_701_, v_x2_688_);
v___x_706_ = lean_box(v___x_686_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_705_);
lean_ctor_set(v___x_703_, 0, v___x_706_);
v___x_708_ = v___x_703_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_705_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v_x1_714_, lean_object* v_x2_715_){
_start:
{
uint8_t v___x_7636__boxed_716_; uint8_t v___x_7637__boxed_717_; lean_object* v_res_718_; 
v___x_7636__boxed_716_ = lean_unbox(v___x_712_);
v___x_7637__boxed_717_ = lean_unbox(v___x_713_);
v_res_718_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v___x_7636__boxed_716_, v___x_7637__boxed_717_, v_x1_714_, v_x2_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object* v_ids_719_, lean_object* v___f_720_, lean_object* v_a_721_, lean_object* v_inst_722_, lean_object* v_ref_723_, lean_object* v_toBind_724_, lean_object* v___f_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; size_t v_sz_728_; size_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_728_ = lean_array_size(v_ids_719_);
v___x_729_ = ((size_t)0ULL);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_727_, v___f_720_, v_sz_728_, v___x_729_, v_ids_719_);
v___x_731_ = lean_array_to_list(v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_a_721_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_722_, v___x_732_, v_ref_723_);
v___x_734_ = lean_apply_4(v_toBind_724_, lean_box(0), lean_box(0), v___x_733_, v___f_725_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object* v_ids_735_, lean_object* v___f_736_, lean_object* v_a_737_, lean_object* v_inst_738_, lean_object* v_ref_739_, lean_object* v_toBind_740_, lean_object* v___f_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(v_ids_735_, v___f_736_, v_a_737_, v_inst_738_, v_ref_739_, v_toBind_740_, v___f_741_, v_a_742_);
lean_dec(v_ref_739_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v___x_744_, lean_object* v_toPure_745_, lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v___y_752_, lean_object* v_toBind_753_, lean_object* v___f_754_, lean_object* v_a_755_){
_start:
{
uint8_t v_enabled_756_; 
v_enabled_756_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*3);
if (v_enabled_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v___f_754_);
lean_dec(v_toBind_753_);
lean_dec(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v___x_749_);
lean_dec_ref(v___x_748_);
lean_dec_ref(v___x_747_);
lean_dec_ref(v___x_746_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_744_);
v___x_758_ = lean_apply_2(v_toPure_745_, lean_box(0), v___x_757_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_6758__overap_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v_toPure_745_);
v___x_759_ = lean_box(0);
v___x_6758__overap_760_ = l_Lean_Elab_addConstInfo___redArg(v___x_746_, v___x_747_, v___x_748_, v___x_749_, v_a_750_, v_a_751_, v___x_759_);
lean_inc(v___y_752_);
v___x_761_ = lean_apply_1(v___x_6758__overap_760_, v___y_752_);
v___x_762_ = lean_apply_4(v_toBind_753_, lean_box(0), lean_box(0), v___x_761_, v___f_754_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v___x_763_, lean_object* v_toPure_764_, lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v___y_771_, lean_object* v_toBind_772_, lean_object* v___f_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v___x_763_, v_toPure_764_, v___x_765_, v___x_766_, v___x_767_, v___x_768_, v_a_769_, v_a_770_, v___y_771_, v_toBind_772_, v___f_773_, v_a_774_);
lean_dec_ref(v_a_774_);
lean_dec(v___y_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object* v___x_776_, lean_object* v_inst_777_, lean_object* v___x_778_, lean_object* v_toPure_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v_a_783_, lean_object* v___y_784_, lean_object* v_toBind_785_, lean_object* v___f_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; lean_object* v_getInfoState_789_; lean_object* v___f_790_; lean_object* v___x_791_; 
lean_inc_ref(v_inst_777_);
v___x_788_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_776_, v_inst_777_);
v_getInfoState_789_ = lean_ctor_get(v_inst_777_, 0);
lean_inc(v_getInfoState_789_);
lean_dec_ref(v_inst_777_);
lean_inc(v_toBind_785_);
lean_inc(v___y_784_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 12, 11);
lean_closure_set(v___f_790_, 0, v___x_778_);
lean_closure_set(v___f_790_, 1, v_toPure_779_);
lean_closure_set(v___f_790_, 2, v___x_780_);
lean_closure_set(v___f_790_, 3, v___x_788_);
lean_closure_set(v___f_790_, 4, v___x_781_);
lean_closure_set(v___f_790_, 5, v___x_782_);
lean_closure_set(v___f_790_, 6, v_a_783_);
lean_closure_set(v___f_790_, 7, v_a_787_);
lean_closure_set(v___f_790_, 8, v___y_784_);
lean_closure_set(v___f_790_, 9, v_toBind_785_);
lean_closure_set(v___f_790_, 10, v___f_786_);
v___x_791_ = lean_apply_4(v_toBind_785_, lean_box(0), lean_box(0), v_getInfoState_789_, v___f_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object* v___x_792_, lean_object* v_inst_793_, lean_object* v___x_794_, lean_object* v_toPure_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v___y_800_, lean_object* v_toBind_801_, lean_object* v___f_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v___x_792_, v_inst_793_, v___x_794_, v_toPure_795_, v___x_796_, v___x_797_, v___x_798_, v_a_799_, v___y_800_, v_toBind_801_, v___f_802_, v_a_803_);
lean_dec(v___y_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v___x_805_, lean_object* v_inst_806_, lean_object* v___x_807_, lean_object* v_toPure_808_, lean_object* v___x_809_, lean_object* v___x_810_, lean_object* v___x_811_, lean_object* v_toBind_812_, lean_object* v___f_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v___x_816_, lean_object* v___x_817_, lean_object* v___x_818_, lean_object* v___f_819_, lean_object* v___x_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_6791__overap_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_inc(v_toBind_812_);
lean_inc(v___y_825_);
lean_inc(v_a_822_);
lean_inc_ref(v___x_810_);
lean_inc_ref(v___x_809_);
lean_inc(v___x_805_);
v___f_826_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed), 12, 11);
lean_closure_set(v___f_826_, 0, v___x_805_);
lean_closure_set(v___f_826_, 1, v_inst_806_);
lean_closure_set(v___f_826_, 2, v___x_807_);
lean_closure_set(v___f_826_, 3, v_toPure_808_);
lean_closure_set(v___f_826_, 4, v___x_809_);
lean_closure_set(v___f_826_, 5, v___x_810_);
lean_closure_set(v___f_826_, 6, v___x_811_);
lean_closure_set(v___f_826_, 7, v_a_822_);
lean_closure_set(v___f_826_, 8, v___y_825_);
lean_closure_set(v___f_826_, 9, v_toBind_812_);
lean_closure_set(v___f_826_, 10, v___f_813_);
v___x_827_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_805_, v_inst_814_);
v___x_828_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_828_, 0, lean_box(0));
lean_closure_set(v___x_828_, 1, lean_box(0));
lean_closure_set(v___x_828_, 2, lean_box(0));
lean_closure_set(v___x_828_, 3, lean_box(0));
lean_closure_set(v___x_828_, 4, v_inst_815_);
v___x_6791__overap_829_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_809_, v___x_810_, v___x_816_, v___x_817_, v___x_818_, v___f_819_, v___x_827_, v___x_828_, v___x_820_, v_a_821_, v_a_822_);
lean_inc(v___y_825_);
v___x_830_ = lean_apply_1(v___x_6791__overap_829_, v___y_825_);
v___x_831_ = lean_apply_4(v_toBind_812_, lean_box(0), lean_box(0), v___x_830_, v___f_826_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object** _args){
lean_object* v___x_832_ = _args[0];
lean_object* v_inst_833_ = _args[1];
lean_object* v___x_834_ = _args[2];
lean_object* v_toPure_835_ = _args[3];
lean_object* v___x_836_ = _args[4];
lean_object* v___x_837_ = _args[5];
lean_object* v___x_838_ = _args[6];
lean_object* v_toBind_839_ = _args[7];
lean_object* v___f_840_ = _args[8];
lean_object* v_inst_841_ = _args[9];
lean_object* v_inst_842_ = _args[10];
lean_object* v___x_843_ = _args[11];
lean_object* v___x_844_ = _args[12];
lean_object* v___x_845_ = _args[13];
lean_object* v___f_846_ = _args[14];
lean_object* v___x_847_ = _args[15];
lean_object* v_a_848_ = _args[16];
lean_object* v_a_849_ = _args[17];
lean_object* v_x_850_ = _args[18];
lean_object* v___y_851_ = _args[19];
lean_object* v___y_852_ = _args[20];
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v___x_832_, v_inst_833_, v___x_834_, v_toPure_835_, v___x_836_, v___x_837_, v___x_838_, v_toBind_839_, v___f_840_, v_inst_841_, v_inst_842_, v___x_843_, v___x_844_, v___x_845_, v___f_846_, v___x_847_, v_a_848_, v_a_849_, v_x_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v_toPure_854_, lean_object* v___x_855_, lean_object* v_inst_856_, lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v_toBind_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v___f_866_, lean_object* v___x_867_, lean_object* v_a_868_, lean_object* v_ids_869_, lean_object* v_ref_870_, lean_object* v___f_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___f_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_6810__overap_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_873_ = lean_box(0);
lean_inc(v_toPure_854_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_874_, 0, v___x_873_);
lean_closure_set(v___f_874_, 1, v_toPure_854_);
lean_inc(v_toBind_860_);
lean_inc_ref(v___x_857_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 21, 17);
lean_closure_set(v___f_875_, 0, v___x_855_);
lean_closure_set(v___f_875_, 1, v_inst_856_);
lean_closure_set(v___f_875_, 2, v___x_873_);
lean_closure_set(v___f_875_, 3, v_toPure_854_);
lean_closure_set(v___f_875_, 4, v___x_857_);
lean_closure_set(v___f_875_, 5, v___x_858_);
lean_closure_set(v___f_875_, 6, v___x_859_);
lean_closure_set(v___f_875_, 7, v_toBind_860_);
lean_closure_set(v___f_875_, 8, v___f_874_);
lean_closure_set(v___f_875_, 9, v_inst_861_);
lean_closure_set(v___f_875_, 10, v_inst_862_);
lean_closure_set(v___f_875_, 11, v___x_863_);
lean_closure_set(v___f_875_, 12, v___x_864_);
lean_closure_set(v___f_875_, 13, v___x_865_);
lean_closure_set(v___f_875_, 14, v___f_866_);
lean_closure_set(v___f_875_, 15, v___x_867_);
lean_closure_set(v___f_875_, 16, v_a_868_);
v_sz_876_ = lean_array_size(v_ids_869_);
v___x_877_ = ((size_t)0ULL);
v___x_6810__overap_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_857_, v_ids_869_, v___f_875_, v_sz_876_, v___x_877_, v___x_873_);
v___x_879_ = lean_apply_1(v___x_6810__overap_878_, v_ref_870_);
v___x_880_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_879_, v___f_871_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_toPure_881_ = _args[0];
lean_object* v___x_882_ = _args[1];
lean_object* v_inst_883_ = _args[2];
lean_object* v___x_884_ = _args[3];
lean_object* v___x_885_ = _args[4];
lean_object* v___x_886_ = _args[5];
lean_object* v_toBind_887_ = _args[6];
lean_object* v_inst_888_ = _args[7];
lean_object* v_inst_889_ = _args[8];
lean_object* v___x_890_ = _args[9];
lean_object* v___x_891_ = _args[10];
lean_object* v___x_892_ = _args[11];
lean_object* v___f_893_ = _args[12];
lean_object* v___x_894_ = _args[13];
lean_object* v_a_895_ = _args[14];
lean_object* v_ids_896_ = _args[15];
lean_object* v_ref_897_ = _args[16];
lean_object* v___f_898_ = _args[17];
lean_object* v_a_899_ = _args[18];
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v_toPure_881_, v___x_882_, v_inst_883_, v___x_884_, v___x_885_, v___x_886_, v_toBind_887_, v_inst_888_, v_inst_889_, v___x_890_, v___x_891_, v___x_892_, v___f_893_, v___x_894_, v_a_895_, v_ids_896_, v_ref_897_, v___f_898_, v_a_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_ids_901_, lean_object* v___f_902_, lean_object* v_inst_903_, lean_object* v_ref_904_, lean_object* v_toBind_905_, lean_object* v___f_906_, lean_object* v_toPure_907_, lean_object* v___x_908_, lean_object* v_inst_909_, lean_object* v___x_910_, lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v___f_918_, lean_object* v___x_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___f_921_; lean_object* v___f_922_; lean_object* v___f_923_; lean_object* v___x_6830__overap_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_inc(v_toBind_905_);
lean_inc(v_ref_904_);
lean_inc(v_inst_903_);
lean_inc(v_a_920_);
lean_inc_ref(v_ids_901_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed), 8, 7);
lean_closure_set(v___f_921_, 0, v_ids_901_);
lean_closure_set(v___f_921_, 1, v___f_902_);
lean_closure_set(v___f_921_, 2, v_a_920_);
lean_closure_set(v___f_921_, 3, v_inst_903_);
lean_closure_set(v___f_921_, 4, v_ref_904_);
lean_closure_set(v___f_921_, 5, v_toBind_905_);
lean_closure_set(v___f_921_, 6, v___f_906_);
lean_inc(v_ref_904_);
lean_inc(v_a_920_);
lean_inc(v_toBind_905_);
lean_inc_ref(v___x_911_);
lean_inc_ref(v___x_910_);
lean_inc(v___x_908_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 19, 18);
lean_closure_set(v___f_922_, 0, v_toPure_907_);
lean_closure_set(v___f_922_, 1, v___x_908_);
lean_closure_set(v___f_922_, 2, v_inst_909_);
lean_closure_set(v___f_922_, 3, v___x_910_);
lean_closure_set(v___f_922_, 4, v___x_911_);
lean_closure_set(v___f_922_, 5, v___x_912_);
lean_closure_set(v___f_922_, 6, v_toBind_905_);
lean_closure_set(v___f_922_, 7, v_inst_913_);
lean_closure_set(v___f_922_, 8, v_inst_914_);
lean_closure_set(v___f_922_, 9, v___x_915_);
lean_closure_set(v___f_922_, 10, v___x_916_);
lean_closure_set(v___f_922_, 11, v___x_917_);
lean_closure_set(v___f_922_, 12, v___f_918_);
lean_closure_set(v___f_922_, 13, v___x_919_);
lean_closure_set(v___f_922_, 14, v_a_920_);
lean_closure_set(v___f_922_, 15, v_ids_901_);
lean_closure_set(v___f_922_, 16, v_ref_904_);
lean_closure_set(v___f_922_, 17, v___f_921_);
v___f_923_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_923_, 0, v_inst_903_);
lean_closure_set(v___f_923_, 1, v___x_908_);
v___x_6830__overap_924_ = l_Lean_activateScoped___redArg(v___x_910_, v___x_911_, v___f_923_, v_a_920_);
v___x_925_ = lean_apply_1(v___x_6830__overap_924_, v_ref_904_);
v___x_926_ = lean_apply_4(v_toBind_905_, lean_box(0), lean_box(0), v___x_925_, v___f_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_ids_927_ = _args[0];
lean_object* v___f_928_ = _args[1];
lean_object* v_inst_929_ = _args[2];
lean_object* v_ref_930_ = _args[3];
lean_object* v_toBind_931_ = _args[4];
lean_object* v___f_932_ = _args[5];
lean_object* v_toPure_933_ = _args[6];
lean_object* v___x_934_ = _args[7];
lean_object* v_inst_935_ = _args[8];
lean_object* v___x_936_ = _args[9];
lean_object* v___x_937_ = _args[10];
lean_object* v___x_938_ = _args[11];
lean_object* v_inst_939_ = _args[12];
lean_object* v_inst_940_ = _args[13];
lean_object* v___x_941_ = _args[14];
lean_object* v___x_942_ = _args[15];
lean_object* v___x_943_ = _args[16];
lean_object* v___f_944_ = _args[17];
lean_object* v___x_945_ = _args[18];
lean_object* v_a_946_ = _args[19];
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_ids_927_, v___f_928_, v_inst_929_, v_ref_930_, v_toBind_931_, v___f_932_, v_toPure_933_, v___x_934_, v_inst_935_, v___x_936_, v___x_937_, v___x_938_, v_inst_939_, v_inst_940_, v___x_941_, v___x_942_, v___x_943_, v___f_944_, v___x_945_, v_a_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_inst_950_, lean_object* v_toBind_951_, lean_object* v___f_952_, lean_object* v_____r_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = l_Lean_TSyntax_getId(v_a_948_);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v_a_949_);
v___x_957_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_950_, v___x_956_, v___y_954_);
v___x_958_ = lean_apply_4(v_toBind_951_, lean_box(0), lean_box(0), v___x_957_, v___f_952_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_inst_961_, lean_object* v_toBind_962_, lean_object* v___f_963_, lean_object* v_____r_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v_a_959_, v_a_960_, v_inst_961_, v_toBind_962_, v___f_963_, v_____r_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec(v_a_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v___f_967_, lean_object* v___x_968_, lean_object* v___y_969_, lean_object* v___x_970_, lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_toBind_976_, lean_object* v___f_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_enabled_979_; 
v_enabled_979_ = lean_ctor_get_uint8(v_a_978_, sizeof(void*)*3);
if (v_enabled_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec(v___f_977_);
lean_dec(v_toBind_976_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v___x_973_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_970_);
lean_inc(v___y_969_);
v___x_980_ = lean_apply_2(v___f_967_, v___x_968_, v___y_969_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_6859__overap_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v___f_967_);
v___x_981_ = lean_box(0);
v___x_6859__overap_982_ = l_Lean_Elab_addConstInfo___redArg(v___x_970_, v___x_971_, v___x_972_, v___x_973_, v_a_974_, v_a_975_, v___x_981_);
lean_inc(v___y_969_);
v___x_983_ = lean_apply_1(v___x_6859__overap_982_, v___y_969_);
v___x_984_ = lean_apply_4(v_toBind_976_, lean_box(0), lean_box(0), v___x_983_, v___f_977_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object* v___f_985_, lean_object* v___x_986_, lean_object* v___y_987_, lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_toBind_994_, lean_object* v___f_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v___f_985_, v___x_986_, v___y_987_, v___x_988_, v___x_989_, v___x_990_, v___x_991_, v_a_992_, v_a_993_, v_toBind_994_, v___f_995_, v_a_996_);
lean_dec_ref(v_a_996_);
lean_dec(v___y_987_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v___x_998_, lean_object* v_inst_999_, lean_object* v_a_1000_, lean_object* v_inst_1001_, lean_object* v_toBind_1002_, lean_object* v___f_1003_, lean_object* v___y_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v_getInfoState_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
lean_inc_ref(v_inst_999_);
v___x_1010_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_998_, v_inst_999_);
v_getInfoState_1011_ = lean_ctor_get(v_inst_999_, 0);
lean_inc(v_getInfoState_1011_);
lean_dec_ref(v_inst_999_);
lean_inc(v_toBind_1002_);
lean_inc(v_a_1009_);
lean_inc(v_a_1000_);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 7, 5);
lean_closure_set(v___f_1012_, 0, v_a_1000_);
lean_closure_set(v___f_1012_, 1, v_a_1009_);
lean_closure_set(v___f_1012_, 2, v_inst_1001_);
lean_closure_set(v___f_1012_, 3, v_toBind_1002_);
lean_closure_set(v___f_1012_, 4, v___f_1003_);
lean_inc(v___y_1004_);
lean_inc_ref(v___f_1012_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 3, 2);
lean_closure_set(v___f_1013_, 0, v___f_1012_);
lean_closure_set(v___f_1013_, 1, v___y_1004_);
lean_inc(v_toBind_1002_);
lean_inc(v___y_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed), 12, 11);
lean_closure_set(v___f_1014_, 0, v___f_1012_);
lean_closure_set(v___f_1014_, 1, v___x_1005_);
lean_closure_set(v___f_1014_, 2, v___y_1004_);
lean_closure_set(v___f_1014_, 3, v___x_1006_);
lean_closure_set(v___f_1014_, 4, v___x_1010_);
lean_closure_set(v___f_1014_, 5, v___x_1007_);
lean_closure_set(v___f_1014_, 6, v___x_1008_);
lean_closure_set(v___f_1014_, 7, v_a_1000_);
lean_closure_set(v___f_1014_, 8, v_a_1009_);
lean_closure_set(v___f_1014_, 9, v_toBind_1002_);
lean_closure_set(v___f_1014_, 10, v___f_1013_);
v___x_1015_ = lean_apply_4(v_toBind_1002_, lean_box(0), lean_box(0), v_getInfoState_1011_, v___f_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(lean_object* v___x_1016_, lean_object* v_inst_1017_, lean_object* v_a_1018_, lean_object* v_inst_1019_, lean_object* v_toBind_1020_, lean_object* v___f_1021_, lean_object* v___y_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v___x_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(v___x_1016_, v_inst_1017_, v_a_1018_, v_inst_1019_, v_toBind_1020_, v___f_1021_, v___y_1022_, v___x_1023_, v___x_1024_, v___x_1025_, v___x_1026_, v_a_1027_);
lean_dec(v___y_1022_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v___x_1029_, lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_toBind_1032_, lean_object* v___f_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v___f_1043_, lean_object* v___x_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_6896__overap_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_inc_ref(v___x_1036_);
lean_inc_ref(v___x_1035_);
lean_inc(v___y_1049_);
lean_inc(v_toBind_1032_);
lean_inc(v_a_1046_);
lean_inc(v___x_1029_);
v___f_1050_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed), 12, 11);
lean_closure_set(v___f_1050_, 0, v___x_1029_);
lean_closure_set(v___f_1050_, 1, v_inst_1030_);
lean_closure_set(v___f_1050_, 2, v_a_1046_);
lean_closure_set(v___f_1050_, 3, v_inst_1031_);
lean_closure_set(v___f_1050_, 4, v_toBind_1032_);
lean_closure_set(v___f_1050_, 5, v___f_1033_);
lean_closure_set(v___f_1050_, 6, v___y_1049_);
lean_closure_set(v___f_1050_, 7, v___x_1034_);
lean_closure_set(v___f_1050_, 8, v___x_1035_);
lean_closure_set(v___f_1050_, 9, v___x_1036_);
lean_closure_set(v___f_1050_, 10, v___x_1037_);
v___x_1051_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1029_, v_inst_1038_);
v___x_1052_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1052_, 0, lean_box(0));
lean_closure_set(v___x_1052_, 1, lean_box(0));
lean_closure_set(v___x_1052_, 2, lean_box(0));
lean_closure_set(v___x_1052_, 3, lean_box(0));
lean_closure_set(v___x_1052_, 4, v_inst_1039_);
v___x_6896__overap_1053_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1035_, v___x_1036_, v___x_1040_, v___x_1041_, v___x_1042_, v___f_1043_, v___x_1051_, v___x_1052_, v___x_1044_, v_a_1045_, v_a_1046_);
lean_inc(v___y_1049_);
v___x_1054_ = lean_apply_1(v___x_6896__overap_1053_, v___y_1049_);
v___x_1055_ = lean_apply_4(v_toBind_1032_, lean_box(0), lean_box(0), v___x_1054_, v___f_1050_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object** _args){
lean_object* v___x_1056_ = _args[0];
lean_object* v_inst_1057_ = _args[1];
lean_object* v_inst_1058_ = _args[2];
lean_object* v_toBind_1059_ = _args[3];
lean_object* v___f_1060_ = _args[4];
lean_object* v___x_1061_ = _args[5];
lean_object* v___x_1062_ = _args[6];
lean_object* v___x_1063_ = _args[7];
lean_object* v___x_1064_ = _args[8];
lean_object* v_inst_1065_ = _args[9];
lean_object* v_inst_1066_ = _args[10];
lean_object* v___x_1067_ = _args[11];
lean_object* v___x_1068_ = _args[12];
lean_object* v___x_1069_ = _args[13];
lean_object* v___f_1070_ = _args[14];
lean_object* v___x_1071_ = _args[15];
lean_object* v_a_1072_ = _args[16];
lean_object* v_a_1073_ = _args[17];
lean_object* v_x_1074_ = _args[18];
lean_object* v___y_1075_ = _args[19];
lean_object* v___y_1076_ = _args[20];
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v___x_1056_, v_inst_1057_, v_inst_1058_, v_toBind_1059_, v___f_1060_, v___x_1061_, v___x_1062_, v___x_1063_, v___x_1064_, v_inst_1065_, v_inst_1066_, v___x_1067_, v___x_1068_, v___x_1069_, v___f_1070_, v___x_1071_, v_a_1072_, v_a_1073_, v_x_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_toPure_1078_, lean_object* v___x_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_toBind_1082_, lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v___x_1088_, lean_object* v___x_1089_, lean_object* v___x_1090_, lean_object* v___f_1091_, lean_object* v___x_1092_, lean_object* v_ids_1093_, lean_object* v_ref_1094_, lean_object* v___f_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_6916__overap_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1097_ = lean_box(0);
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1098_, 0, v___x_1097_);
lean_closure_set(v___f_1098_, 1, v_toPure_1078_);
lean_inc_ref(v___x_1083_);
lean_inc(v_toBind_1082_);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 21, 17);
lean_closure_set(v___f_1099_, 0, v___x_1079_);
lean_closure_set(v___f_1099_, 1, v_inst_1080_);
lean_closure_set(v___f_1099_, 2, v_inst_1081_);
lean_closure_set(v___f_1099_, 3, v_toBind_1082_);
lean_closure_set(v___f_1099_, 4, v___f_1098_);
lean_closure_set(v___f_1099_, 5, v___x_1097_);
lean_closure_set(v___f_1099_, 6, v___x_1083_);
lean_closure_set(v___f_1099_, 7, v___x_1084_);
lean_closure_set(v___f_1099_, 8, v___x_1085_);
lean_closure_set(v___f_1099_, 9, v_inst_1086_);
lean_closure_set(v___f_1099_, 10, v_inst_1087_);
lean_closure_set(v___f_1099_, 11, v___x_1088_);
lean_closure_set(v___f_1099_, 12, v___x_1089_);
lean_closure_set(v___f_1099_, 13, v___x_1090_);
lean_closure_set(v___f_1099_, 14, v___f_1091_);
lean_closure_set(v___f_1099_, 15, v___x_1092_);
lean_closure_set(v___f_1099_, 16, v_a_1096_);
v_sz_1100_ = lean_array_size(v_ids_1093_);
v___x_1101_ = ((size_t)0ULL);
v___x_6916__overap_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1083_, v_ids_1093_, v___f_1099_, v_sz_1100_, v___x_1101_, v___x_1097_);
v___x_1103_ = lean_apply_1(v___x_6916__overap_1102_, v_ref_1094_);
v___x_1104_ = lean_apply_4(v_toBind_1082_, lean_box(0), lean_box(0), v___x_1103_, v___f_1095_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object** _args){
lean_object* v_toPure_1105_ = _args[0];
lean_object* v___x_1106_ = _args[1];
lean_object* v_inst_1107_ = _args[2];
lean_object* v_inst_1108_ = _args[3];
lean_object* v_toBind_1109_ = _args[4];
lean_object* v___x_1110_ = _args[5];
lean_object* v___x_1111_ = _args[6];
lean_object* v___x_1112_ = _args[7];
lean_object* v_inst_1113_ = _args[8];
lean_object* v_inst_1114_ = _args[9];
lean_object* v___x_1115_ = _args[10];
lean_object* v___x_1116_ = _args[11];
lean_object* v___x_1117_ = _args[12];
lean_object* v___f_1118_ = _args[13];
lean_object* v___x_1119_ = _args[14];
lean_object* v_ids_1120_ = _args[15];
lean_object* v_ref_1121_ = _args[16];
lean_object* v___f_1122_ = _args[17];
lean_object* v_a_1123_ = _args[18];
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_toPure_1105_, v___x_1106_, v_inst_1107_, v_inst_1108_, v_toBind_1109_, v___x_1110_, v___x_1111_, v___x_1112_, v_inst_1113_, v_inst_1114_, v___x_1115_, v___x_1116_, v___x_1117_, v___f_1118_, v___x_1119_, v_ids_1120_, v_ref_1121_, v___f_1122_, v_a_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v_inst_1125_, lean_object* v___x_1126_, lean_object* v___x_1127_, lean_object* v___x_1128_, lean_object* v_toBind_1129_, lean_object* v___f_1130_, lean_object* v_a_1131_, lean_object* v_x_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___f_1135_; lean_object* v___x_6936__overap_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___f_1135_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1135_, 0, v_inst_1125_);
lean_closure_set(v___f_1135_, 1, v___x_1126_);
v___x_6936__overap_1136_ = l_Lean_activateScoped___redArg(v___x_1127_, v___x_1128_, v___f_1135_, v_a_1131_);
lean_inc(v___y_1134_);
v___x_1137_ = lean_apply_1(v___x_6936__overap_1136_, v___y_1134_);
v___x_1138_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v___x_1137_, v___f_1130_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object* v_inst_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v___x_1142_, lean_object* v_toBind_1143_, lean_object* v___f_1144_, lean_object* v_a_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(v_inst_1139_, v___x_1140_, v___x_1141_, v___x_1142_, v_toBind_1143_, v___f_1144_, v_a_1145_, v_x_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v___x_1150_, lean_object* v___f_1151_, lean_object* v___x_1152_, lean_object* v___y_1153_, lean_object* v_toBind_1154_, lean_object* v___f_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_6943__overap_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_6943__overap_1157_ = l_List_forIn_x27_loop___redArg(v___x_1150_, v___f_1151_, v_a_1156_, v___x_1152_);
lean_inc(v___y_1153_);
v___x_1158_ = lean_apply_1(v___x_6943__overap_1157_, v___y_1153_);
v___x_1159_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1158_, v___f_1155_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object* v___x_1160_, lean_object* v___f_1161_, lean_object* v___x_1162_, lean_object* v___y_1163_, lean_object* v_toBind_1164_, lean_object* v___f_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v___x_1160_, v___f_1161_, v___x_1162_, v___y_1163_, v_toBind_1164_, v___f_1165_, v_a_1166_);
lean_dec(v___y_1163_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v___x_1173_, lean_object* v_toBind_1174_, lean_object* v___f_1175_, lean_object* v___x_1176_, lean_object* v___f_1177_, lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_a_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v_getEnv_1186_; lean_object* v_modifyEnv_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1210_; 
lean_inc(v_inst_1171_);
v___x_1185_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1170_, v_inst_1171_);
v_getEnv_1186_ = lean_ctor_get(v_inst_1172_, 0);
v_modifyEnv_1187_ = lean_ctor_get(v_inst_1172_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_inst_1172_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1189_ = v_inst_1172_;
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_modifyEnv_1187_);
lean_inc(v_getEnv_1186_);
lean_dec(v_inst_1172_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1191_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1192_, 0, v_modifyEnv_1187_);
lean_closure_set(v___f_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1193_, 0, lean_box(0));
lean_closure_set(v___x_1193_, 1, lean_box(0));
lean_closure_set(v___x_1193_, 2, lean_box(0));
lean_closure_set(v___x_1193_, 3, lean_box(0));
lean_closure_set(v___x_1193_, 4, v_getEnv_1186_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___f_1192_);
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___f_1192_);
v___x_1195_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_6973__overap_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_inc(v_toBind_1174_);
lean_inc_ref(v___x_1195_);
lean_inc_ref(v___x_1173_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed), 10, 6);
lean_closure_set(v___f_1196_, 0, v_inst_1171_);
lean_closure_set(v___f_1196_, 1, v___x_1191_);
lean_closure_set(v___f_1196_, 2, v___x_1173_);
lean_closure_set(v___f_1196_, 3, v___x_1195_);
lean_closure_set(v___f_1196_, 4, v_toBind_1174_);
lean_closure_set(v___f_1196_, 5, v___f_1175_);
lean_inc(v_toBind_1174_);
lean_inc(v___y_1184_);
lean_inc_ref(v___x_1173_);
v___f_1197_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 7, 6);
lean_closure_set(v___f_1197_, 0, v___x_1173_);
lean_closure_set(v___f_1197_, 1, v___f_1196_);
lean_closure_set(v___f_1197_, 2, v___x_1176_);
lean_closure_set(v___f_1197_, 3, v___y_1184_);
lean_closure_set(v___f_1197_, 4, v_toBind_1174_);
lean_closure_set(v___f_1197_, 5, v___f_1177_);
lean_inc_ref(v_inst_1178_);
v___f_1198_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1198_, 0, v_inst_1178_);
v___f_1199_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1199_, 0, v_inst_1178_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___f_1198_);
lean_ctor_set(v___x_1200_, 1, v___f_1199_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1202_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1191_, v___x_1201_, v_inst_1179_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v_inst_1180_);
lean_closure_set(v___f_1203_, 1, v___x_1191_);
lean_inc_ref(v___x_1173_);
v___x_1204_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1203_, v___x_1173_);
v___x_1205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1200_);
lean_ctor_set(v___x_1205_, 1, v___x_1202_);
lean_ctor_set(v___x_1205_, 2, v___x_1204_);
v___x_6973__overap_1206_ = l_Lean_resolveNamespace___redArg(v___x_1173_, v___x_1185_, v___x_1195_, v___x_1205_, v_a_1181_);
lean_inc(v___y_1184_);
v___x_1207_ = lean_apply_1(v___x_6973__overap_1206_, v___y_1184_);
v___x_1208_ = lean_apply_4(v_toBind_1174_, lean_box(0), lean_box(0), v___x_1207_, v___f_1197_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v___x_1214_, lean_object* v_toBind_1215_, lean_object* v___f_1216_, lean_object* v___x_1217_, lean_object* v___f_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_a_1222_, lean_object* v_x_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v_inst_1211_, v_inst_1212_, v_inst_1213_, v___x_1214_, v_toBind_1215_, v___f_1216_, v___x_1217_, v___f_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_a_1222_, v_x_1223_, v___y_1224_, v___y_1225_);
lean_dec(v___y_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v_inst_1227_, lean_object* v___x_1228_, lean_object* v___x_1229_, lean_object* v___x_1230_, lean_object* v_a_1231_, lean_object* v___y_1232_, lean_object* v_toBind_1233_, lean_object* v___f_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v___f_1236_; lean_object* v___x_6991__overap_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___f_1236_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1236_, 0, v_inst_1227_);
lean_closure_set(v___f_1236_, 1, v___x_1228_);
v___x_6991__overap_1237_ = l_Lean_activateScoped___redArg(v___x_1229_, v___x_1230_, v___f_1236_, v_a_1231_);
lean_inc(v___y_1232_);
v___x_1238_ = lean_apply_1(v___x_6991__overap_1237_, v___y_1232_);
v___x_1239_ = lean_apply_4(v_toBind_1233_, lean_box(0), lean_box(0), v___x_1238_, v___f_1234_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object* v_inst_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, lean_object* v_a_1244_, lean_object* v___y_1245_, lean_object* v_toBind_1246_, lean_object* v___f_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(v_inst_1240_, v___x_1241_, v___x_1242_, v___x_1243_, v_a_1244_, v___y_1245_, v_toBind_1246_, v___f_1247_, v_a_1248_);
lean_dec(v___y_1245_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_inst_1250_, lean_object* v___x_1251_, lean_object* v___x_1252_, lean_object* v___x_1253_, lean_object* v_toBind_1254_, lean_object* v___f_1255_, lean_object* v___x_1256_, lean_object* v_a_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_inc(v_toBind_1254_);
lean_inc(v___y_1260_);
lean_inc(v_a_1257_);
lean_inc(v_inst_1250_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 9, 8);
lean_closure_set(v___f_1261_, 0, v_inst_1250_);
lean_closure_set(v___f_1261_, 1, v___x_1251_);
lean_closure_set(v___f_1261_, 2, v___x_1252_);
lean_closure_set(v___f_1261_, 3, v___x_1253_);
lean_closure_set(v___f_1261_, 4, v_a_1257_);
lean_closure_set(v___f_1261_, 5, v___y_1260_);
lean_closure_set(v___f_1261_, 6, v_toBind_1254_);
lean_closure_set(v___f_1261_, 7, v___f_1255_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1257_);
lean_ctor_set(v___x_1262_, 1, v___x_1256_);
v___x_1263_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1250_, v___x_1262_, v___y_1260_);
v___x_1264_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v___x_1263_, v___f_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object* v_inst_1265_, lean_object* v___x_1266_, lean_object* v___x_1267_, lean_object* v___x_1268_, lean_object* v_toBind_1269_, lean_object* v___f_1270_, lean_object* v___x_1271_, lean_object* v_a_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_inst_1265_, v___x_1266_, v___x_1267_, v___x_1268_, v_toBind_1269_, v___f_1270_, v___x_1271_, v_a_1272_, v_x_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v___x_1280_, lean_object* v_toBind_1281_, lean_object* v___f_1282_, lean_object* v___x_1283_, lean_object* v___x_1284_, lean_object* v___f_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_a_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v_getEnv_1294_; lean_object* v_modifyEnv_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1318_; 
lean_inc(v_inst_1278_);
v___x_1293_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1277_, v_inst_1278_);
v_getEnv_1294_ = lean_ctor_get(v_inst_1279_, 0);
v_modifyEnv_1295_ = lean_ctor_get(v_inst_1279_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_inst_1279_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1297_ = v_inst_1279_;
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_modifyEnv_1295_);
lean_inc(v_getEnv_1294_);
lean_dec(v_inst_1279_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1318_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1299_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1300_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1300_, 0, v_modifyEnv_1295_);
lean_closure_set(v___f_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1301_, 0, lean_box(0));
lean_closure_set(v___x_1301_, 1, lean_box(0));
lean_closure_set(v___x_1301_, 2, lean_box(0));
lean_closure_set(v___x_1301_, 3, lean_box(0));
lean_closure_set(v___x_1301_, 4, v_getEnv_1294_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v___f_1300_);
lean_ctor_set(v___x_1297_, 0, v___x_1301_);
v___x_1303_ = v___x_1297_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v___f_1300_);
v___x_1303_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_7042__overap_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_inc(v_toBind_1281_);
lean_inc_ref(v___x_1303_);
lean_inc_ref(v___x_1280_);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed), 11, 7);
lean_closure_set(v___f_1304_, 0, v_inst_1278_);
lean_closure_set(v___f_1304_, 1, v___x_1299_);
lean_closure_set(v___f_1304_, 2, v___x_1280_);
lean_closure_set(v___f_1304_, 3, v___x_1303_);
lean_closure_set(v___f_1304_, 4, v_toBind_1281_);
lean_closure_set(v___f_1304_, 5, v___f_1282_);
lean_closure_set(v___f_1304_, 6, v___x_1283_);
lean_inc(v_toBind_1281_);
lean_inc(v___y_1292_);
lean_inc_ref(v___x_1280_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 7, 6);
lean_closure_set(v___f_1305_, 0, v___x_1280_);
lean_closure_set(v___f_1305_, 1, v___f_1304_);
lean_closure_set(v___f_1305_, 2, v___x_1284_);
lean_closure_set(v___f_1305_, 3, v___y_1292_);
lean_closure_set(v___f_1305_, 4, v_toBind_1281_);
lean_closure_set(v___f_1305_, 5, v___f_1285_);
lean_inc_ref(v_inst_1286_);
v___f_1306_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1306_, 0, v_inst_1286_);
v___f_1307_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1307_, 0, v_inst_1286_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___f_1306_);
lean_ctor_set(v___x_1308_, 1, v___f_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1310_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1299_, v___x_1309_, v_inst_1287_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1311_, 0, v_inst_1288_);
lean_closure_set(v___f_1311_, 1, v___x_1299_);
lean_inc_ref(v___x_1280_);
v___x_1312_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1311_, v___x_1280_);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1308_);
lean_ctor_set(v___x_1313_, 1, v___x_1310_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
v___x_7042__overap_1314_ = l_Lean_resolveNamespace___redArg(v___x_1280_, v___x_1293_, v___x_1303_, v___x_1313_, v_a_1289_);
lean_inc(v___y_1292_);
v___x_1315_ = lean_apply_1(v___x_7042__overap_1314_, v___y_1292_);
v___x_1316_ = lean_apply_4(v_toBind_1281_, lean_box(0), lean_box(0), v___x_1315_, v___f_1305_);
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v___x_1322_, lean_object* v_toBind_1323_, lean_object* v___f_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v___f_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_a_1331_, lean_object* v_x_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(v_inst_1319_, v_inst_1320_, v_inst_1321_, v___x_1322_, v_toBind_1323_, v___f_1324_, v___x_1325_, v___x_1326_, v___f_1327_, v_inst_1328_, v_inst_1329_, v_inst_1330_, v_a_1331_, v_x_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v_toPure_1363_, lean_object* v_inst_1364_, lean_object* v_toBind_1365_, uint8_t v___x_1366_, lean_object* v___x_1367_, lean_object* v___x_1368_, lean_object* v___x_1369_, lean_object* v_stx_1370_, lean_object* v___f_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v___f_1375_, lean_object* v___f_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v___x_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v___f_1383_, lean_object* v_ref_1384_){
_start:
{
lean_object* v___f_1385_; 
lean_inc(v_toBind_1365_);
lean_inc(v_inst_1364_);
lean_inc(v_ref_1384_);
lean_inc(v_toPure_1363_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1385_, 0, v_toPure_1363_);
lean_closure_set(v___f_1385_, 1, v_ref_1384_);
lean_closure_set(v___f_1385_, 2, v_inst_1364_);
lean_closure_set(v___f_1385_, 3, v_toBind_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0));
lean_inc_ref(v___x_1369_);
lean_inc_ref(v___x_1368_);
lean_inc_ref(v___x_1367_);
v___x_1387_ = l_Lean_Name_mkStr4(v___x_1367_, v___x_1368_, v___x_1369_, v___x_1386_);
lean_inc(v_stx_1370_);
v___x_1388_ = l_Lean_Syntax_isOfKind(v_stx_1370_, v___x_1387_);
lean_dec(v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1));
lean_inc_ref(v___x_1369_);
lean_inc_ref(v___x_1368_);
lean_inc_ref(v___x_1367_);
v___x_1390_ = l_Lean_Name_mkStr4(v___x_1367_, v___x_1368_, v___x_1369_, v___x_1389_);
lean_inc(v_stx_1370_);
v___x_1391_ = l_Lean_Syntax_isOfKind(v_stx_1370_, v___x_1390_);
lean_dec(v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2));
lean_inc_ref(v___x_1369_);
lean_inc_ref(v___x_1368_);
lean_inc_ref(v___x_1367_);
v___x_1393_ = l_Lean_Name_mkStr4(v___x_1367_, v___x_1368_, v___x_1369_, v___x_1392_);
lean_inc(v_stx_1370_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v_stx_1370_, v___x_1393_);
lean_dec(v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
lean_dec_ref(v___f_1383_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3));
lean_inc_ref(v___x_1369_);
lean_inc_ref(v___x_1368_);
lean_inc_ref(v___x_1367_);
v___x_1396_ = l_Lean_Name_mkStr4(v___x_1367_, v___x_1368_, v___x_1369_, v___x_1395_);
lean_inc(v_stx_1370_);
v___x_1397_ = l_Lean_Syntax_isOfKind(v_stx_1370_, v___x_1396_);
lean_dec(v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___f_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_7079__overap_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_dec_ref(v___x_1379_);
lean_dec(v_inst_1378_);
lean_dec_ref(v_inst_1377_);
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v_inst_1374_);
lean_dec_ref(v_inst_1373_);
lean_dec(v_stx_1370_);
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1367_);
lean_dec(v_inst_1364_);
lean_dec(v_toPure_1363_);
lean_inc(v_ref_1384_);
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1398_, 0, v___f_1371_);
lean_closure_set(v___f_1398_, 1, v_ref_1384_);
lean_inc_ref(v_inst_1372_);
v___f_1399_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1399_, 0, v_inst_1372_);
v___f_1400_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1400_, 0, v_inst_1372_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___f_1399_);
lean_ctor_set(v___x_1401_, 1, v___f_1400_);
v___x_7079__overap_1402_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1401_);
v___x_1403_ = lean_apply_1(v___x_7079__overap_1402_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1404_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1403_, v___f_1398_);
v___x_1405_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1404_, v___f_1385_);
return v___x_1405_;
}
else
{
lean_object* v___f_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v_ns_1409_; lean_object* v___x_1410_; lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___y_1415_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
lean_inc(v_ref_1384_);
lean_inc(v___f_1371_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1406_, 0, v___f_1371_);
lean_closure_set(v___f_1406_, 1, v_ref_1384_);
lean_inc(v_ref_1384_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1407_, 0, v___f_1371_);
lean_closure_set(v___f_1407_, 1, v_ref_1384_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v_ns_1409_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1408_);
v___x_1410_ = lean_unsigned_to_nat(2u);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1411_, 0, v___x_1367_);
lean_closure_set(v___f_1411_, 1, v___x_1368_);
lean_closure_set(v___f_1411_, 2, v___x_1369_);
lean_closure_set(v___f_1411_, 3, v___x_1408_);
lean_closure_set(v___f_1411_, 4, v___x_1410_);
v___x_1412_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1410_);
lean_dec(v_stx_1370_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13));
v___x_1458_ = l_Lean_Syntax_getArgs(v___x_1412_);
lean_dec(v___x_1412_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14));
v___x_1460_ = lean_array_get_size(v___x_1458_);
v___x_1461_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1462_ = lean_nat_dec_lt(v___x_1408_, v___x_1460_);
if (v___x_1462_ == 0)
{
lean_dec_ref(v___x_1458_);
v___y_1415_ = v___x_1459_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1463_ = lean_box(v___x_1397_);
v___x_1464_ = lean_box(v___x_1394_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 4, 2);
lean_closure_set(v___f_1465_, 0, v___x_1463_);
lean_closure_set(v___f_1465_, 1, v___x_1464_);
v___x_1466_ = lean_box(v___x_1397_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v___x_1459_);
v___x_1468_ = lean_nat_dec_le(v___x_1460_, v___x_1460_);
if (v___x_1468_ == 0)
{
if (v___x_1462_ == 0)
{
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1458_);
v___y_1415_ = v___x_1459_;
goto v___jp_1414_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; lean_object* v_snd_1472_; 
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1460_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1461_, v___f_1465_, v___x_1458_, v___x_1469_, v___x_1470_, v___x_1467_);
v_snd_1472_ = lean_ctor_get(v___x_1471_, 1);
lean_inc(v_snd_1472_);
lean_dec(v___x_1471_);
v___y_1415_ = v_snd_1472_;
goto v___jp_1414_;
}
}
else
{
size_t v___x_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v_snd_1476_; 
v___x_1473_ = ((size_t)0ULL);
v___x_1474_ = lean_usize_of_nat(v___x_1460_);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1461_, v___f_1465_, v___x_1458_, v___x_1473_, v___x_1474_, v___x_1467_);
v_snd_1476_ = lean_ctor_get(v___x_1475_, 1);
lean_inc(v_snd_1476_);
lean_dec(v___x_1475_);
v___y_1415_ = v_snd_1476_;
goto v___jp_1414_;
}
}
v___jp_1414_:
{
size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v_sz_1416_ = lean_array_size(v___y_1415_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1413_, v___f_1411_, v_sz_1416_, v___x_1417_, v___y_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_7105__overap_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec(v_ns_1409_);
lean_dec_ref(v___f_1406_);
lean_dec(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_dec_ref(v___x_1379_);
lean_dec(v_inst_1378_);
lean_dec_ref(v_inst_1377_);
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v_inst_1374_);
lean_dec_ref(v_inst_1373_);
lean_dec(v_inst_1364_);
lean_dec(v_toPure_1363_);
lean_inc_ref(v_inst_1372_);
v___f_1419_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1419_, 0, v_inst_1372_);
v___f_1420_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1420_, 0, v_inst_1372_);
v___x_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1421_, 0, v___f_1419_);
lean_ctor_set(v___x_1421_, 1, v___f_1420_);
v___x_7105__overap_1422_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1421_);
v___x_1423_ = lean_apply_1(v___x_7105__overap_1422_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1424_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1423_, v___f_1407_);
v___x_1425_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1424_, v___f_1385_);
return v___x_1425_;
}
else
{
lean_object* v_val_1426_; lean_object* v___x_1427_; size_t v_sz_1428_; lean_object* v___x_1429_; lean_object* v_getEnv_1430_; lean_object* v_modifyEnv_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___f_1407_);
v_val_1426_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1418_);
v___x_1427_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1428_ = lean_array_size(v_val_1426_);
lean_inc(v_inst_1364_);
v___x_1429_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1373_, v_inst_1364_);
v_getEnv_1430_ = lean_ctor_get(v_inst_1374_, 0);
v_modifyEnv_1431_ = lean_ctor_get(v_inst_1374_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_inst_1374_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1433_ = v_inst_1374_;
v_isShared_1434_ = v_isSharedCheck_1457_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_modifyEnv_1431_);
lean_inc(v_getEnv_1430_);
lean_dec(v_inst_1374_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1457_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_tos_1435_; lean_object* v_froms_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_inc(v_val_1426_);
v_tos_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1427_, v___f_1375_, v_sz_1428_, v___x_1417_, v_val_1426_);
v_froms_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1427_, v___f_1376_, v_sz_1428_, v___x_1417_, v_val_1426_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1438_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1438_, 0, v_modifyEnv_1431_);
lean_closure_set(v___f_1438_, 1, v___x_1437_);
v___x_1439_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1439_, 0, lean_box(0));
lean_closure_set(v___x_1439_, 1, lean_box(0));
lean_closure_set(v___x_1439_, 2, lean_box(0));
lean_closure_set(v___x_1439_, 3, lean_box(0));
lean_closure_set(v___x_1439_, 4, v_getEnv_1430_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v___f_1438_);
lean_ctor_set(v___x_1433_, 0, v___x_1439_);
v___x_1441_ = v___x_1433_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___f_1438_);
v___x_1441_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_7133__overap_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_inc_ref(v_inst_1372_);
v___f_1442_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1442_, 0, v_inst_1372_);
v___f_1443_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1443_, 0, v_inst_1372_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___f_1442_);
lean_ctor_set(v___x_1444_, 1, v___f_1443_);
v___x_1445_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1446_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1437_, v___x_1445_, v_inst_1377_);
v___f_1447_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1447_, 0, v_inst_1378_);
lean_closure_set(v___f_1447_, 1, v___x_1437_);
lean_inc_ref(v___x_1379_);
lean_inc_ref(v___f_1447_);
v___x_1448_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1447_, v___x_1379_);
lean_inc(v___x_1448_);
lean_inc_ref(v___x_1446_);
lean_inc_ref(v___x_1444_);
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1444_);
lean_ctor_set(v___x_1449_, 1, v___x_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1));
lean_inc(v_ref_1384_);
lean_inc_ref(v___x_1429_);
lean_inc_ref(v___x_1449_);
lean_inc_ref(v___x_1441_);
lean_inc_ref(v___x_1379_);
lean_inc(v_toBind_1365_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 21, 20);
lean_closure_set(v___f_1451_, 0, v_froms_1436_);
lean_closure_set(v___f_1451_, 1, v_tos_1435_);
lean_closure_set(v___f_1451_, 2, v_toPure_1363_);
lean_closure_set(v___f_1451_, 3, v___x_1437_);
lean_closure_set(v___f_1451_, 4, v_inst_1380_);
lean_closure_set(v___f_1451_, 5, v_inst_1364_);
lean_closure_set(v___f_1451_, 6, v_toBind_1365_);
lean_closure_set(v___f_1451_, 7, v___x_1379_);
lean_closure_set(v___f_1451_, 8, v___x_1441_);
lean_closure_set(v___f_1451_, 9, v___x_1449_);
lean_closure_set(v___f_1451_, 10, v_inst_1381_);
lean_closure_set(v___f_1451_, 11, v_inst_1382_);
lean_closure_set(v___f_1451_, 12, v___x_1444_);
lean_closure_set(v___f_1451_, 13, v___x_1446_);
lean_closure_set(v___f_1451_, 14, v___x_1448_);
lean_closure_set(v___f_1451_, 15, v___f_1447_);
lean_closure_set(v___f_1451_, 16, v___x_1429_);
lean_closure_set(v___f_1451_, 17, v___x_1450_);
lean_closure_set(v___f_1451_, 18, v_ref_1384_);
lean_closure_set(v___f_1451_, 19, v___f_1406_);
v___x_7133__overap_1452_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1379_, v___x_1429_, v___x_1441_, v___x_1449_, v_ns_1409_);
v___x_1453_ = lean_apply_1(v___x_7133__overap_1452_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1454_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1453_, v___f_1451_);
v___x_1455_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1454_, v___f_1385_);
return v___x_1455_;
}
}
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v_getEnv_1478_; lean_object* v_modifyEnv_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1367_);
lean_inc(v_inst_1364_);
v___x_1477_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1373_, v_inst_1364_);
v_getEnv_1478_ = lean_ctor_get(v_inst_1374_, 0);
v_modifyEnv_1479_ = lean_ctor_get(v_inst_1374_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_inst_1374_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1481_ = v_inst_1374_;
v_isShared_1482_ = v_isSharedCheck_1508_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_modifyEnv_1479_);
lean_inc(v_getEnv_1478_);
lean_dec(v_inst_1374_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1508_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___f_1483_; lean_object* v___x_1484_; lean_object* v_ns_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_ids_1488_; lean_object* v___x_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_inc(v_ref_1384_);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1483_, 0, v___f_1371_);
lean_closure_set(v___f_1483_, 1, v_ref_1384_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v_ns_1485_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1484_);
v___x_1486_ = lean_unsigned_to_nat(2u);
v___x_1487_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1486_);
lean_dec(v_stx_1370_);
v_ids_1488_ = l_Lean_Syntax_getArgs(v___x_1487_);
lean_dec(v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1490_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1490_, 0, v_modifyEnv_1479_);
lean_closure_set(v___f_1490_, 1, v___x_1489_);
v___x_1491_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1491_, 0, lean_box(0));
lean_closure_set(v___x_1491_, 1, lean_box(0));
lean_closure_set(v___x_1491_, 2, lean_box(0));
lean_closure_set(v___x_1491_, 3, lean_box(0));
lean_closure_set(v___x_1491_, 4, v_getEnv_1478_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v___f_1490_);
lean_ctor_set(v___x_1481_, 0, v___x_1491_);
v___x_1493_ = v___x_1481_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___f_1490_);
v___x_1493_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_7177__overap_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_inc_ref(v_inst_1372_);
v___f_1494_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1494_, 0, v_inst_1372_);
v___f_1495_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1495_, 0, v_inst_1372_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___f_1494_);
lean_ctor_set(v___x_1496_, 1, v___f_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1498_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1489_, v___x_1497_, v_inst_1377_);
v___f_1499_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1499_, 0, v_inst_1378_);
lean_closure_set(v___f_1499_, 1, v___x_1489_);
lean_inc_ref(v___x_1379_);
lean_inc_ref(v___f_1499_);
v___x_1500_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1499_, v___x_1379_);
lean_inc(v___x_1500_);
lean_inc_ref(v___x_1498_);
lean_inc_ref(v___x_1496_);
v___x_1501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1496_);
lean_ctor_set(v___x_1501_, 1, v___x_1498_);
lean_ctor_set(v___x_1501_, 2, v___x_1500_);
lean_inc_ref(v___x_1477_);
lean_inc_ref(v___x_1501_);
lean_inc_ref(v___x_1493_);
lean_inc_ref(v___x_1379_);
lean_inc(v_toBind_1365_);
lean_inc(v_ref_1384_);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 20, 19);
lean_closure_set(v___f_1502_, 0, v_ids_1488_);
lean_closure_set(v___f_1502_, 1, v___f_1383_);
lean_closure_set(v___f_1502_, 2, v_inst_1364_);
lean_closure_set(v___f_1502_, 3, v_ref_1384_);
lean_closure_set(v___f_1502_, 4, v_toBind_1365_);
lean_closure_set(v___f_1502_, 5, v___f_1483_);
lean_closure_set(v___f_1502_, 6, v_toPure_1363_);
lean_closure_set(v___f_1502_, 7, v___x_1489_);
lean_closure_set(v___f_1502_, 8, v_inst_1380_);
lean_closure_set(v___f_1502_, 9, v___x_1379_);
lean_closure_set(v___f_1502_, 10, v___x_1493_);
lean_closure_set(v___f_1502_, 11, v___x_1501_);
lean_closure_set(v___f_1502_, 12, v_inst_1381_);
lean_closure_set(v___f_1502_, 13, v_inst_1382_);
lean_closure_set(v___f_1502_, 14, v___x_1496_);
lean_closure_set(v___f_1502_, 15, v___x_1498_);
lean_closure_set(v___f_1502_, 16, v___x_1500_);
lean_closure_set(v___f_1502_, 17, v___f_1499_);
lean_closure_set(v___f_1502_, 18, v___x_1477_);
v___x_7177__overap_1503_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1379_, v___x_1477_, v___x_1493_, v___x_1501_, v_ns_1485_);
v___x_1504_ = lean_apply_1(v___x_7177__overap_1503_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1505_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1504_, v___f_1502_);
v___x_1506_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1505_, v___f_1385_);
return v___x_1506_;
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v_getEnv_1510_; lean_object* v_modifyEnv_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___f_1383_);
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1367_);
lean_inc(v_inst_1364_);
v___x_1509_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1373_, v_inst_1364_);
v_getEnv_1510_ = lean_ctor_get(v_inst_1374_, 0);
v_modifyEnv_1511_ = lean_ctor_get(v_inst_1374_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_inst_1374_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1513_ = v_inst_1374_;
v_isShared_1514_ = v_isSharedCheck_1540_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_modifyEnv_1511_);
lean_inc(v_getEnv_1510_);
lean_dec(v_inst_1374_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1540_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___f_1515_; lean_object* v___x_1516_; lean_object* v_ns_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_ids_1520_; lean_object* v___x_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
lean_inc(v_ref_1384_);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1515_, 0, v___f_1371_);
lean_closure_set(v___f_1515_, 1, v_ref_1384_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v_ns_1517_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1516_);
v___x_1518_ = lean_unsigned_to_nat(2u);
v___x_1519_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1518_);
lean_dec(v_stx_1370_);
v_ids_1520_ = l_Lean_Syntax_getArgs(v___x_1519_);
lean_dec(v___x_1519_);
v___x_1521_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1522_, 0, v_modifyEnv_1511_);
lean_closure_set(v___f_1522_, 1, v___x_1521_);
v___x_1523_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1523_, 0, lean_box(0));
lean_closure_set(v___x_1523_, 1, lean_box(0));
lean_closure_set(v___x_1523_, 2, lean_box(0));
lean_closure_set(v___x_1523_, 3, lean_box(0));
lean_closure_set(v___x_1523_, 4, v_getEnv_1510_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___f_1522_);
lean_ctor_set(v___x_1513_, 0, v___x_1523_);
v___x_1525_ = v___x_1513_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___f_1522_);
v___x_1525_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___f_1534_; lean_object* v___x_7198__overap_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc_ref(v_inst_1372_);
v___f_1526_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1526_, 0, v_inst_1372_);
v___f_1527_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1527_, 0, v_inst_1372_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___f_1526_);
lean_ctor_set(v___x_1528_, 1, v___f_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1530_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1521_, v___x_1529_, v_inst_1377_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1531_, 0, v_inst_1378_);
lean_closure_set(v___f_1531_, 1, v___x_1521_);
lean_inc_ref(v___x_1379_);
lean_inc_ref(v___f_1531_);
v___x_1532_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1531_, v___x_1379_);
lean_inc(v___x_1532_);
lean_inc_ref(v___x_1530_);
lean_inc_ref(v___x_1528_);
v___x_1533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1528_);
lean_ctor_set(v___x_1533_, 1, v___x_1530_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
lean_inc(v_ref_1384_);
lean_inc_ref(v___x_1509_);
lean_inc_ref(v___x_1533_);
lean_inc_ref(v___x_1525_);
lean_inc_ref(v___x_1379_);
lean_inc(v_toBind_1365_);
v___f_1534_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 19, 18);
lean_closure_set(v___f_1534_, 0, v_toPure_1363_);
lean_closure_set(v___f_1534_, 1, v___x_1521_);
lean_closure_set(v___f_1534_, 2, v_inst_1380_);
lean_closure_set(v___f_1534_, 3, v_inst_1364_);
lean_closure_set(v___f_1534_, 4, v_toBind_1365_);
lean_closure_set(v___f_1534_, 5, v___x_1379_);
lean_closure_set(v___f_1534_, 6, v___x_1525_);
lean_closure_set(v___f_1534_, 7, v___x_1533_);
lean_closure_set(v___f_1534_, 8, v_inst_1381_);
lean_closure_set(v___f_1534_, 9, v_inst_1382_);
lean_closure_set(v___f_1534_, 10, v___x_1528_);
lean_closure_set(v___f_1534_, 11, v___x_1530_);
lean_closure_set(v___f_1534_, 12, v___x_1532_);
lean_closure_set(v___f_1534_, 13, v___f_1531_);
lean_closure_set(v___f_1534_, 14, v___x_1509_);
lean_closure_set(v___f_1534_, 15, v_ids_1520_);
lean_closure_set(v___f_1534_, 16, v_ref_1384_);
lean_closure_set(v___f_1534_, 17, v___f_1515_);
v___x_7198__overap_1535_ = l_Lean_resolveNamespace___redArg(v___x_1379_, v___x_1509_, v___x_1525_, v___x_1533_, v_ns_1517_);
v___x_1536_ = lean_apply_1(v___x_7198__overap_1535_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1537_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1536_, v___f_1534_);
v___x_1538_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1537_, v___f_1385_);
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_nss_1544_; lean_object* v___x_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; size_t v_sz_1548_; size_t v___x_1549_; lean_object* v___x_7209__overap_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec_ref(v___f_1383_);
lean_dec(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1367_);
lean_inc(v_ref_1384_);
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1541_, 0, v___f_1371_);
lean_closure_set(v___f_1541_, 1, v_ref_1384_);
v___x_1542_ = lean_unsigned_to_nat(1u);
v___x_1543_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1542_);
lean_dec(v_stx_1370_);
v_nss_1544_ = l_Lean_Syntax_getArgs(v___x_1543_);
lean_dec(v___x_1543_);
v___x_1545_ = lean_box(0);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1546_, 0, v___x_1545_);
lean_closure_set(v___f_1546_, 1, v_toPure_1363_);
lean_inc_ref(v___f_1546_);
lean_inc(v_toBind_1365_);
lean_inc_ref(v___x_1379_);
v___f_1547_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed), 15, 11);
lean_closure_set(v___f_1547_, 0, v_inst_1373_);
lean_closure_set(v___f_1547_, 1, v_inst_1364_);
lean_closure_set(v___f_1547_, 2, v_inst_1374_);
lean_closure_set(v___f_1547_, 3, v___x_1379_);
lean_closure_set(v___f_1547_, 4, v_toBind_1365_);
lean_closure_set(v___f_1547_, 5, v___f_1546_);
lean_closure_set(v___f_1547_, 6, v___x_1545_);
lean_closure_set(v___f_1547_, 7, v___f_1546_);
lean_closure_set(v___f_1547_, 8, v_inst_1372_);
lean_closure_set(v___f_1547_, 9, v_inst_1377_);
lean_closure_set(v___f_1547_, 10, v_inst_1378_);
v_sz_1548_ = lean_array_size(v_nss_1544_);
v___x_1549_ = ((size_t)0ULL);
v___x_7209__overap_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v_nss_1544_, v___f_1547_, v_sz_1548_, v___x_1549_, v___x_1545_);
v___x_1551_ = lean_apply_1(v___x_7209__overap_1550_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1552_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1551_, v___f_1541_);
v___x_1553_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1552_, v___f_1385_);
return v___x_1553_;
}
}
else
{
lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_nss_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___f_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_7221__overap_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v___f_1383_);
lean_dec(v_inst_1382_);
lean_dec_ref(v_inst_1381_);
lean_dec_ref(v_inst_1380_);
lean_dec_ref(v___f_1376_);
lean_dec_ref(v___f_1375_);
lean_dec_ref(v___x_1369_);
lean_dec_ref(v___x_1368_);
lean_dec_ref(v___x_1367_);
lean_inc(v_ref_1384_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1554_, 0, v___f_1371_);
lean_closure_set(v___f_1554_, 1, v_ref_1384_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = l_Lean_Syntax_getArg(v_stx_1370_, v___x_1555_);
lean_dec(v_stx_1370_);
v___x_1557_ = lean_box(0);
v_nss_1558_ = l_Lean_Syntax_getArgs(v___x_1556_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1560_, 0, v___x_1559_);
lean_closure_set(v___f_1560_, 1, v_toPure_1363_);
lean_inc_ref(v___f_1560_);
lean_inc(v_toBind_1365_);
lean_inc_ref(v___x_1379_);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed), 16, 12);
lean_closure_set(v___f_1561_, 0, v_inst_1373_);
lean_closure_set(v___f_1561_, 1, v_inst_1364_);
lean_closure_set(v___f_1561_, 2, v_inst_1374_);
lean_closure_set(v___f_1561_, 3, v___x_1379_);
lean_closure_set(v___f_1561_, 4, v_toBind_1365_);
lean_closure_set(v___f_1561_, 5, v___f_1560_);
lean_closure_set(v___f_1561_, 6, v___x_1557_);
lean_closure_set(v___f_1561_, 7, v___x_1559_);
lean_closure_set(v___f_1561_, 8, v___f_1560_);
lean_closure_set(v___f_1561_, 9, v_inst_1372_);
lean_closure_set(v___f_1561_, 10, v_inst_1377_);
lean_closure_set(v___f_1561_, 11, v_inst_1378_);
v_sz_1562_ = lean_array_size(v_nss_1558_);
v___x_1563_ = ((size_t)0ULL);
v___x_7221__overap_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1379_, v_nss_1558_, v___f_1561_, v_sz_1562_, v___x_1563_, v___x_1559_);
v___x_1565_ = lean_apply_1(v___x_7221__overap_1564_, v_ref_1384_);
lean_inc(v_toBind_1365_);
v___x_1566_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1565_, v___f_1554_);
v___x_1567_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1566_, v___f_1385_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object** _args){
lean_object* v_toPure_1568_ = _args[0];
lean_object* v_inst_1569_ = _args[1];
lean_object* v_toBind_1570_ = _args[2];
lean_object* v___x_1571_ = _args[3];
lean_object* v___x_1572_ = _args[4];
lean_object* v___x_1573_ = _args[5];
lean_object* v___x_1574_ = _args[6];
lean_object* v_stx_1575_ = _args[7];
lean_object* v___f_1576_ = _args[8];
lean_object* v_inst_1577_ = _args[9];
lean_object* v_inst_1578_ = _args[10];
lean_object* v_inst_1579_ = _args[11];
lean_object* v___f_1580_ = _args[12];
lean_object* v___f_1581_ = _args[13];
lean_object* v_inst_1582_ = _args[14];
lean_object* v_inst_1583_ = _args[15];
lean_object* v___x_1584_ = _args[16];
lean_object* v_inst_1585_ = _args[17];
lean_object* v_inst_1586_ = _args[18];
lean_object* v_inst_1587_ = _args[19];
lean_object* v___f_1588_ = _args[20];
lean_object* v_ref_1589_ = _args[21];
_start:
{
uint8_t v___x_8564__boxed_1590_; lean_object* v_res_1591_; 
v___x_8564__boxed_1590_ = lean_unbox(v___x_1571_);
v_res_1591_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v_toPure_1568_, v_inst_1569_, v_toBind_1570_, v___x_8564__boxed_1590_, v___x_1572_, v___x_1573_, v___x_1574_, v_stx_1575_, v___f_1576_, v_inst_1577_, v_inst_1578_, v_inst_1579_, v___f_1580_, v___f_1581_, v_inst_1582_, v_inst_1583_, v___x_1584_, v_inst_1585_, v_inst_1586_, v_inst_1587_, v___f_1588_, v_ref_1589_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v_toPure_1592_, lean_object* v_____x_1593_){
_start:
{
lean_object* v_fst_1594_; lean_object* v___x_1595_; 
v_fst_1594_ = lean_ctor_get(v_____x_1593_, 0);
lean_inc(v_fst_1594_);
lean_dec_ref(v_____x_1593_);
v___x_1595_ = lean_apply_2(v_toPure_1592_, lean_box(0), v_fst_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v_toApplicative_1605_, lean_object* v_stx_1606_, lean_object* v_____do__lift_1607_, lean_object* v_inst_1608_, lean_object* v_toBind_1609_, lean_object* v___f_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v___f_1614_, lean_object* v___f_1615_, lean_object* v_inst_1616_, lean_object* v_inst_1617_, lean_object* v___x_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v___f_1622_, lean_object* v_____do__lift_1623_){
_start:
{
lean_object* v_toPure_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_toPure_1624_ = lean_ctor_get(v_toApplicative_1605_, 1);
lean_inc(v_toPure_1624_);
lean_dec_ref(v_toApplicative_1605_);
v___x_1625_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0));
v___x_1626_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1));
v___x_1627_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2));
v___x_1628_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4));
lean_inc(v_stx_1606_);
v___x_1629_ = l_Lean_Syntax_isOfKind(v_stx_1606_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_____do__lift_1607_);
lean_ctor_set(v___x_1630_, 1, v_____do__lift_1623_);
v___x_1631_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1631_, 0, lean_box(0));
lean_closure_set(v___x_1631_, 1, lean_box(0));
lean_closure_set(v___x_1631_, 2, v___x_1630_);
lean_inc(v_inst_1608_);
v___x_1632_ = lean_apply_2(v_inst_1608_, lean_box(0), v___x_1631_);
v___x_1633_ = lean_box(v___x_1629_);
lean_inc(v_toBind_1609_);
lean_inc(v_toPure_1624_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 22, 21);
lean_closure_set(v___f_1634_, 0, v_toPure_1624_);
lean_closure_set(v___f_1634_, 1, v_inst_1608_);
lean_closure_set(v___f_1634_, 2, v_toBind_1609_);
lean_closure_set(v___f_1634_, 3, v___x_1633_);
lean_closure_set(v___f_1634_, 4, v___x_1625_);
lean_closure_set(v___f_1634_, 5, v___x_1626_);
lean_closure_set(v___f_1634_, 6, v___x_1627_);
lean_closure_set(v___f_1634_, 7, v_stx_1606_);
lean_closure_set(v___f_1634_, 8, v___f_1610_);
lean_closure_set(v___f_1634_, 9, v_inst_1611_);
lean_closure_set(v___f_1634_, 10, v_inst_1612_);
lean_closure_set(v___f_1634_, 11, v_inst_1613_);
lean_closure_set(v___f_1634_, 12, v___f_1614_);
lean_closure_set(v___f_1634_, 13, v___f_1615_);
lean_closure_set(v___f_1634_, 14, v_inst_1616_);
lean_closure_set(v___f_1634_, 15, v_inst_1617_);
lean_closure_set(v___f_1634_, 16, v___x_1618_);
lean_closure_set(v___f_1634_, 17, v_inst_1619_);
lean_closure_set(v___f_1634_, 18, v_inst_1620_);
lean_closure_set(v___f_1634_, 19, v_inst_1621_);
lean_closure_set(v___f_1634_, 20, v___f_1622_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36), 2, 1);
lean_closure_set(v___f_1635_, 0, v_toPure_1624_);
lean_inc(v_toBind_1609_);
v___x_1636_ = lean_apply_4(v_toBind_1609_, lean_box(0), lean_box(0), v___x_1632_, v___f_1634_);
v___x_1637_ = lean_apply_4(v_toBind_1609_, lean_box(0), lean_box(0), v___x_1636_, v___f_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object** _args){
lean_object* v_toApplicative_1638_ = _args[0];
lean_object* v_stx_1639_ = _args[1];
lean_object* v_____do__lift_1640_ = _args[2];
lean_object* v_inst_1641_ = _args[3];
lean_object* v_toBind_1642_ = _args[4];
lean_object* v___f_1643_ = _args[5];
lean_object* v_inst_1644_ = _args[6];
lean_object* v_inst_1645_ = _args[7];
lean_object* v_inst_1646_ = _args[8];
lean_object* v___f_1647_ = _args[9];
lean_object* v___f_1648_ = _args[10];
lean_object* v_inst_1649_ = _args[11];
lean_object* v_inst_1650_ = _args[12];
lean_object* v___x_1651_ = _args[13];
lean_object* v_inst_1652_ = _args[14];
lean_object* v_inst_1653_ = _args[15];
lean_object* v_inst_1654_ = _args[16];
lean_object* v___f_1655_ = _args[17];
lean_object* v_____do__lift_1656_ = _args[18];
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(v_toApplicative_1638_, v_stx_1639_, v_____do__lift_1640_, v_inst_1641_, v_toBind_1642_, v___f_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v___f_1647_, v___f_1648_, v_inst_1649_, v_inst_1650_, v___x_1651_, v_inst_1652_, v_inst_1653_, v_inst_1654_, v___f_1655_, v_____do__lift_1656_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v_toApplicative_1658_, lean_object* v_stx_1659_, lean_object* v_inst_1660_, lean_object* v_toBind_1661_, lean_object* v___f_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v___f_1666_, lean_object* v___f_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v___x_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v___f_1674_, lean_object* v_getCurrNamespace_1675_, lean_object* v_____do__lift_1676_){
_start:
{
lean_object* v___f_1677_; lean_object* v___x_1678_; 
lean_inc(v_toBind_1661_);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed), 19, 18);
lean_closure_set(v___f_1677_, 0, v_toApplicative_1658_);
lean_closure_set(v___f_1677_, 1, v_stx_1659_);
lean_closure_set(v___f_1677_, 2, v_____do__lift_1676_);
lean_closure_set(v___f_1677_, 3, v_inst_1660_);
lean_closure_set(v___f_1677_, 4, v_toBind_1661_);
lean_closure_set(v___f_1677_, 5, v___f_1662_);
lean_closure_set(v___f_1677_, 6, v_inst_1663_);
lean_closure_set(v___f_1677_, 7, v_inst_1664_);
lean_closure_set(v___f_1677_, 8, v_inst_1665_);
lean_closure_set(v___f_1677_, 9, v___f_1666_);
lean_closure_set(v___f_1677_, 10, v___f_1667_);
lean_closure_set(v___f_1677_, 11, v_inst_1668_);
lean_closure_set(v___f_1677_, 12, v_inst_1669_);
lean_closure_set(v___f_1677_, 13, v___x_1670_);
lean_closure_set(v___f_1677_, 14, v_inst_1671_);
lean_closure_set(v___f_1677_, 15, v_inst_1672_);
lean_closure_set(v___f_1677_, 16, v_inst_1673_);
lean_closure_set(v___f_1677_, 17, v___f_1674_);
v___x_1678_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v_getCurrNamespace_1675_, v___f_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object** _args){
lean_object* v_toApplicative_1679_ = _args[0];
lean_object* v_stx_1680_ = _args[1];
lean_object* v_inst_1681_ = _args[2];
lean_object* v_toBind_1682_ = _args[3];
lean_object* v___f_1683_ = _args[4];
lean_object* v_inst_1684_ = _args[5];
lean_object* v_inst_1685_ = _args[6];
lean_object* v_inst_1686_ = _args[7];
lean_object* v___f_1687_ = _args[8];
lean_object* v___f_1688_ = _args[9];
lean_object* v_inst_1689_ = _args[10];
lean_object* v_inst_1690_ = _args[11];
lean_object* v___x_1691_ = _args[12];
lean_object* v_inst_1692_ = _args[13];
lean_object* v_inst_1693_ = _args[14];
lean_object* v_inst_1694_ = _args[15];
lean_object* v___f_1695_ = _args[16];
lean_object* v_getCurrNamespace_1696_ = _args[17];
lean_object* v_____do__lift_1697_ = _args[18];
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(v_toApplicative_1679_, v_stx_1680_, v_inst_1681_, v_toBind_1682_, v___f_1683_, v_inst_1684_, v_inst_1685_, v_inst_1686_, v___f_1687_, v___f_1688_, v_inst_1689_, v_inst_1690_, v___x_1691_, v_inst_1692_, v_inst_1693_, v_inst_1694_, v___f_1695_, v_getCurrNamespace_1696_, v_____do__lift_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_stx_1712_){
_start:
{
lean_object* v_toApplicative_1713_; lean_object* v_toBind_1714_; lean_object* v_getCurrNamespace_1715_; lean_object* v_getOpenDecls_1716_; lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; 
v_toApplicative_1713_ = lean_ctor_get(v_inst_1702_, 0);
lean_inc_ref(v_toApplicative_1713_);
v_toBind_1714_ = lean_ctor_get(v_inst_1702_, 1);
lean_inc(v_toBind_1714_);
v_getCurrNamespace_1715_ = lean_ctor_get(v_inst_1710_, 0);
lean_inc(v_getCurrNamespace_1715_);
v_getOpenDecls_1716_ = lean_ctor_get(v_inst_1710_, 1);
lean_inc(v_getOpenDecls_1716_);
lean_dec_ref(v_inst_1710_);
lean_inc_ref(v_toApplicative_1713_);
v___f_1717_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1717_, 0, v_toApplicative_1713_);
lean_inc(v_toBind_1714_);
lean_inc(v_inst_1707_);
v___f_1718_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1718_, 0, v_inst_1707_);
lean_closure_set(v___f_1718_, 1, v_toBind_1714_);
lean_closure_set(v___f_1718_, 2, v___f_1717_);
v___f_1719_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0));
v___f_1720_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1));
v___f_1721_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2));
lean_inc_ref(v_inst_1702_);
v___x_1722_ = l_StateRefT_x27_instMonad___redArg(v_inst_1702_);
lean_inc(v_toBind_1714_);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed), 19, 18);
lean_closure_set(v___f_1723_, 0, v_toApplicative_1713_);
lean_closure_set(v___f_1723_, 1, v_stx_1712_);
lean_closure_set(v___f_1723_, 2, v_inst_1707_);
lean_closure_set(v___f_1723_, 3, v_toBind_1714_);
lean_closure_set(v___f_1723_, 4, v___f_1718_);
lean_closure_set(v___f_1723_, 5, v_inst_1704_);
lean_closure_set(v___f_1723_, 6, v_inst_1702_);
lean_closure_set(v___f_1723_, 7, v_inst_1703_);
lean_closure_set(v___f_1723_, 8, v___f_1719_);
lean_closure_set(v___f_1723_, 9, v___f_1720_);
lean_closure_set(v___f_1723_, 10, v_inst_1705_);
lean_closure_set(v___f_1723_, 11, v_inst_1706_);
lean_closure_set(v___f_1723_, 12, v___x_1722_);
lean_closure_set(v___f_1723_, 13, v_inst_1711_);
lean_closure_set(v___f_1723_, 14, v_inst_1708_);
lean_closure_set(v___f_1723_, 15, v_inst_1709_);
lean_closure_set(v___f_1723_, 16, v___f_1721_);
lean_closure_set(v___f_1723_, 17, v_getCurrNamespace_1715_);
v___x_1724_ = lean_apply_4(v_toBind_1714_, lean_box(0), lean_box(0), v_getOpenDecls_1716_, v___f_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_stx_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1726_, v_inst_1727_, v_inst_1728_, v_inst_1729_, v_inst_1730_, v_inst_1731_, v_inst_1732_, v_inst_1733_, v_inst_1734_, v_inst_1735_, v_stx_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object* v_a_1738_, lean_object* v_toPure_1739_, lean_object* v_s_1740_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_a_1738_);
lean_ctor_set(v___x_1741_, 1, v_s_1740_);
v___x_1742_ = lean_apply_2(v_toPure_1739_, lean_box(0), v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object* v_toPure_1743_, lean_object* v_ref_1744_, lean_object* v_inst_1745_, lean_object* v_toBind_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1748_, 0, v_a_1747_);
lean_closure_set(v___f_1748_, 1, v_toPure_1743_);
v___x_1749_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1749_, 0, lean_box(0));
lean_closure_set(v___x_1749_, 1, lean_box(0));
lean_closure_set(v___x_1749_, 2, v_ref_1744_);
v___x_1750_ = lean_apply_2(v_inst_1745_, lean_box(0), v___x_1749_);
v___x_1751_ = lean_apply_4(v_toBind_1746_, lean_box(0), lean_box(0), v___x_1750_, v___f_1748_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object* v_toPure_1752_, lean_object* v_inst_1753_, lean_object* v_toBind_1754_, lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v___x_1759_, lean_object* v___f_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v___x_1763_, lean_object* v_nss_1764_, lean_object* v_idStx_1765_, lean_object* v_ref_1766_){
_start:
{
lean_object* v___f_1767_; lean_object* v___x_100__overap_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_inc(v_toBind_1754_);
lean_inc(v_ref_1766_);
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1767_, 0, v_toPure_1752_);
lean_closure_set(v___f_1767_, 1, v_ref_1766_);
lean_closure_set(v___f_1767_, 2, v_inst_1753_);
lean_closure_set(v___f_1767_, 3, v_toBind_1754_);
v___x_100__overap_1768_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1755_, v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v___f_1760_, v___x_1761_, v___x_1762_, v___x_1763_, v_nss_1764_, v_idStx_1765_);
v___x_1769_ = lean_apply_1(v___x_100__overap_1768_, v_ref_1766_);
v___x_1770_ = lean_apply_4(v_toBind_1754_, lean_box(0), lean_box(0), v___x_1769_, v___f_1767_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object* v_toPure_1771_, lean_object* v_____x_1772_){
_start:
{
lean_object* v_fst_1773_; lean_object* v___x_1774_; 
v_fst_1773_ = lean_ctor_get(v_____x_1772_, 0);
lean_inc(v_fst_1773_);
lean_dec_ref(v_____x_1772_);
v___x_1774_ = lean_apply_2(v_toPure_1771_, lean_box(0), v_fst_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object* v_toApplicative_1775_, lean_object* v_____do__lift_1776_, lean_object* v_inst_1777_, lean_object* v_toBind_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v___x_1783_, lean_object* v___f_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, lean_object* v_nss_1788_, lean_object* v_idStx_1789_, lean_object* v_____do__lift_1790_){
_start:
{
lean_object* v_toPure_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___f_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toPure_1791_ = lean_ctor_get(v_toApplicative_1775_, 1);
lean_inc(v_toPure_1791_);
lean_dec_ref(v_toApplicative_1775_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_____do__lift_1776_);
lean_ctor_set(v___x_1792_, 1, v_____do__lift_1790_);
v___x_1793_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1793_, 0, lean_box(0));
lean_closure_set(v___x_1793_, 1, lean_box(0));
lean_closure_set(v___x_1793_, 2, v___x_1792_);
lean_inc(v_inst_1777_);
v___x_1794_ = lean_apply_2(v_inst_1777_, lean_box(0), v___x_1793_);
lean_inc(v_toBind_1778_);
lean_inc(v_toPure_1791_);
v___f_1795_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2), 15, 14);
lean_closure_set(v___f_1795_, 0, v_toPure_1791_);
lean_closure_set(v___f_1795_, 1, v_inst_1777_);
lean_closure_set(v___f_1795_, 2, v_toBind_1778_);
lean_closure_set(v___f_1795_, 3, v___x_1779_);
lean_closure_set(v___f_1795_, 4, v___x_1780_);
lean_closure_set(v___f_1795_, 5, v___x_1781_);
lean_closure_set(v___f_1795_, 6, v___x_1782_);
lean_closure_set(v___f_1795_, 7, v___x_1783_);
lean_closure_set(v___f_1795_, 8, v___f_1784_);
lean_closure_set(v___f_1795_, 9, v___x_1785_);
lean_closure_set(v___f_1795_, 10, v___x_1786_);
lean_closure_set(v___f_1795_, 11, v___x_1787_);
lean_closure_set(v___f_1795_, 12, v_nss_1788_);
lean_closure_set(v___f_1795_, 13, v_idStx_1789_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1796_, 0, v_toPure_1791_);
lean_inc(v_toBind_1778_);
v___x_1797_ = lean_apply_4(v_toBind_1778_, lean_box(0), lean_box(0), v___x_1794_, v___f_1795_);
v___x_1798_ = lean_apply_4(v_toBind_1778_, lean_box(0), lean_box(0), v___x_1797_, v___f_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object* v_toApplicative_1799_, lean_object* v_inst_1800_, lean_object* v_toBind_1801_, lean_object* v___x_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v___f_1807_, lean_object* v___x_1808_, lean_object* v___x_1809_, lean_object* v___x_1810_, lean_object* v_nss_1811_, lean_object* v_idStx_1812_, lean_object* v_getCurrNamespace_1813_, lean_object* v_____do__lift_1814_){
_start:
{
lean_object* v___f_1815_; lean_object* v___x_1816_; 
lean_inc(v_toBind_1801_);
v___f_1815_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4), 16, 15);
lean_closure_set(v___f_1815_, 0, v_toApplicative_1799_);
lean_closure_set(v___f_1815_, 1, v_____do__lift_1814_);
lean_closure_set(v___f_1815_, 2, v_inst_1800_);
lean_closure_set(v___f_1815_, 3, v_toBind_1801_);
lean_closure_set(v___f_1815_, 4, v___x_1802_);
lean_closure_set(v___f_1815_, 5, v___x_1803_);
lean_closure_set(v___f_1815_, 6, v___x_1804_);
lean_closure_set(v___f_1815_, 7, v___x_1805_);
lean_closure_set(v___f_1815_, 8, v___x_1806_);
lean_closure_set(v___f_1815_, 9, v___f_1807_);
lean_closure_set(v___f_1815_, 10, v___x_1808_);
lean_closure_set(v___f_1815_, 11, v___x_1809_);
lean_closure_set(v___f_1815_, 12, v___x_1810_);
lean_closure_set(v___f_1815_, 13, v_nss_1811_);
lean_closure_set(v___f_1815_, 14, v_idStx_1812_);
v___x_1816_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v_getCurrNamespace_1813_, v___f_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_nss_1826_, lean_object* v_idStx_1827_){
_start:
{
lean_object* v_toApplicative_1828_; lean_object* v_toBind_1829_; lean_object* v_getCurrNamespace_1830_; lean_object* v_getOpenDecls_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1862_; 
v_toApplicative_1828_ = lean_ctor_get(v_inst_1817_, 0);
lean_inc_ref(v_toApplicative_1828_);
v_toBind_1829_ = lean_ctor_get(v_inst_1817_, 1);
lean_inc(v_toBind_1829_);
v_getCurrNamespace_1830_ = lean_ctor_get(v_inst_1825_, 0);
v_getOpenDecls_1831_ = lean_ctor_get(v_inst_1825_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_inst_1825_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1833_ = v_inst_1825_;
v_isShared_1834_ = v_isSharedCheck_1862_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_getOpenDecls_1831_);
lean_inc(v_getCurrNamespace_1830_);
lean_dec(v_inst_1825_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1862_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v_getEnv_1836_; lean_object* v_modifyEnv_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1861_; 
lean_inc_ref(v_inst_1817_);
v___x_1835_ = l_StateRefT_x27_instMonad___redArg(v_inst_1817_);
v_getEnv_1836_ = lean_ctor_get(v_inst_1818_, 0);
v_modifyEnv_1837_ = lean_ctor_get(v_inst_1818_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_inst_1818_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1839_ = v_inst_1818_;
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_modifyEnv_1837_);
lean_inc(v_getEnv_1836_);
lean_dec(v_inst_1818_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1861_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1841_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1842_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1842_, 0, v_modifyEnv_1837_);
lean_closure_set(v___f_1842_, 1, v___x_1841_);
v___x_1843_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1843_, 0, lean_box(0));
lean_closure_set(v___x_1843_, 1, lean_box(0));
lean_closure_set(v___x_1843_, 2, lean_box(0));
lean_closure_set(v___x_1843_, 3, lean_box(0));
lean_closure_set(v___x_1843_, 4, v_getEnv_1836_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___f_1842_);
lean_ctor_set(v___x_1839_, 0, v___x_1843_);
v___x_1845_ = v___x_1839_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___f_1842_);
v___x_1845_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___f_1846_; lean_object* v___f_1847_; lean_object* v___x_1849_; 
lean_inc_ref(v_inst_1819_);
v___f_1846_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1846_, 0, v_inst_1819_);
v___f_1847_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1847_, 0, v_inst_1819_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___f_1847_);
lean_ctor_set(v___x_1833_, 0, v___f_1846_);
v___x_1849_ = v___x_1833_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___f_1846_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___f_1847_);
v___x_1849_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___f_1857_; lean_object* v___x_1858_; 
v___x_1850_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1851_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1841_, v___x_1850_, v_inst_1820_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1852_, 0, v_inst_1821_);
lean_closure_set(v___f_1852_, 1, v___x_1841_);
lean_inc_ref(v___x_1835_);
lean_inc_ref(v___f_1852_);
v___x_1853_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1852_, v___x_1835_);
v___x_1854_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1841_, v_inst_1823_);
v___x_1855_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1855_, 0, lean_box(0));
lean_closure_set(v___x_1855_, 1, lean_box(0));
lean_closure_set(v___x_1855_, 2, lean_box(0));
lean_closure_set(v___x_1855_, 3, lean_box(0));
lean_closure_set(v___x_1855_, 4, v_inst_1824_);
lean_inc(v_inst_1822_);
v___x_1856_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1817_, v_inst_1822_);
lean_inc(v_toBind_1829_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5), 16, 15);
lean_closure_set(v___f_1857_, 0, v_toApplicative_1828_);
lean_closure_set(v___f_1857_, 1, v_inst_1822_);
lean_closure_set(v___f_1857_, 2, v_toBind_1829_);
lean_closure_set(v___f_1857_, 3, v___x_1835_);
lean_closure_set(v___f_1857_, 4, v___x_1845_);
lean_closure_set(v___f_1857_, 5, v___x_1849_);
lean_closure_set(v___f_1857_, 6, v___x_1851_);
lean_closure_set(v___f_1857_, 7, v___x_1853_);
lean_closure_set(v___f_1857_, 8, v___f_1852_);
lean_closure_set(v___f_1857_, 9, v___x_1854_);
lean_closure_set(v___f_1857_, 10, v___x_1855_);
lean_closure_set(v___f_1857_, 11, v___x_1856_);
lean_closure_set(v___f_1857_, 12, v_nss_1826_);
lean_closure_set(v___f_1857_, 13, v_idStx_1827_);
lean_closure_set(v___f_1857_, 14, v_getCurrNamespace_1830_);
v___x_1858_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v_getOpenDecls_1831_, v___f_1857_);
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object* v_m_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_nss_1873_, lean_object* v_idStx_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(v_inst_1864_, v_inst_1865_, v_inst_1866_, v_inst_1867_, v_inst_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_nss_1873_, v_idStx_1874_);
return v___x_1875_;
}
}
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
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
