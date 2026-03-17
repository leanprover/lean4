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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0_value;
static const lean_closure_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_27_ = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(v___x_27_, 0, lean_box(0));
lean_closure_set(v___x_27_, 1, lean_box(0));
lean_closure_set(v___x_27_, 2, lean_box(0));
lean_closure_set(v___x_27_, 3, v_inst_24_);
lean_inc_ref(v___x_27_);
lean_inc_ref(v_inst_23_);
v___x_28_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(v___x_28_, 0, lean_box(0));
lean_closure_set(v___x_28_, 1, lean_box(0));
lean_closure_set(v___x_28_, 2, v_inst_23_);
lean_closure_set(v___x_28_, 3, lean_box(0));
lean_closure_set(v___x_28_, 4, lean_box(0));
lean_closure_set(v___x_28_, 5, v___x_27_);
lean_closure_set(v___x_28_, 6, v___f_25_);
v___x_29_ = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl(lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_decl_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_122_, v_decl_123_, v_a_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__0(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_box(0);
v___x_128_ = l_Lean_mkConst(v_x_126_, v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1(lean_object* v_toPure_129_, lean_object* v_p_130_){
_start:
{
lean_object* v_snd_131_; lean_object* v_fst_132_; lean_object* v_snd_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
v_snd_131_ = lean_ctor_get(v_p_130_, 1);
lean_inc(v_snd_131_);
lean_dec_ref(v_p_130_);
v_fst_132_ = lean_ctor_get(v_snd_131_, 0);
v_snd_133_ = lean_ctor_get(v_snd_131_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_snd_131_);
if (v_isSharedCheck_142_ == 0)
{
v___x_135_ = v_snd_131_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_snd_133_);
lean_inc(v_fst_132_);
lean_dec(v_snd_131_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_fst_132_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_snd_133_);
v___x_138_ = v_reuseFailAlloc_141_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = lean_apply_2(v_toPure_129_, lean_box(0), v___x_139_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2(lean_object* v_snd_143_, lean_object* v_fst_144_, lean_object* v_toPure_145_, lean_object* v_declName_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = lean_array_push(v_snd_143_, v_declName_146_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v_fst_144_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = lean_apply_2(v_toPure_145_, lean_box(0), v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3(lean_object* v_fst_152_, lean_object* v_snd_153_, lean_object* v_toPure_154_, lean_object* v_ex_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = lean_array_push(v_fst_152_, v_ex_155_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set(v___x_158_, 1, v_snd_153_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_apply_2(v_toPure_154_, lean_box(0), v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4(lean_object* v_inst_161_, lean_object* v_toPure_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_idStx_171_, lean_object* v_toBind_172_, lean_object* v___f_173_, lean_object* v_a_174_, lean_object* v_x_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_fst_177_; lean_object* v_snd_178_; lean_object* v_tryCatch_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_fst_177_ = lean_ctor_get(v___y_176_, 0);
lean_inc(v_fst_177_);
v_snd_178_ = lean_ctor_get(v___y_176_, 1);
lean_inc(v_snd_178_);
lean_dec_ref(v___y_176_);
v_tryCatch_179_ = lean_ctor_get(v_inst_161_, 1);
lean_inc(v_tryCatch_179_);
lean_inc(v_toPure_162_);
lean_inc(v_fst_177_);
lean_inc(v_snd_178_);
v___f_180_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__2), 4, 3);
lean_closure_set(v___f_180_, 0, v_snd_178_);
lean_closure_set(v___f_180_, 1, v_fst_177_);
lean_closure_set(v___f_180_, 2, v_toPure_162_);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_181_, 0, v_fst_177_);
lean_closure_set(v___f_181_, 1, v_snd_178_);
lean_closure_set(v___f_181_, 2, v_toPure_162_);
v___x_182_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v_inst_163_, v_inst_164_, v_inst_161_, v_inst_165_, v_inst_166_, v_inst_167_, v_inst_168_, v_inst_169_, v_inst_170_, v_a_174_, v_idStx_171_);
lean_inc(v_toBind_172_);
v___x_183_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_182_, v___f_180_);
v___x_184_ = lean_apply_3(v_tryCatch_179_, lean_box(0), v___x_183_, v___f_181_);
v___x_185_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_184_, v___f_173_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__10));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__12));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(lean_object* v_snd_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_idStx_216_, lean_object* v___f_217_, lean_object* v_inst_218_, lean_object* v_toBind_219_, lean_object* v___x_220_, lean_object* v_toPure_221_, lean_object* v_____r_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = lean_array_get_size(v_snd_212_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_getRef_228_; lean_object* v_withRef_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_toPure_221_);
lean_inc_ref(v_inst_214_);
v___x_226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_226_, 0, v_inst_213_);
lean_ctor_set(v___x_226_, 1, v_inst_214_);
lean_ctor_set(v___x_226_, 2, v_inst_215_);
v___x_227_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_getRef_228_ = lean_ctor_get(v_inst_214_, 0);
v_withRef_229_ = lean_ctor_get(v_inst_214_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_inst_214_);
if (v_isSharedCheck_253_ == 0)
{
v___x_231_ = v_inst_214_;
v_isShared_232_ = v_isSharedCheck_253_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_withRef_229_);
lean_inc(v_getRef_228_);
lean_dec(v_inst_214_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_253_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
size_t v_sz_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v_sz_233_ = lean_array_size(v_snd_212_);
v___x_234_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__11);
v___x_235_ = l_Lean_Syntax_getId(v_idStx_216_);
v___x_236_ = l_Lean_MessageData_ofName(v___x_235_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 7);
lean_ctor_set(v___x_231_, 1, v___x_236_);
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_252_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___x_251_; 
v___x_239_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__13);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_227_, v___f_217_, v_sz_233_, v___x_241_, v_snd_212_);
v___x_243_ = lean_array_to_list(v___x_242_);
v___x_244_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__14));
v___x_245_ = lean_box(0);
v___x_246_ = l_List_mapTR_loop___redArg(v___x_244_, v___x_243_, v___x_245_);
v___x_247_ = l_Lean_MessageData_ofList(v___x_246_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_240_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwError___redArg(v_inst_218_, v___x_226_, v___x_248_);
v___f_250_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveId___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_250_, 0, v_idStx_216_);
lean_closure_set(v___f_250_, 1, v_withRef_229_);
lean_closure_set(v___f_250_, 2, v___x_249_);
v___x_251_ = lean_apply_4(v_toBind_219_, lean_box(0), lean_box(0), v_getRef_228_, v___f_250_);
return v___x_251_;
}
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_toBind_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v___f_217_);
lean_dec(v_idStx_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec_ref(v_inst_213_);
v___x_254_ = lean_array_fget(v_snd_212_, v___x_220_);
lean_dec(v_snd_212_);
v___x_255_ = lean_apply_2(v_toPure_221_, lean_box(0), v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed(lean_object* v_snd_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_idStx_260_, lean_object* v___f_261_, lean_object* v_inst_262_, lean_object* v_toBind_263_, lean_object* v___x_264_, lean_object* v_toPure_265_, lean_object* v_____r_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_256_, v_inst_257_, v_inst_258_, v_inst_259_, v_idStx_260_, v___f_261_, v_inst_262_, v_toBind_263_, v___x_264_, v_toPure_265_, v_____r_266_);
lean_dec(v___x_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5(lean_object* v___f_268_, lean_object* v_____r_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = lean_apply_1(v___f_268_, v_____r_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(lean_object* v_idStx_271_, lean_object* v_withRef_272_, lean_object* v___y_273_, lean_object* v_oldRef_274_){
_start:
{
lean_object* v_ref_275_; lean_object* v___x_276_; 
v_ref_275_ = l_Lean_replaceRef(v_idStx_271_, v_oldRef_274_);
v___x_276_ = lean_apply_3(v_withRef_272_, lean_box(0), v_ref_275_, v___y_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed(lean_object* v_idStx_277_, lean_object* v_withRef_278_, lean_object* v___y_279_, lean_object* v_oldRef_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7(v_idStx_277_, v_withRef_278_, v___y_279_, v_oldRef_280_);
lean_dec(v_oldRef_280_);
lean_dec(v_idStx_277_);
return v_res_281_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__1));
v___x_286_ = l_Lean_MessageData_ofFormat(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_idStx_290_, lean_object* v___f_291_, lean_object* v_inst_292_, lean_object* v_toBind_293_, lean_object* v___x_294_, lean_object* v_toPure_295_, lean_object* v_nss_296_, lean_object* v_inst_297_, lean_object* v_____s_298_){
_start:
{
lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_fst_299_ = lean_ctor_get(v_____s_298_, 0);
lean_inc(v_fst_299_);
v_snd_300_ = lean_ctor_get(v_____s_298_, 1);
lean_inc(v_snd_300_);
lean_dec_ref(v_____s_298_);
lean_inc(v_toPure_295_);
lean_inc(v___x_294_);
lean_inc(v_toBind_293_);
lean_inc_ref(v_inst_292_);
lean_inc_ref(v___f_291_);
lean_inc(v_idStx_290_);
lean_inc(v_inst_289_);
lean_inc_ref(v_inst_288_);
lean_inc_ref(v_inst_287_);
lean_inc(v_snd_300_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_301_, 0, v_snd_300_);
lean_closure_set(v___f_301_, 1, v_inst_287_);
lean_closure_set(v___f_301_, 2, v_inst_288_);
lean_closure_set(v___f_301_, 3, v_inst_289_);
lean_closure_set(v___f_301_, 4, v_idStx_290_);
lean_closure_set(v___f_301_, 5, v___f_291_);
lean_closure_set(v___f_301_, 6, v_inst_292_);
lean_closure_set(v___f_301_, 7, v_toBind_293_);
lean_closure_set(v___f_301_, 8, v___x_294_);
lean_closure_set(v___f_301_, 9, v_toPure_295_);
v___x_302_ = lean_array_get_size(v_fst_299_);
v___x_303_ = l_List_lengthTR___redArg(v_nss_296_);
v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v___f_301_);
lean_dec(v_fst_299_);
lean_dec_ref(v_inst_297_);
v___x_305_ = lean_box(0);
v___x_306_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6(v_snd_300_, v_inst_287_, v_inst_288_, v_inst_289_, v_idStx_290_, v___f_291_, v_inst_292_, v_toBind_293_, v___x_294_, v_toPure_295_, v___x_305_);
lean_dec(v___x_294_);
return v___x_306_;
}
else
{
lean_object* v___f_307_; lean_object* v___y_309_; lean_object* v___x_315_; uint8_t v___x_316_; 
lean_dec(v_snd_300_);
lean_dec(v_toPure_295_);
lean_dec_ref(v___f_291_);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__5), 2, 1);
lean_closure_set(v___f_307_, 0, v___f_301_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_dec_eq(v___x_302_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v___x_294_);
lean_inc_ref(v_inst_288_);
v___x_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_317_, 0, v_inst_287_);
lean_ctor_set(v___x_317_, 1, v_inst_288_);
lean_ctor_set(v___x_317_, 2, v_inst_289_);
v___x_318_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___closed__2);
v___x_319_ = l_Lean_Elab_throwErrorWithNestedErrors___redArg(v___x_317_, v_inst_292_, v_inst_297_, v___x_318_, v_fst_299_);
v___y_309_ = v___x_319_;
goto v___jp_308_;
}
else
{
lean_object* v_throw_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_inst_297_);
lean_dec_ref(v_inst_292_);
lean_dec(v_inst_289_);
v_throw_320_ = lean_ctor_get(v_inst_287_, 0);
lean_inc(v_throw_320_);
lean_dec_ref(v_inst_287_);
v___x_321_ = lean_array_fget(v_fst_299_, v___x_294_);
lean_dec(v___x_294_);
lean_dec(v_fst_299_);
v___x_322_ = lean_apply_2(v_throw_320_, lean_box(0), v___x_321_);
v___y_309_ = v___x_322_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v_getRef_310_; lean_object* v_withRef_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_getRef_310_ = lean_ctor_get(v_inst_288_, 0);
lean_inc(v_getRef_310_);
v_withRef_311_ = lean_ctor_get(v_inst_288_, 1);
lean_inc(v_withRef_311_);
lean_dec_ref(v_inst_288_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_312_, 0, v_idStx_290_);
lean_closure_set(v___f_312_, 1, v_withRef_311_);
lean_closure_set(v___f_312_, 2, v___y_309_);
lean_inc(v_toBind_293_);
v___x_313_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v_getRef_310_, v___f_312_);
v___x_314_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_313_, v___f_307_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed(lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_idStx_326_, lean_object* v___f_327_, lean_object* v_inst_328_, lean_object* v_toBind_329_, lean_object* v___x_330_, lean_object* v_toPure_331_, lean_object* v_nss_332_, lean_object* v_inst_333_, lean_object* v_____s_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8(v_inst_323_, v_inst_324_, v_inst_325_, v_idStx_326_, v___f_327_, v_inst_328_, v_toBind_329_, v___x_330_, v_toPure_331_, v_nss_332_, v_inst_333_, v_____s_334_);
lean_dec(v_nss_332_);
return v_res_335_;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2(void){
_start:
{
lean_object* v_exs_339_; lean_object* v___x_340_; 
v_exs_339_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__1));
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_exs_339_);
lean_ctor_set(v___x_340_, 1, v_exs_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_nss_350_, lean_object* v_idStx_351_){
_start:
{
lean_object* v_toApplicative_352_; lean_object* v_toBind_353_; lean_object* v_toPure_354_; lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_toApplicative_352_ = lean_ctor_get(v_inst_341_, 0);
v_toBind_353_ = lean_ctor_get(v_inst_341_, 1);
lean_inc(v_toBind_353_);
v_toPure_354_ = lean_ctor_get(v_toApplicative_352_, 1);
v___f_355_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__0));
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_obj_once(&l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2, &l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2_once, _init_l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___closed__2);
lean_inc(v_toPure_354_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_358_, 0, v_toPure_354_);
lean_inc(v_toBind_353_);
lean_inc(v_idStx_351_);
lean_inc_ref(v_inst_347_);
lean_inc(v_inst_345_);
lean_inc_ref(v_inst_344_);
lean_inc_ref(v_inst_341_);
lean_inc(v_toPure_354_);
lean_inc_ref(v_inst_343_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__4), 16, 13);
lean_closure_set(v___f_359_, 0, v_inst_343_);
lean_closure_set(v___f_359_, 1, v_toPure_354_);
lean_closure_set(v___f_359_, 2, v_inst_341_);
lean_closure_set(v___f_359_, 3, v_inst_342_);
lean_closure_set(v___f_359_, 4, v_inst_344_);
lean_closure_set(v___f_359_, 5, v_inst_345_);
lean_closure_set(v___f_359_, 6, v_inst_346_);
lean_closure_set(v___f_359_, 7, v_inst_347_);
lean_closure_set(v___f_359_, 8, v_inst_348_);
lean_closure_set(v___f_359_, 9, v_inst_349_);
lean_closure_set(v___f_359_, 10, v_idStx_351_);
lean_closure_set(v___f_359_, 11, v_toBind_353_);
lean_closure_set(v___f_359_, 12, v___f_358_);
lean_inc(v_nss_350_);
lean_inc(v_toPure_354_);
lean_inc(v_toBind_353_);
lean_inc_ref(v_inst_341_);
v___f_360_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__8___boxed), 12, 11);
lean_closure_set(v___f_360_, 0, v_inst_343_);
lean_closure_set(v___f_360_, 1, v_inst_344_);
lean_closure_set(v___f_360_, 2, v_inst_345_);
lean_closure_set(v___f_360_, 3, v_idStx_351_);
lean_closure_set(v___f_360_, 4, v___f_355_);
lean_closure_set(v___f_360_, 5, v_inst_341_);
lean_closure_set(v___f_360_, 6, v_toBind_353_);
lean_closure_set(v___f_360_, 7, v___x_356_);
lean_closure_set(v___f_360_, 8, v_toPure_354_);
lean_closure_set(v___f_360_, 9, v_nss_350_);
lean_closure_set(v___f_360_, 10, v_inst_347_);
v___x_361_ = l_List_forIn_x27_loop___redArg(v_inst_341_, v___f_359_, v_nss_350_, v___x_357_);
v___x_362_ = lean_apply_4(v_toBind_353_, lean_box(0), lean_box(0), v___x_361_, v___f_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore(lean_object* v_m_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_nss_373_, lean_object* v_idStx_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v_inst_364_, v_inst_365_, v_inst_366_, v_inst_367_, v_inst_368_, v_inst_369_, v_inst_370_, v_inst_371_, v_inst_372_, v_nss_373_, v_idStx_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0(lean_object* v_toApplicative_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_openDecls_378_; lean_object* v_toPure_379_; lean_object* v___x_380_; 
v_openDecls_378_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_openDecls_378_);
lean_dec_ref(v_a_377_);
v_toPure_379_ = lean_ctor_get(v_toApplicative_376_, 1);
lean_inc(v_toPure_379_);
lean_dec_ref(v_toApplicative_376_);
v___x_380_ = lean_apply_2(v_toPure_379_, lean_box(0), v_openDecls_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1(lean_object* v_inst_381_, lean_object* v_toBind_382_, lean_object* v___f_383_, lean_object* v_____r_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_386_, 0, lean_box(0));
lean_closure_set(v___x_386_, 1, lean_box(0));
lean_closure_set(v___x_386_, 2, v___y_385_);
v___x_387_ = lean_apply_2(v_inst_381_, lean_box(0), v___x_386_);
v___x_388_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_387_, v___f_383_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(lean_object* v_x_389_){
_start:
{
lean_object* v_snd_390_; 
v_snd_390_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_snd_390_);
return v_snd_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2___boxed(lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__2(v_x_391_);
lean_dec_ref(v_x_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(lean_object* v_x_393_){
_start:
{
lean_object* v_fst_394_; 
v_fst_394_ = lean_ctor_get(v_x_393_, 0);
lean_inc(v_fst_394_);
return v_fst_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3___boxed(lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__3(v_x_395_);
lean_dec_ref(v_x_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4(lean_object* v_a_397_, lean_object* v_toPure_398_, lean_object* v_s_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_a_397_);
lean_ctor_set(v___x_400_, 1, v_s_399_);
v___x_401_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5(lean_object* v_toPure_402_, lean_object* v_ref_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__4), 3, 2);
lean_closure_set(v___f_407_, 0, v_a_406_);
lean_closure_set(v___f_407_, 1, v_toPure_402_);
v___x_408_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_408_, 0, lean_box(0));
lean_closure_set(v___x_408_, 1, lean_box(0));
lean_closure_set(v___x_408_, 2, v_ref_403_);
v___x_409_ = lean_apply_2(v_inst_404_, lean_box(0), v___x_408_);
v___x_410_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v___x_409_, v___f_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6(lean_object* v___f_411_, lean_object* v_ref_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_apply_2(v___f_411_, v_a_413_, v_ref_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7(lean_object* v___f_415_, lean_object* v_ref_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_box(0);
v___x_419_ = lean_apply_2(v___f_415_, v___x_418_, v_ref_416_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___closed__0));
v___x_428_ = l_Lean_Name_mkStr4(v___x_421_, v___x_422_, v___x_423_, v___x_427_);
lean_inc(v_x_426_);
v___x_429_ = l_Lean_Syntax_isOfKind(v_x_426_, v___x_428_);
lean_dec(v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_x_426_);
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_froms_431_; lean_object* v_tos_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_froms_431_ = l_Lean_Syntax_getArg(v_x_426_, v___x_424_);
v_tos_432_ = l_Lean_Syntax_getArg(v_x_426_, v___x_425_);
lean_dec(v_x_426_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v_froms_431_);
lean_ctor_set(v___x_433_, 1, v_tos_432_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed(lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9(v___x_435_, v___x_436_, v___x_437_, v___x_438_, v___x_439_, v_x_440_);
lean_dec(v___x_439_);
lean_dec(v___x_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8(lean_object* v___x_442_, lean_object* v_toPure_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_442_);
v___x_446_ = lean_apply_2(v_toPure_443_, lean_box(0), v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(lean_object* v_snd_447_, lean_object* v_a_448_, lean_object* v_inst_449_, lean_object* v_toBind_450_, lean_object* v___f_451_, lean_object* v_____r_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = l_Lean_Syntax_getId(v_snd_447_);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_a_448_);
v___x_456_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_449_, v___x_455_, v___y_453_);
v___x_457_ = lean_apply_4(v_toBind_450_, lean_box(0), lean_box(0), v___x_456_, v___f_451_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(lean_object* v_snd_458_, lean_object* v_a_459_, lean_object* v_inst_460_, lean_object* v_toBind_461_, lean_object* v___f_462_, lean_object* v_____r_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(v_snd_458_, v_a_459_, v_inst_460_, v_toBind_461_, v___f_462_, v_____r_463_, v___y_464_);
lean_dec(v_snd_458_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object* v___f_466_, lean_object* v___y_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_apply_2(v___f_466_, v_a_468_, v___y_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_snd_474_, lean_object* v_a_475_, lean_object* v___x_476_, lean_object* v___y_477_, lean_object* v_toBind_478_, lean_object* v___f_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_6836__overap_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_6836__overap_481_ = l_Lean_Elab_addConstInfo___redArg(v___x_470_, v___x_471_, v___x_472_, v___x_473_, v_snd_474_, v_a_475_, v___x_476_);
v___x_482_ = lean_apply_1(v___x_6836__overap_481_, v___y_477_);
v___x_483_ = lean_apply_4(v_toBind_478_, lean_box(0), lean_box(0), v___x_482_, v___f_479_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object* v___f_484_, lean_object* v___x_485_, lean_object* v___y_486_, lean_object* v___x_487_, lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v_snd_491_, lean_object* v_a_492_, lean_object* v_toBind_493_, lean_object* v___f_494_, lean_object* v_fst_495_, lean_object* v_a_496_){
_start:
{
uint8_t v_enabled_497_; 
v_enabled_497_ = lean_ctor_get_uint8(v_a_496_, sizeof(void*)*3);
if (v_enabled_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v_fst_495_);
lean_dec(v___f_494_);
lean_dec(v_toBind_493_);
lean_dec(v_a_492_);
lean_dec(v_snd_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v___x_488_);
lean_dec_ref(v___x_487_);
v___x_498_ = lean_apply_2(v___f_484_, v___x_485_, v___y_486_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_6851__overap_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___f_484_);
v___x_499_ = lean_box(0);
lean_inc(v_toBind_493_);
lean_inc(v___y_486_);
lean_inc(v_a_492_);
lean_inc_ref(v___x_490_);
lean_inc_ref(v___x_489_);
lean_inc_ref(v___x_488_);
lean_inc_ref(v___x_487_);
v___f_500_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12), 11, 10);
lean_closure_set(v___f_500_, 0, v___x_487_);
lean_closure_set(v___f_500_, 1, v___x_488_);
lean_closure_set(v___f_500_, 2, v___x_489_);
lean_closure_set(v___f_500_, 3, v___x_490_);
lean_closure_set(v___f_500_, 4, v_snd_491_);
lean_closure_set(v___f_500_, 5, v_a_492_);
lean_closure_set(v___f_500_, 6, v___x_499_);
lean_closure_set(v___f_500_, 7, v___y_486_);
lean_closure_set(v___f_500_, 8, v_toBind_493_);
lean_closure_set(v___f_500_, 9, v___f_494_);
v___x_6851__overap_501_ = l_Lean_Elab_addConstInfo___redArg(v___x_487_, v___x_488_, v___x_489_, v___x_490_, v_fst_495_, v_a_492_, v___x_499_);
v___x_502_ = lean_apply_1(v___x_6851__overap_501_, v___y_486_);
v___x_503_ = lean_apply_4(v_toBind_493_, lean_box(0), lean_box(0), v___x_502_, v___f_500_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object* v___f_504_, lean_object* v___x_505_, lean_object* v___y_506_, lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v_snd_511_, lean_object* v_a_512_, lean_object* v_toBind_513_, lean_object* v___f_514_, lean_object* v_fst_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(v___f_504_, v___x_505_, v___y_506_, v___x_507_, v___x_508_, v___x_509_, v___x_510_, v_snd_511_, v_a_512_, v_toBind_513_, v___f_514_, v_fst_515_, v_a_516_);
lean_dec_ref(v_a_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object* v___x_518_, lean_object* v_inst_519_, lean_object* v_snd_520_, lean_object* v_inst_521_, lean_object* v_toBind_522_, lean_object* v___f_523_, lean_object* v___y_524_, lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v_fst_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_531_; lean_object* v_getInfoState_532_; lean_object* v___f_533_; lean_object* v___f_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
lean_inc_ref(v_inst_519_);
v___x_531_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_518_, v_inst_519_);
v_getInfoState_532_ = lean_ctor_get(v_inst_519_, 0);
lean_inc(v_getInfoState_532_);
lean_dec_ref(v_inst_519_);
lean_inc(v_toBind_522_);
lean_inc(v_a_530_);
lean_inc(v_snd_520_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_533_, 0, v_snd_520_);
lean_closure_set(v___f_533_, 1, v_a_530_);
lean_closure_set(v___f_533_, 2, v_inst_521_);
lean_closure_set(v___f_533_, 3, v_toBind_522_);
lean_closure_set(v___f_533_, 4, v___f_523_);
lean_inc(v___y_524_);
lean_inc_ref(v___f_533_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11), 3, 2);
lean_closure_set(v___f_534_, 0, v___f_533_);
lean_closure_set(v___f_534_, 1, v___y_524_);
lean_inc(v_toBind_522_);
v___f_535_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed), 13, 12);
lean_closure_set(v___f_535_, 0, v___f_533_);
lean_closure_set(v___f_535_, 1, v___x_525_);
lean_closure_set(v___f_535_, 2, v___y_524_);
lean_closure_set(v___f_535_, 3, v___x_526_);
lean_closure_set(v___f_535_, 4, v___x_531_);
lean_closure_set(v___f_535_, 5, v___x_527_);
lean_closure_set(v___f_535_, 6, v___x_528_);
lean_closure_set(v___f_535_, 7, v_snd_520_);
lean_closure_set(v___f_535_, 8, v_a_530_);
lean_closure_set(v___f_535_, 9, v_toBind_522_);
lean_closure_set(v___f_535_, 10, v___f_534_);
lean_closure_set(v___f_535_, 11, v_fst_529_);
v___x_536_ = lean_apply_4(v_toBind_522_, lean_box(0), lean_box(0), v_getInfoState_532_, v___f_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v___x_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_toBind_540_, lean_object* v___f_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v___f_551_, lean_object* v___x_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___f_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_6892__overap_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_fst_558_ = lean_ctor_get(v_a_554_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_a_554_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v_a_554_);
lean_inc(v_fst_558_);
lean_inc_ref(v___x_544_);
lean_inc_ref(v___x_543_);
lean_inc(v___y_557_);
lean_inc(v_toBind_540_);
lean_inc(v___x_537_);
v___f_560_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14), 13, 12);
lean_closure_set(v___f_560_, 0, v___x_537_);
lean_closure_set(v___f_560_, 1, v_inst_538_);
lean_closure_set(v___f_560_, 2, v_snd_559_);
lean_closure_set(v___f_560_, 3, v_inst_539_);
lean_closure_set(v___f_560_, 4, v_toBind_540_);
lean_closure_set(v___f_560_, 5, v___f_541_);
lean_closure_set(v___f_560_, 6, v___y_557_);
lean_closure_set(v___f_560_, 7, v___x_542_);
lean_closure_set(v___f_560_, 8, v___x_543_);
lean_closure_set(v___f_560_, 9, v___x_544_);
lean_closure_set(v___f_560_, 10, v___x_545_);
lean_closure_set(v___f_560_, 11, v_fst_558_);
v___x_561_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_537_, v_inst_546_);
v___x_562_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_562_, 0, lean_box(0));
lean_closure_set(v___x_562_, 1, lean_box(0));
lean_closure_set(v___x_562_, 2, lean_box(0));
lean_closure_set(v___x_562_, 3, lean_box(0));
lean_closure_set(v___x_562_, 4, v_inst_547_);
v___x_6892__overap_563_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_543_, v___x_544_, v___x_548_, v___x_549_, v___x_550_, v___f_551_, v___x_561_, v___x_562_, v___x_552_, v_a_553_, v_fst_558_);
v___x_564_ = lean_apply_1(v___x_6892__overap_563_, v___y_557_);
v___x_565_ = lean_apply_4(v_toBind_540_, lean_box(0), lean_box(0), v___x_564_, v___f_560_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object** _args){
lean_object* v___x_566_ = _args[0];
lean_object* v_inst_567_ = _args[1];
lean_object* v_inst_568_ = _args[2];
lean_object* v_toBind_569_ = _args[3];
lean_object* v___f_570_ = _args[4];
lean_object* v___x_571_ = _args[5];
lean_object* v___x_572_ = _args[6];
lean_object* v___x_573_ = _args[7];
lean_object* v___x_574_ = _args[8];
lean_object* v_inst_575_ = _args[9];
lean_object* v_inst_576_ = _args[10];
lean_object* v___x_577_ = _args[11];
lean_object* v___x_578_ = _args[12];
lean_object* v___x_579_ = _args[13];
lean_object* v___f_580_ = _args[14];
lean_object* v___x_581_ = _args[15];
lean_object* v_a_582_ = _args[16];
lean_object* v_a_583_ = _args[17];
lean_object* v_x_584_ = _args[18];
lean_object* v___y_585_ = _args[19];
lean_object* v___y_586_ = _args[20];
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v___x_566_, v_inst_567_, v_inst_568_, v_toBind_569_, v___f_570_, v___x_571_, v___x_572_, v___x_573_, v___x_574_, v_inst_575_, v_inst_576_, v___x_577_, v___x_578_, v___x_579_, v___f_580_, v___x_581_, v_a_582_, v_a_583_, v_x_584_, v___y_585_, v___y_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_froms_588_, lean_object* v_tos_589_, lean_object* v_toPure_590_, lean_object* v___x_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_toBind_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v_inst_598_, lean_object* v_inst_599_, lean_object* v___x_600_, lean_object* v___x_601_, lean_object* v___x_602_, lean_object* v___f_603_, lean_object* v___x_604_, size_t v___x_605_, lean_object* v_ref_606_, lean_object* v___f_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___f_611_; lean_object* v___f_612_; size_t v_sz_613_; lean_object* v___x_6913__overap_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_609_ = l_Array_zip___redArg(v_froms_588_, v_tos_589_);
v___x_610_ = lean_box(0);
v___f_611_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_611_, 0, v___x_610_);
lean_closure_set(v___f_611_, 1, v_toPure_590_);
lean_inc_ref(v___x_595_);
lean_inc(v_toBind_594_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 21, 17);
lean_closure_set(v___f_612_, 0, v___x_591_);
lean_closure_set(v___f_612_, 1, v_inst_592_);
lean_closure_set(v___f_612_, 2, v_inst_593_);
lean_closure_set(v___f_612_, 3, v_toBind_594_);
lean_closure_set(v___f_612_, 4, v___f_611_);
lean_closure_set(v___f_612_, 5, v___x_610_);
lean_closure_set(v___f_612_, 6, v___x_595_);
lean_closure_set(v___f_612_, 7, v___x_596_);
lean_closure_set(v___f_612_, 8, v___x_597_);
lean_closure_set(v___f_612_, 9, v_inst_598_);
lean_closure_set(v___f_612_, 10, v_inst_599_);
lean_closure_set(v___f_612_, 11, v___x_600_);
lean_closure_set(v___f_612_, 12, v___x_601_);
lean_closure_set(v___f_612_, 13, v___x_602_);
lean_closure_set(v___f_612_, 14, v___f_603_);
lean_closure_set(v___f_612_, 15, v___x_604_);
lean_closure_set(v___f_612_, 16, v_a_608_);
v_sz_613_ = lean_array_size(v___x_609_);
v___x_6913__overap_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_595_, v___x_609_, v___f_612_, v_sz_613_, v___x_605_, v___x_610_);
v___x_615_ = lean_apply_1(v___x_6913__overap_614_, v_ref_606_);
v___x_616_ = lean_apply_4(v_toBind_594_, lean_box(0), lean_box(0), v___x_615_, v___f_607_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_froms_617_ = _args[0];
lean_object* v_tos_618_ = _args[1];
lean_object* v_toPure_619_ = _args[2];
lean_object* v___x_620_ = _args[3];
lean_object* v_inst_621_ = _args[4];
lean_object* v_inst_622_ = _args[5];
lean_object* v_toBind_623_ = _args[6];
lean_object* v___x_624_ = _args[7];
lean_object* v___x_625_ = _args[8];
lean_object* v___x_626_ = _args[9];
lean_object* v_inst_627_ = _args[10];
lean_object* v_inst_628_ = _args[11];
lean_object* v___x_629_ = _args[12];
lean_object* v___x_630_ = _args[13];
lean_object* v___x_631_ = _args[14];
lean_object* v___f_632_ = _args[15];
lean_object* v___x_633_ = _args[16];
lean_object* v___x_634_ = _args[17];
lean_object* v_ref_635_ = _args[18];
lean_object* v___f_636_ = _args[19];
lean_object* v_a_637_ = _args[20];
_start:
{
size_t v___x_7767__boxed_638_; lean_object* v_res_639_; 
v___x_7767__boxed_638_ = lean_unbox_usize(v___x_634_);
lean_dec(v___x_634_);
v_res_639_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_froms_617_, v_tos_618_, v_toPure_619_, v___x_620_, v_inst_621_, v_inst_622_, v_toBind_623_, v___x_624_, v___x_625_, v___x_626_, v_inst_627_, v_inst_628_, v___x_629_, v___x_630_, v___x_631_, v___f_632_, v___x_633_, v___x_7767__boxed_638_, v_ref_635_, v___f_636_, v_a_637_);
lean_dec_ref(v_tos_618_);
lean_dec_ref(v_froms_617_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(uint8_t v___x_640_, uint8_t v___x_641_, lean_object* v_x1_642_, lean_object* v_x2_643_){
_start:
{
lean_object* v_fst_644_; uint8_t v___x_645_; 
v_fst_644_ = lean_ctor_get(v_x1_642_, 0);
v___x_645_ = lean_unbox(v_fst_644_);
if (v___x_645_ == 0)
{
lean_object* v_snd_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_x2_643_);
v_snd_646_ = lean_ctor_get(v_x1_642_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x1_642_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_x1_642_, 0);
lean_dec(v_unused_655_);
v___x_648_ = v_x1_642_;
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snd_646_);
lean_dec(v_x1_642_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_654_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_650_ = lean_box(v___x_640_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_snd_646_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
v_snd_656_ = lean_ctor_get(v_x1_642_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x1_642_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_x1_642_, 0);
lean_dec(v_unused_666_);
v___x_658_ = v_x1_642_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_dec(v_x1_642_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = lean_array_push(v_snd_656_, v_x2_643_);
v___x_661_ = lean_box(v___x_641_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_660_);
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_660_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v_x1_669_, lean_object* v_x2_670_){
_start:
{
uint8_t v___x_7811__boxed_671_; uint8_t v___x_7812__boxed_672_; lean_object* v_res_673_; 
v___x_7811__boxed_671_ = lean_unbox(v___x_667_);
v___x_7812__boxed_672_ = lean_unbox(v___x_668_);
v_res_673_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v___x_7811__boxed_671_, v___x_7812__boxed_672_, v_x1_669_, v_x2_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(lean_object* v_ids_674_, lean_object* v___f_675_, lean_object* v_a_676_, lean_object* v_inst_677_, lean_object* v_ref_678_, lean_object* v_toBind_679_, lean_object* v___f_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_682_; size_t v_sz_683_; size_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_682_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_683_ = lean_array_size(v_ids_674_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_682_, v___f_675_, v_sz_683_, v___x_684_, v_ids_674_);
v___x_686_ = lean_array_to_list(v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_a_676_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_677_, v___x_687_, v_ref_678_);
v___x_689_ = lean_apply_4(v_toBind_679_, lean_box(0), lean_box(0), v___x_688_, v___f_680_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v___x_690_, lean_object* v_toPure_691_, lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v___y_698_, lean_object* v_toBind_699_, lean_object* v___f_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_enabled_702_; 
v_enabled_702_ = lean_ctor_get_uint8(v_a_701_, sizeof(void*)*3);
if (v_enabled_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v___f_700_);
lean_dec(v_toBind_699_);
lean_dec(v___y_698_);
lean_dec(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_692_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_690_);
v___x_704_ = lean_apply_2(v_toPure_691_, lean_box(0), v___x_703_);
return v___x_704_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_6958__overap_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_toPure_691_);
v___x_705_ = lean_box(0);
v___x_6958__overap_706_ = l_Lean_Elab_addConstInfo___redArg(v___x_692_, v___x_693_, v___x_694_, v___x_695_, v_a_696_, v_a_697_, v___x_705_);
v___x_707_ = lean_apply_1(v___x_6958__overap_706_, v___y_698_);
v___x_708_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_707_, v___f_700_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v___x_709_, lean_object* v_toPure_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v___y_717_, lean_object* v_toBind_718_, lean_object* v___f_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v___x_709_, v_toPure_710_, v___x_711_, v___x_712_, v___x_713_, v___x_714_, v_a_715_, v_a_716_, v___y_717_, v_toBind_718_, v___f_719_, v_a_720_);
lean_dec_ref(v_a_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object* v___x_722_, lean_object* v_inst_723_, lean_object* v___x_724_, lean_object* v_toPure_725_, lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v_a_729_, lean_object* v___y_730_, lean_object* v_toBind_731_, lean_object* v___f_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; lean_object* v_getInfoState_735_; lean_object* v___f_736_; lean_object* v___x_737_; 
lean_inc_ref(v_inst_723_);
v___x_734_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_722_, v_inst_723_);
v_getInfoState_735_ = lean_ctor_get(v_inst_723_, 0);
lean_inc(v_getInfoState_735_);
lean_dec_ref(v_inst_723_);
lean_inc(v_toBind_731_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 12, 11);
lean_closure_set(v___f_736_, 0, v___x_724_);
lean_closure_set(v___f_736_, 1, v_toPure_725_);
lean_closure_set(v___f_736_, 2, v___x_726_);
lean_closure_set(v___f_736_, 3, v___x_734_);
lean_closure_set(v___f_736_, 4, v___x_727_);
lean_closure_set(v___f_736_, 5, v___x_728_);
lean_closure_set(v___f_736_, 6, v_a_729_);
lean_closure_set(v___f_736_, 7, v_a_733_);
lean_closure_set(v___f_736_, 8, v___y_730_);
lean_closure_set(v___f_736_, 9, v_toBind_731_);
lean_closure_set(v___f_736_, 10, v___f_732_);
v___x_737_ = lean_apply_4(v_toBind_731_, lean_box(0), lean_box(0), v_getInfoState_735_, v___f_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v___x_738_, lean_object* v_inst_739_, lean_object* v___x_740_, lean_object* v_toPure_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_toBind_745_, lean_object* v___f_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v___x_749_, lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v___f_752_, lean_object* v___x_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_6991__overap_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc(v_toBind_745_);
lean_inc(v___y_758_);
lean_inc(v_a_755_);
lean_inc_ref(v___x_743_);
lean_inc_ref(v___x_742_);
lean_inc(v___x_738_);
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18), 12, 11);
lean_closure_set(v___f_759_, 0, v___x_738_);
lean_closure_set(v___f_759_, 1, v_inst_739_);
lean_closure_set(v___f_759_, 2, v___x_740_);
lean_closure_set(v___f_759_, 3, v_toPure_741_);
lean_closure_set(v___f_759_, 4, v___x_742_);
lean_closure_set(v___f_759_, 5, v___x_743_);
lean_closure_set(v___f_759_, 6, v___x_744_);
lean_closure_set(v___f_759_, 7, v_a_755_);
lean_closure_set(v___f_759_, 8, v___y_758_);
lean_closure_set(v___f_759_, 9, v_toBind_745_);
lean_closure_set(v___f_759_, 10, v___f_746_);
v___x_760_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_738_, v_inst_747_);
v___x_761_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_761_, 0, lean_box(0));
lean_closure_set(v___x_761_, 1, lean_box(0));
lean_closure_set(v___x_761_, 2, lean_box(0));
lean_closure_set(v___x_761_, 3, lean_box(0));
lean_closure_set(v___x_761_, 4, v_inst_748_);
v___x_6991__overap_762_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_742_, v___x_743_, v___x_749_, v___x_750_, v___x_751_, v___f_752_, v___x_760_, v___x_761_, v___x_753_, v_a_754_, v_a_755_);
v___x_763_ = lean_apply_1(v___x_6991__overap_762_, v___y_758_);
v___x_764_ = lean_apply_4(v_toBind_745_, lean_box(0), lean_box(0), v___x_763_, v___f_759_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object** _args){
lean_object* v___x_765_ = _args[0];
lean_object* v_inst_766_ = _args[1];
lean_object* v___x_767_ = _args[2];
lean_object* v_toPure_768_ = _args[3];
lean_object* v___x_769_ = _args[4];
lean_object* v___x_770_ = _args[5];
lean_object* v___x_771_ = _args[6];
lean_object* v_toBind_772_ = _args[7];
lean_object* v___f_773_ = _args[8];
lean_object* v_inst_774_ = _args[9];
lean_object* v_inst_775_ = _args[10];
lean_object* v___x_776_ = _args[11];
lean_object* v___x_777_ = _args[12];
lean_object* v___x_778_ = _args[13];
lean_object* v___f_779_ = _args[14];
lean_object* v___x_780_ = _args[15];
lean_object* v_a_781_ = _args[16];
lean_object* v_a_782_ = _args[17];
lean_object* v_x_783_ = _args[18];
lean_object* v___y_784_ = _args[19];
lean_object* v___y_785_ = _args[20];
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v___x_765_, v_inst_766_, v___x_767_, v_toPure_768_, v___x_769_, v___x_770_, v___x_771_, v_toBind_772_, v___f_773_, v_inst_774_, v_inst_775_, v___x_776_, v___x_777_, v___x_778_, v___f_779_, v___x_780_, v_a_781_, v_a_782_, v_x_783_, v___y_784_, v___y_785_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v_toPure_787_, lean_object* v___x_788_, lean_object* v_inst_789_, lean_object* v___x_790_, lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v_toBind_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v___f_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_ids_802_, lean_object* v_ref_803_, lean_object* v___f_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; lean_object* v___f_807_; lean_object* v___f_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_7010__overap_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_806_ = lean_box(0);
lean_inc(v_toPure_787_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_807_, 0, v___x_806_);
lean_closure_set(v___f_807_, 1, v_toPure_787_);
lean_inc(v_toBind_793_);
lean_inc_ref(v___x_790_);
v___f_808_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 21, 17);
lean_closure_set(v___f_808_, 0, v___x_788_);
lean_closure_set(v___f_808_, 1, v_inst_789_);
lean_closure_set(v___f_808_, 2, v___x_806_);
lean_closure_set(v___f_808_, 3, v_toPure_787_);
lean_closure_set(v___f_808_, 4, v___x_790_);
lean_closure_set(v___f_808_, 5, v___x_791_);
lean_closure_set(v___f_808_, 6, v___x_792_);
lean_closure_set(v___f_808_, 7, v_toBind_793_);
lean_closure_set(v___f_808_, 8, v___f_807_);
lean_closure_set(v___f_808_, 9, v_inst_794_);
lean_closure_set(v___f_808_, 10, v_inst_795_);
lean_closure_set(v___f_808_, 11, v___x_796_);
lean_closure_set(v___f_808_, 12, v___x_797_);
lean_closure_set(v___f_808_, 13, v___x_798_);
lean_closure_set(v___f_808_, 14, v___f_799_);
lean_closure_set(v___f_808_, 15, v___x_800_);
lean_closure_set(v___f_808_, 16, v_a_801_);
v_sz_809_ = lean_array_size(v_ids_802_);
v___x_810_ = ((size_t)0ULL);
v___x_7010__overap_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_790_, v_ids_802_, v___f_808_, v_sz_809_, v___x_810_, v___x_806_);
v___x_812_ = lean_apply_1(v___x_7010__overap_811_, v_ref_803_);
v___x_813_ = lean_apply_4(v_toBind_793_, lean_box(0), lean_box(0), v___x_812_, v___f_804_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object** _args){
lean_object* v_toPure_814_ = _args[0];
lean_object* v___x_815_ = _args[1];
lean_object* v_inst_816_ = _args[2];
lean_object* v___x_817_ = _args[3];
lean_object* v___x_818_ = _args[4];
lean_object* v___x_819_ = _args[5];
lean_object* v_toBind_820_ = _args[6];
lean_object* v_inst_821_ = _args[7];
lean_object* v_inst_822_ = _args[8];
lean_object* v___x_823_ = _args[9];
lean_object* v___x_824_ = _args[10];
lean_object* v___x_825_ = _args[11];
lean_object* v___f_826_ = _args[12];
lean_object* v___x_827_ = _args[13];
lean_object* v_a_828_ = _args[14];
lean_object* v_ids_829_ = _args[15];
lean_object* v_ref_830_ = _args[16];
lean_object* v___f_831_ = _args[17];
lean_object* v_a_832_ = _args[18];
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v_toPure_814_, v___x_815_, v_inst_816_, v___x_817_, v___x_818_, v___x_819_, v_toBind_820_, v_inst_821_, v_inst_822_, v___x_823_, v___x_824_, v___x_825_, v___f_826_, v___x_827_, v_a_828_, v_ids_829_, v_ref_830_, v___f_831_, v_a_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_ids_834_, lean_object* v___f_835_, lean_object* v_inst_836_, lean_object* v_ref_837_, lean_object* v_toBind_838_, lean_object* v___f_839_, lean_object* v_toPure_840_, lean_object* v___x_841_, lean_object* v_inst_842_, lean_object* v___x_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___f_851_, lean_object* v___x_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_7030__overap_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_inc(v_toBind_838_);
lean_inc(v_ref_837_);
lean_inc(v_inst_836_);
lean_inc(v_a_853_);
lean_inc_ref(v_ids_834_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19), 8, 7);
lean_closure_set(v___f_854_, 0, v_ids_834_);
lean_closure_set(v___f_854_, 1, v___f_835_);
lean_closure_set(v___f_854_, 2, v_a_853_);
lean_closure_set(v___f_854_, 3, v_inst_836_);
lean_closure_set(v___f_854_, 4, v_ref_837_);
lean_closure_set(v___f_854_, 5, v_toBind_838_);
lean_closure_set(v___f_854_, 6, v___f_839_);
lean_inc(v_ref_837_);
lean_inc(v_a_853_);
lean_inc(v_toBind_838_);
lean_inc_ref(v___x_844_);
lean_inc_ref(v___x_843_);
lean_inc(v___x_841_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 19, 18);
lean_closure_set(v___f_855_, 0, v_toPure_840_);
lean_closure_set(v___f_855_, 1, v___x_841_);
lean_closure_set(v___f_855_, 2, v_inst_842_);
lean_closure_set(v___f_855_, 3, v___x_843_);
lean_closure_set(v___f_855_, 4, v___x_844_);
lean_closure_set(v___f_855_, 5, v___x_845_);
lean_closure_set(v___f_855_, 6, v_toBind_838_);
lean_closure_set(v___f_855_, 7, v_inst_846_);
lean_closure_set(v___f_855_, 8, v_inst_847_);
lean_closure_set(v___f_855_, 9, v___x_848_);
lean_closure_set(v___f_855_, 10, v___x_849_);
lean_closure_set(v___f_855_, 11, v___x_850_);
lean_closure_set(v___f_855_, 12, v___f_851_);
lean_closure_set(v___f_855_, 13, v___x_852_);
lean_closure_set(v___f_855_, 14, v_a_853_);
lean_closure_set(v___f_855_, 15, v_ids_834_);
lean_closure_set(v___f_855_, 16, v_ref_837_);
lean_closure_set(v___f_855_, 17, v___f_854_);
v___f_856_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_856_, 0, v_inst_836_);
lean_closure_set(v___f_856_, 1, v___x_841_);
v___x_7030__overap_857_ = l_Lean_activateScoped___redArg(v___x_843_, v___x_844_, v___f_856_, v_a_853_);
v___x_858_ = lean_apply_1(v___x_7030__overap_857_, v_ref_837_);
v___x_859_ = lean_apply_4(v_toBind_838_, lean_box(0), lean_box(0), v___x_858_, v___f_855_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_ids_860_ = _args[0];
lean_object* v___f_861_ = _args[1];
lean_object* v_inst_862_ = _args[2];
lean_object* v_ref_863_ = _args[3];
lean_object* v_toBind_864_ = _args[4];
lean_object* v___f_865_ = _args[5];
lean_object* v_toPure_866_ = _args[6];
lean_object* v___x_867_ = _args[7];
lean_object* v_inst_868_ = _args[8];
lean_object* v___x_869_ = _args[9];
lean_object* v___x_870_ = _args[10];
lean_object* v___x_871_ = _args[11];
lean_object* v_inst_872_ = _args[12];
lean_object* v_inst_873_ = _args[13];
lean_object* v___x_874_ = _args[14];
lean_object* v___x_875_ = _args[15];
lean_object* v___x_876_ = _args[16];
lean_object* v___f_877_ = _args[17];
lean_object* v___x_878_ = _args[18];
lean_object* v_a_879_ = _args[19];
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_ids_860_, v___f_861_, v_inst_862_, v_ref_863_, v_toBind_864_, v___f_865_, v_toPure_866_, v___x_867_, v_inst_868_, v___x_869_, v___x_870_, v___x_871_, v_inst_872_, v_inst_873_, v___x_874_, v___x_875_, v___x_876_, v___f_877_, v___x_878_, v_a_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_inst_883_, lean_object* v_toBind_884_, lean_object* v___f_885_, lean_object* v_____r_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_888_ = l_Lean_TSyntax_getId(v_a_881_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_a_882_);
v___x_890_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_883_, v___x_889_, v___y_887_);
v___x_891_ = lean_apply_4(v_toBind_884_, lean_box(0), lean_box(0), v___x_890_, v___f_885_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_inst_894_, lean_object* v_toBind_895_, lean_object* v___f_896_, lean_object* v_____r_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v_a_892_, v_a_893_, v_inst_894_, v_toBind_895_, v___f_896_, v_____r_897_, v___y_898_);
lean_dec(v_a_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v___f_900_, lean_object* v___x_901_, lean_object* v___y_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_toBind_909_, lean_object* v___f_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_enabled_912_; 
v_enabled_912_ = lean_ctor_get_uint8(v_a_911_, sizeof(void*)*3);
if (v_enabled_912_ == 0)
{
lean_object* v___x_913_; 
lean_dec(v___f_910_);
lean_dec(v_toBind_909_);
lean_dec(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v___x_906_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
v___x_913_ = lean_apply_2(v___f_900_, v___x_901_, v___y_902_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_7059__overap_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v___f_900_);
v___x_914_ = lean_box(0);
v___x_7059__overap_915_ = l_Lean_Elab_addConstInfo___redArg(v___x_903_, v___x_904_, v___x_905_, v___x_906_, v_a_907_, v_a_908_, v___x_914_);
v___x_916_ = lean_apply_1(v___x_7059__overap_915_, v___y_902_);
v___x_917_ = lean_apply_4(v_toBind_909_, lean_box(0), lean_box(0), v___x_916_, v___f_910_);
return v___x_917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed(lean_object* v___f_918_, lean_object* v___x_919_, lean_object* v___y_920_, lean_object* v___x_921_, lean_object* v___x_922_, lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_toBind_927_, lean_object* v___f_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(v___f_918_, v___x_919_, v___y_920_, v___x_921_, v___x_922_, v___x_923_, v___x_924_, v_a_925_, v_a_926_, v_toBind_927_, v___f_928_, v_a_929_);
lean_dec_ref(v_a_929_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v___x_931_, lean_object* v_inst_932_, lean_object* v_a_933_, lean_object* v_inst_934_, lean_object* v_toBind_935_, lean_object* v___f_936_, lean_object* v___y_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_943_; lean_object* v_getInfoState_944_; lean_object* v___f_945_; lean_object* v___f_946_; lean_object* v___f_947_; lean_object* v___x_948_; 
lean_inc_ref(v_inst_932_);
v___x_943_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_931_, v_inst_932_);
v_getInfoState_944_ = lean_ctor_get(v_inst_932_, 0);
lean_inc(v_getInfoState_944_);
lean_dec_ref(v_inst_932_);
lean_inc(v_toBind_935_);
lean_inc(v_a_942_);
lean_inc(v_a_933_);
v___f_945_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 7, 5);
lean_closure_set(v___f_945_, 0, v_a_933_);
lean_closure_set(v___f_945_, 1, v_a_942_);
lean_closure_set(v___f_945_, 2, v_inst_934_);
lean_closure_set(v___f_945_, 3, v_toBind_935_);
lean_closure_set(v___f_945_, 4, v___f_936_);
lean_inc(v___y_937_);
lean_inc_ref(v___f_945_);
v___f_946_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11), 3, 2);
lean_closure_set(v___f_946_, 0, v___f_945_);
lean_closure_set(v___f_946_, 1, v___y_937_);
lean_inc(v_toBind_935_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25___boxed), 12, 11);
lean_closure_set(v___f_947_, 0, v___f_945_);
lean_closure_set(v___f_947_, 1, v___x_938_);
lean_closure_set(v___f_947_, 2, v___y_937_);
lean_closure_set(v___f_947_, 3, v___x_939_);
lean_closure_set(v___f_947_, 4, v___x_943_);
lean_closure_set(v___f_947_, 5, v___x_940_);
lean_closure_set(v___f_947_, 6, v___x_941_);
lean_closure_set(v___f_947_, 7, v_a_933_);
lean_closure_set(v___f_947_, 8, v_a_942_);
lean_closure_set(v___f_947_, 9, v_toBind_935_);
lean_closure_set(v___f_947_, 10, v___f_946_);
v___x_948_ = lean_apply_4(v_toBind_935_, lean_box(0), lean_box(0), v_getInfoState_944_, v___f_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v___x_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_toBind_952_, lean_object* v___f_953_, lean_object* v___x_954_, lean_object* v___x_955_, lean_object* v___x_956_, lean_object* v___x_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v___f_963_, lean_object* v___x_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_7096__overap_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref(v___x_956_);
lean_inc_ref(v___x_955_);
lean_inc(v___y_969_);
lean_inc(v_toBind_952_);
lean_inc(v_a_966_);
lean_inc(v___x_949_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24), 12, 11);
lean_closure_set(v___f_970_, 0, v___x_949_);
lean_closure_set(v___f_970_, 1, v_inst_950_);
lean_closure_set(v___f_970_, 2, v_a_966_);
lean_closure_set(v___f_970_, 3, v_inst_951_);
lean_closure_set(v___f_970_, 4, v_toBind_952_);
lean_closure_set(v___f_970_, 5, v___f_953_);
lean_closure_set(v___f_970_, 6, v___y_969_);
lean_closure_set(v___f_970_, 7, v___x_954_);
lean_closure_set(v___f_970_, 8, v___x_955_);
lean_closure_set(v___f_970_, 9, v___x_956_);
lean_closure_set(v___f_970_, 10, v___x_957_);
v___x_971_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_949_, v_inst_958_);
v___x_972_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_972_, 0, lean_box(0));
lean_closure_set(v___x_972_, 1, lean_box(0));
lean_closure_set(v___x_972_, 2, lean_box(0));
lean_closure_set(v___x_972_, 3, lean_box(0));
lean_closure_set(v___x_972_, 4, v_inst_959_);
v___x_7096__overap_973_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_955_, v___x_956_, v___x_960_, v___x_961_, v___x_962_, v___f_963_, v___x_971_, v___x_972_, v___x_964_, v_a_965_, v_a_966_);
v___x_974_ = lean_apply_1(v___x_7096__overap_973_, v___y_969_);
v___x_975_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v___x_974_, v___f_970_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object** _args){
lean_object* v___x_976_ = _args[0];
lean_object* v_inst_977_ = _args[1];
lean_object* v_inst_978_ = _args[2];
lean_object* v_toBind_979_ = _args[3];
lean_object* v___f_980_ = _args[4];
lean_object* v___x_981_ = _args[5];
lean_object* v___x_982_ = _args[6];
lean_object* v___x_983_ = _args[7];
lean_object* v___x_984_ = _args[8];
lean_object* v_inst_985_ = _args[9];
lean_object* v_inst_986_ = _args[10];
lean_object* v___x_987_ = _args[11];
lean_object* v___x_988_ = _args[12];
lean_object* v___x_989_ = _args[13];
lean_object* v___f_990_ = _args[14];
lean_object* v___x_991_ = _args[15];
lean_object* v_a_992_ = _args[16];
lean_object* v_a_993_ = _args[17];
lean_object* v_x_994_ = _args[18];
lean_object* v___y_995_ = _args[19];
lean_object* v___y_996_ = _args[20];
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v___x_976_, v_inst_977_, v_inst_978_, v_toBind_979_, v___f_980_, v___x_981_, v___x_982_, v___x_983_, v___x_984_, v_inst_985_, v_inst_986_, v___x_987_, v___x_988_, v___x_989_, v___f_990_, v___x_991_, v_a_992_, v_a_993_, v_x_994_, v___y_995_, v___y_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_toPure_998_, lean_object* v___x_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_toBind_1002_, lean_object* v___x_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v___x_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v___f_1011_, lean_object* v___x_1012_, lean_object* v_ids_1013_, lean_object* v_ref_1014_, lean_object* v___f_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; size_t v_sz_1020_; size_t v___x_1021_; lean_object* v___x_7116__overap_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1017_ = lean_box(0);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1018_, 0, v___x_1017_);
lean_closure_set(v___f_1018_, 1, v_toPure_998_);
lean_inc_ref(v___x_1003_);
lean_inc(v_toBind_1002_);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 21, 17);
lean_closure_set(v___f_1019_, 0, v___x_999_);
lean_closure_set(v___f_1019_, 1, v_inst_1000_);
lean_closure_set(v___f_1019_, 2, v_inst_1001_);
lean_closure_set(v___f_1019_, 3, v_toBind_1002_);
lean_closure_set(v___f_1019_, 4, v___f_1018_);
lean_closure_set(v___f_1019_, 5, v___x_1017_);
lean_closure_set(v___f_1019_, 6, v___x_1003_);
lean_closure_set(v___f_1019_, 7, v___x_1004_);
lean_closure_set(v___f_1019_, 8, v___x_1005_);
lean_closure_set(v___f_1019_, 9, v_inst_1006_);
lean_closure_set(v___f_1019_, 10, v_inst_1007_);
lean_closure_set(v___f_1019_, 11, v___x_1008_);
lean_closure_set(v___f_1019_, 12, v___x_1009_);
lean_closure_set(v___f_1019_, 13, v___x_1010_);
lean_closure_set(v___f_1019_, 14, v___f_1011_);
lean_closure_set(v___f_1019_, 15, v___x_1012_);
lean_closure_set(v___f_1019_, 16, v_a_1016_);
v_sz_1020_ = lean_array_size(v_ids_1013_);
v___x_1021_ = ((size_t)0ULL);
v___x_7116__overap_1022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1003_, v_ids_1013_, v___f_1019_, v_sz_1020_, v___x_1021_, v___x_1017_);
v___x_1023_ = lean_apply_1(v___x_7116__overap_1022_, v_ref_1014_);
v___x_1024_ = lean_apply_4(v_toBind_1002_, lean_box(0), lean_box(0), v___x_1023_, v___f_1015_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object** _args){
lean_object* v_toPure_1025_ = _args[0];
lean_object* v___x_1026_ = _args[1];
lean_object* v_inst_1027_ = _args[2];
lean_object* v_inst_1028_ = _args[3];
lean_object* v_toBind_1029_ = _args[4];
lean_object* v___x_1030_ = _args[5];
lean_object* v___x_1031_ = _args[6];
lean_object* v___x_1032_ = _args[7];
lean_object* v_inst_1033_ = _args[8];
lean_object* v_inst_1034_ = _args[9];
lean_object* v___x_1035_ = _args[10];
lean_object* v___x_1036_ = _args[11];
lean_object* v___x_1037_ = _args[12];
lean_object* v___f_1038_ = _args[13];
lean_object* v___x_1039_ = _args[14];
lean_object* v_ids_1040_ = _args[15];
lean_object* v_ref_1041_ = _args[16];
lean_object* v___f_1042_ = _args[17];
lean_object* v_a_1043_ = _args[18];
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_toPure_1025_, v___x_1026_, v_inst_1027_, v_inst_1028_, v_toBind_1029_, v___x_1030_, v___x_1031_, v___x_1032_, v_inst_1033_, v_inst_1034_, v___x_1035_, v___x_1036_, v___x_1037_, v___f_1038_, v___x_1039_, v_ids_1040_, v_ref_1041_, v___f_1042_, v_a_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v_inst_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_toBind_1049_, lean_object* v___f_1050_, lean_object* v_a_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_7136__overap_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___f_1055_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1055_, 0, v_inst_1045_);
lean_closure_set(v___f_1055_, 1, v___x_1046_);
v___x_7136__overap_1056_ = l_Lean_activateScoped___redArg(v___x_1047_, v___x_1048_, v___f_1055_, v_a_1051_);
v___x_1057_ = lean_apply_1(v___x_7136__overap_1056_, v___y_1054_);
v___x_1058_ = lean_apply_4(v_toBind_1049_, lean_box(0), lean_box(0), v___x_1057_, v___f_1050_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v___x_1059_, lean_object* v___f_1060_, lean_object* v___x_1061_, lean_object* v___y_1062_, lean_object* v_toBind_1063_, lean_object* v___f_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_7143__overap_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_7143__overap_1066_ = l_List_forIn_x27_loop___redArg(v___x_1059_, v___f_1060_, v_a_1065_, v___x_1061_);
v___x_1067_ = lean_apply_1(v___x_7143__overap_1066_, v___y_1062_);
v___x_1068_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1067_, v___f_1064_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v___x_1074_, lean_object* v_toBind_1075_, lean_object* v___f_1076_, lean_object* v___x_1077_, lean_object* v___f_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_a_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v_getEnv_1087_; lean_object* v_modifyEnv_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1111_; 
lean_inc(v_inst_1072_);
v___x_1086_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1071_, v_inst_1072_);
v_getEnv_1087_ = lean_ctor_get(v_inst_1073_, 0);
v_modifyEnv_1088_ = lean_ctor_get(v_inst_1073_, 1);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_inst_1073_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1090_ = v_inst_1073_;
v_isShared_1091_ = v_isSharedCheck_1111_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_modifyEnv_1088_);
lean_inc(v_getEnv_1087_);
lean_dec(v_inst_1073_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1111_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1093_, 0, v_modifyEnv_1088_);
lean_closure_set(v___f_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1094_, 0, lean_box(0));
lean_closure_set(v___x_1094_, 1, lean_box(0));
lean_closure_set(v___x_1094_, 2, lean_box(0));
lean_closure_set(v___x_1094_, 3, lean_box(0));
lean_closure_set(v___x_1094_, 4, v_getEnv_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v___f_1093_);
lean_ctor_set(v___x_1090_, 0, v___x_1094_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___f_1093_);
v___x_1096_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_7173__overap_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc(v_toBind_1075_);
lean_inc_ref(v___x_1096_);
lean_inc_ref(v___x_1074_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32), 10, 6);
lean_closure_set(v___f_1097_, 0, v_inst_1072_);
lean_closure_set(v___f_1097_, 1, v___x_1092_);
lean_closure_set(v___f_1097_, 2, v___x_1074_);
lean_closure_set(v___f_1097_, 3, v___x_1096_);
lean_closure_set(v___f_1097_, 4, v_toBind_1075_);
lean_closure_set(v___f_1097_, 5, v___f_1076_);
lean_inc(v_toBind_1075_);
lean_inc(v___y_1085_);
lean_inc_ref(v___x_1074_);
v___f_1098_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29), 7, 6);
lean_closure_set(v___f_1098_, 0, v___x_1074_);
lean_closure_set(v___f_1098_, 1, v___f_1097_);
lean_closure_set(v___f_1098_, 2, v___x_1077_);
lean_closure_set(v___f_1098_, 3, v___y_1085_);
lean_closure_set(v___f_1098_, 4, v_toBind_1075_);
lean_closure_set(v___f_1098_, 5, v___f_1078_);
lean_inc_ref(v_inst_1079_);
v___f_1099_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1099_, 0, v_inst_1079_);
v___f_1100_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1100_, 0, v_inst_1079_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___f_1099_);
lean_ctor_set(v___x_1101_, 1, v___f_1100_);
v___f_1102_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1103_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1092_, v___f_1102_, v_inst_1080_);
v___f_1104_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1104_, 0, v_inst_1081_);
lean_closure_set(v___f_1104_, 1, v___x_1092_);
lean_inc_ref(v___x_1074_);
v___x_1105_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1104_, v___x_1074_);
v___x_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
lean_ctor_set(v___x_1106_, 1, v___x_1103_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
v___x_7173__overap_1107_ = l_Lean_resolveNamespace___redArg(v___x_1074_, v___x_1086_, v___x_1096_, v___x_1106_, v_a_1082_);
v___x_1108_ = lean_apply_1(v___x_7173__overap_1107_, v___y_1085_);
v___x_1109_ = lean_apply_4(v_toBind_1075_, lean_box(0), lean_box(0), v___x_1108_, v___f_1098_);
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v_inst_1112_, lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v___x_1115_, lean_object* v_a_1116_, lean_object* v___y_1117_, lean_object* v_toBind_1118_, lean_object* v___f_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___f_1121_; lean_object* v___x_7191__overap_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___f_1121_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1121_, 0, v_inst_1112_);
lean_closure_set(v___f_1121_, 1, v___x_1113_);
v___x_7191__overap_1122_ = l_Lean_activateScoped___redArg(v___x_1114_, v___x_1115_, v___f_1121_, v_a_1116_);
v___x_1123_ = lean_apply_1(v___x_7191__overap_1122_, v___y_1117_);
v___x_1124_ = lean_apply_4(v_toBind_1118_, lean_box(0), lean_box(0), v___x_1123_, v___f_1119_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_inst_1125_, lean_object* v___x_1126_, lean_object* v___x_1127_, lean_object* v___x_1128_, lean_object* v_toBind_1129_, lean_object* v___f_1130_, lean_object* v___x_1131_, lean_object* v_a_1132_, lean_object* v_x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___f_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_toBind_1129_);
lean_inc(v___y_1135_);
lean_inc(v_a_1132_);
lean_inc(v_inst_1125_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35), 9, 8);
lean_closure_set(v___f_1136_, 0, v_inst_1125_);
lean_closure_set(v___f_1136_, 1, v___x_1126_);
lean_closure_set(v___f_1136_, 2, v___x_1127_);
lean_closure_set(v___f_1136_, 3, v___x_1128_);
lean_closure_set(v___f_1136_, 4, v_a_1132_);
lean_closure_set(v___f_1136_, 5, v___y_1135_);
lean_closure_set(v___f_1136_, 6, v_toBind_1129_);
lean_closure_set(v___f_1136_, 7, v___f_1130_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1132_);
lean_ctor_set(v___x_1137_, 1, v___x_1131_);
v___x_1138_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1125_, v___x_1137_, v___y_1135_);
v___x_1139_ = lean_apply_4(v_toBind_1129_, lean_box(0), lean_box(0), v___x_1138_, v___f_1136_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v___x_1143_, lean_object* v_toBind_1144_, lean_object* v___f_1145_, lean_object* v___x_1146_, lean_object* v___x_1147_, lean_object* v___f_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_a_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v_getEnv_1157_; lean_object* v_modifyEnv_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1181_; 
lean_inc(v_inst_1141_);
v___x_1156_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1140_, v_inst_1141_);
v_getEnv_1157_ = lean_ctor_get(v_inst_1142_, 0);
v_modifyEnv_1158_ = lean_ctor_get(v_inst_1142_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_inst_1142_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1160_ = v_inst_1142_;
v_isShared_1161_ = v_isSharedCheck_1181_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_modifyEnv_1158_);
lean_inc(v_getEnv_1157_);
lean_dec(v_inst_1142_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1181_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1162_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1163_, 0, v_modifyEnv_1158_);
lean_closure_set(v___f_1163_, 1, v___x_1162_);
v___x_1164_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1164_, 0, lean_box(0));
lean_closure_set(v___x_1164_, 1, lean_box(0));
lean_closure_set(v___x_1164_, 2, lean_box(0));
lean_closure_set(v___x_1164_, 3, lean_box(0));
lean_closure_set(v___x_1164_, 4, v_getEnv_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___f_1163_);
lean_ctor_set(v___x_1160_, 0, v___x_1164_);
v___x_1166_ = v___x_1160_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___f_1163_);
v___x_1166_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_7242__overap_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_inc(v_toBind_1144_);
lean_inc_ref(v___x_1166_);
lean_inc_ref(v___x_1143_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31), 11, 7);
lean_closure_set(v___f_1167_, 0, v_inst_1141_);
lean_closure_set(v___f_1167_, 1, v___x_1162_);
lean_closure_set(v___f_1167_, 2, v___x_1143_);
lean_closure_set(v___f_1167_, 3, v___x_1166_);
lean_closure_set(v___f_1167_, 4, v_toBind_1144_);
lean_closure_set(v___f_1167_, 5, v___f_1145_);
lean_closure_set(v___f_1167_, 6, v___x_1146_);
lean_inc(v_toBind_1144_);
lean_inc(v___y_1155_);
lean_inc_ref(v___x_1143_);
v___f_1168_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29), 7, 6);
lean_closure_set(v___f_1168_, 0, v___x_1143_);
lean_closure_set(v___f_1168_, 1, v___f_1167_);
lean_closure_set(v___f_1168_, 2, v___x_1147_);
lean_closure_set(v___f_1168_, 3, v___y_1155_);
lean_closure_set(v___f_1168_, 4, v_toBind_1144_);
lean_closure_set(v___f_1168_, 5, v___f_1148_);
lean_inc_ref(v_inst_1149_);
v___f_1169_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1169_, 0, v_inst_1149_);
v___f_1170_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1170_, 0, v_inst_1149_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___f_1169_);
lean_ctor_set(v___x_1171_, 1, v___f_1170_);
v___f_1172_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1173_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1162_, v___f_1172_, v_inst_1150_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1174_, 0, v_inst_1151_);
lean_closure_set(v___f_1174_, 1, v___x_1162_);
lean_inc_ref(v___x_1143_);
v___x_1175_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1174_, v___x_1143_);
v___x_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1171_);
lean_ctor_set(v___x_1176_, 1, v___x_1173_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
v___x_7242__overap_1177_ = l_Lean_resolveNamespace___redArg(v___x_1143_, v___x_1156_, v___x_1166_, v___x_1176_, v_a_1152_);
v___x_1178_ = lean_apply_1(v___x_7242__overap_1177_, v___y_1155_);
v___x_1179_ = lean_apply_4(v_toBind_1144_, lean_box(0), lean_box(0), v___x_1178_, v___f_1168_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v_toPure_1209_, lean_object* v_inst_1210_, lean_object* v_toBind_1211_, uint8_t v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v_stx_1216_, lean_object* v___f_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v___f_1221_, lean_object* v___f_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v___x_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v___f_1229_, lean_object* v_ref_1230_){
_start:
{
lean_object* v___f_1231_; 
lean_inc(v_toBind_1211_);
lean_inc(v_inst_1210_);
lean_inc(v_ref_1230_);
lean_inc(v_toPure_1209_);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1231_, 0, v_toPure_1209_);
lean_closure_set(v___f_1231_, 1, v_ref_1230_);
lean_closure_set(v___f_1231_, 2, v_inst_1210_);
lean_closure_set(v___f_1231_, 3, v_toBind_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1232_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__0));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1233_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1232_);
lean_inc(v_stx_1216_);
v___x_1234_ = l_Lean_Syntax_isOfKind(v_stx_1216_, v___x_1233_);
lean_dec(v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1235_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__1));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1236_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1235_);
lean_inc(v_stx_1216_);
v___x_1237_ = l_Lean_Syntax_isOfKind(v_stx_1216_, v___x_1236_);
lean_dec(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1238_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__2));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1239_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1238_);
lean_inc(v_stx_1216_);
v___x_1240_ = l_Lean_Syntax_isOfKind(v_stx_1216_, v___x_1239_);
lean_dec(v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
lean_dec_ref(v___f_1229_);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__3));
lean_inc_ref(v___x_1215_);
lean_inc_ref(v___x_1214_);
lean_inc_ref(v___x_1213_);
v___x_1242_ = l_Lean_Name_mkStr4(v___x_1213_, v___x_1214_, v___x_1215_, v___x_1241_);
lean_inc(v_stx_1216_);
v___x_1243_ = l_Lean_Syntax_isOfKind(v_stx_1216_, v___x_1242_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___f_1244_; lean_object* v___f_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_7279__overap_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v___x_1225_);
lean_dec(v_inst_1224_);
lean_dec_ref(v_inst_1223_);
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec_ref(v_inst_1219_);
lean_dec(v_stx_1216_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_dec(v_inst_1210_);
lean_dec(v_toPure_1209_);
lean_inc(v_ref_1230_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1244_, 0, v___f_1217_);
lean_closure_set(v___f_1244_, 1, v_ref_1230_);
lean_inc_ref(v_inst_1218_);
v___f_1245_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1245_, 0, v_inst_1218_);
v___f_1246_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1246_, 0, v_inst_1218_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___f_1245_);
lean_ctor_set(v___x_1247_, 1, v___f_1246_);
v___x_7279__overap_1248_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1247_);
v___x_1249_ = lean_apply_1(v___x_7279__overap_1248_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1250_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1249_, v___f_1244_);
v___x_1251_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1250_, v___f_1231_);
return v___x_1251_;
}
else
{
lean_object* v___f_1252_; lean_object* v___f_1253_; lean_object* v___x_1254_; lean_object* v_ns_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___y_1261_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
lean_inc(v_ref_1230_);
lean_inc(v___f_1217_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1252_, 0, v___f_1217_);
lean_closure_set(v___f_1252_, 1, v_ref_1230_);
lean_inc(v_ref_1230_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1253_, 0, v___f_1217_);
lean_closure_set(v___f_1253_, 1, v_ref_1230_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v_ns_1255_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1254_);
v___x_1256_ = lean_unsigned_to_nat(2u);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1257_, 0, v___x_1213_);
lean_closure_set(v___f_1257_, 1, v___x_1214_);
lean_closure_set(v___f_1257_, 2, v___x_1215_);
lean_closure_set(v___f_1257_, 3, v___x_1254_);
lean_closure_set(v___f_1257_, 4, v___x_1256_);
v___x_1258_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1256_);
lean_dec(v_stx_1216_);
v___x_1259_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__13));
v___x_1304_ = l_Lean_Syntax_getArgs(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1305_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___closed__14));
v___x_1306_ = lean_array_get_size(v___x_1304_);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1308_ = lean_nat_dec_lt(v___x_1254_, v___x_1306_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v___x_1304_);
v___y_1261_ = v___x_1305_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1309_ = lean_box(v___x_1243_);
v___x_1310_ = lean_box(v___x_1240_);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 4, 2);
lean_closure_set(v___f_1311_, 0, v___x_1309_);
lean_closure_set(v___f_1311_, 1, v___x_1310_);
v___x_1312_ = lean_box(v___x_1243_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
lean_ctor_set(v___x_1313_, 1, v___x_1305_);
v___x_1314_ = lean_nat_dec_le(v___x_1306_, v___x_1306_);
if (v___x_1314_ == 0)
{
if (v___x_1308_ == 0)
{
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___f_1311_);
lean_dec_ref(v___x_1304_);
v___y_1261_ = v___x_1305_;
goto v___jp_1260_;
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; lean_object* v_snd_1318_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1306_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1307_, v___f_1311_, v___x_1304_, v___x_1315_, v___x_1316_, v___x_1313_);
v_snd_1318_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1318_);
lean_dec(v___x_1317_);
v___y_1261_ = v_snd_1318_;
goto v___jp_1260_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; lean_object* v_snd_1322_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1306_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1307_, v___f_1311_, v___x_1304_, v___x_1319_, v___x_1320_, v___x_1313_);
v_snd_1322_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_snd_1322_);
lean_dec(v___x_1321_);
v___y_1261_ = v_snd_1322_;
goto v___jp_1260_;
}
}
v___jp_1260_:
{
size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; 
v_sz_1262_ = lean_array_size(v___y_1261_);
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1259_, v___f_1257_, v_sz_1262_, v___x_1263_, v___y_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_7305__overap_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec(v_ns_1255_);
lean_dec_ref(v___f_1252_);
lean_dec(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v___x_1225_);
lean_dec(v_inst_1224_);
lean_dec_ref(v_inst_1223_);
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec_ref(v_inst_1219_);
lean_dec(v_inst_1210_);
lean_dec(v_toPure_1209_);
lean_inc_ref(v_inst_1218_);
v___f_1265_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1265_, 0, v_inst_1218_);
v___f_1266_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1266_, 0, v_inst_1218_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___f_1265_);
lean_ctor_set(v___x_1267_, 1, v___f_1266_);
v___x_7305__overap_1268_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1267_);
v___x_1269_ = lean_apply_1(v___x_7305__overap_1268_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1270_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1269_, v___f_1253_);
v___x_1271_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1270_, v___f_1231_);
return v___x_1271_;
}
else
{
lean_object* v_val_1272_; lean_object* v___x_1273_; size_t v_sz_1274_; lean_object* v___x_1275_; lean_object* v_getEnv_1276_; lean_object* v_modifyEnv_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v___f_1253_);
v_val_1272_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1272_);
lean_dec_ref(v___x_1264_);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1274_ = lean_array_size(v_val_1272_);
lean_inc(v_inst_1210_);
v___x_1275_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1219_, v_inst_1210_);
v_getEnv_1276_ = lean_ctor_get(v_inst_1220_, 0);
v_modifyEnv_1277_ = lean_ctor_get(v_inst_1220_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_inst_1220_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1279_ = v_inst_1220_;
v_isShared_1280_ = v_isSharedCheck_1303_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_modifyEnv_1277_);
lean_inc(v_getEnv_1276_);
lean_dec(v_inst_1220_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1303_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_tos_1281_; lean_object* v_froms_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_inc(v_val_1272_);
v_tos_1281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1273_, v___f_1221_, v_sz_1274_, v___x_1263_, v_val_1272_);
v_froms_1282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1273_, v___f_1222_, v_sz_1274_, v___x_1263_, v_val_1272_);
v___x_1283_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1284_, 0, v_modifyEnv_1277_);
lean_closure_set(v___f_1284_, 1, v___x_1283_);
v___x_1285_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1285_, 0, lean_box(0));
lean_closure_set(v___x_1285_, 1, lean_box(0));
lean_closure_set(v___x_1285_, 2, lean_box(0));
lean_closure_set(v___x_1285_, 3, lean_box(0));
lean_closure_set(v___x_1285_, 4, v_getEnv_1276_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___f_1284_);
lean_ctor_set(v___x_1279_, 0, v___x_1285_);
v___x_1287_ = v___x_1279_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___f_1284_);
v___x_1287_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; lean_object* v___x_7333__overap_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc_ref(v_inst_1218_);
v___f_1288_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1288_, 0, v_inst_1218_);
v___f_1289_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1289_, 0, v_inst_1218_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___f_1288_);
lean_ctor_set(v___x_1290_, 1, v___f_1289_);
v___f_1291_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1292_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1283_, v___f_1291_, v_inst_1223_);
v___f_1293_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1293_, 0, v_inst_1224_);
lean_closure_set(v___f_1293_, 1, v___x_1283_);
lean_inc_ref(v___x_1225_);
lean_inc_ref(v___f_1293_);
v___x_1294_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1293_, v___x_1225_);
lean_inc(v___x_1294_);
lean_inc_ref(v___x_1292_);
lean_inc_ref(v___x_1290_);
v___x_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1290_);
lean_ctor_set(v___x_1295_, 1, v___x_1292_);
lean_ctor_set(v___x_1295_, 2, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed__const__1));
lean_inc(v_ref_1230_);
lean_inc_ref(v___x_1275_);
lean_inc_ref(v___x_1295_);
lean_inc_ref(v___x_1287_);
lean_inc_ref(v___x_1225_);
lean_inc(v_toBind_1211_);
v___f_1297_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 21, 20);
lean_closure_set(v___f_1297_, 0, v_froms_1282_);
lean_closure_set(v___f_1297_, 1, v_tos_1281_);
lean_closure_set(v___f_1297_, 2, v_toPure_1209_);
lean_closure_set(v___f_1297_, 3, v___x_1283_);
lean_closure_set(v___f_1297_, 4, v_inst_1226_);
lean_closure_set(v___f_1297_, 5, v_inst_1210_);
lean_closure_set(v___f_1297_, 6, v_toBind_1211_);
lean_closure_set(v___f_1297_, 7, v___x_1225_);
lean_closure_set(v___f_1297_, 8, v___x_1287_);
lean_closure_set(v___f_1297_, 9, v___x_1295_);
lean_closure_set(v___f_1297_, 10, v_inst_1227_);
lean_closure_set(v___f_1297_, 11, v_inst_1228_);
lean_closure_set(v___f_1297_, 12, v___x_1290_);
lean_closure_set(v___f_1297_, 13, v___x_1292_);
lean_closure_set(v___f_1297_, 14, v___x_1294_);
lean_closure_set(v___f_1297_, 15, v___f_1293_);
lean_closure_set(v___f_1297_, 16, v___x_1275_);
lean_closure_set(v___f_1297_, 17, v___x_1296_);
lean_closure_set(v___f_1297_, 18, v_ref_1230_);
lean_closure_set(v___f_1297_, 19, v___f_1252_);
v___x_7333__overap_1298_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1225_, v___x_1275_, v___x_1287_, v___x_1295_, v_ns_1255_);
v___x_1299_ = lean_apply_1(v___x_7333__overap_1298_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1300_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1299_, v___f_1297_);
v___x_1301_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1300_, v___f_1231_);
return v___x_1301_;
}
}
}
}
}
}
else
{
lean_object* v___x_1323_; lean_object* v_getEnv_1324_; lean_object* v_modifyEnv_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_inc(v_inst_1210_);
v___x_1323_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1219_, v_inst_1210_);
v_getEnv_1324_ = lean_ctor_get(v_inst_1220_, 0);
v_modifyEnv_1325_ = lean_ctor_get(v_inst_1220_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_inst_1220_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1327_ = v_inst_1220_;
v_isShared_1328_ = v_isSharedCheck_1354_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_modifyEnv_1325_);
lean_inc(v_getEnv_1324_);
lean_dec(v_inst_1220_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1354_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v_ns_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_ids_1334_; lean_object* v___x_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_inc(v_ref_1230_);
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1329_, 0, v___f_1217_);
lean_closure_set(v___f_1329_, 1, v_ref_1230_);
v___x_1330_ = lean_unsigned_to_nat(0u);
v_ns_1331_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1330_);
v___x_1332_ = lean_unsigned_to_nat(2u);
v___x_1333_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1332_);
lean_dec(v_stx_1216_);
v_ids_1334_ = l_Lean_Syntax_getArgs(v___x_1333_);
lean_dec(v___x_1333_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1336_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1336_, 0, v_modifyEnv_1325_);
lean_closure_set(v___f_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1337_, 0, lean_box(0));
lean_closure_set(v___x_1337_, 1, lean_box(0));
lean_closure_set(v___x_1337_, 2, lean_box(0));
lean_closure_set(v___x_1337_, 3, lean_box(0));
lean_closure_set(v___x_1337_, 4, v_getEnv_1324_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___f_1336_);
lean_ctor_set(v___x_1327_, 0, v___x_1337_);
v___x_1339_ = v___x_1327_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___f_1336_);
v___x_1339_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___f_1340_; lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___f_1348_; lean_object* v___x_7377__overap_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
lean_inc_ref(v_inst_1218_);
v___f_1340_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1340_, 0, v_inst_1218_);
v___f_1341_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1341_, 0, v_inst_1218_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___f_1340_);
lean_ctor_set(v___x_1342_, 1, v___f_1341_);
v___f_1343_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1344_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1335_, v___f_1343_, v_inst_1223_);
v___f_1345_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1345_, 0, v_inst_1224_);
lean_closure_set(v___f_1345_, 1, v___x_1335_);
lean_inc_ref(v___x_1225_);
lean_inc_ref(v___f_1345_);
v___x_1346_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1345_, v___x_1225_);
lean_inc(v___x_1346_);
lean_inc_ref(v___x_1344_);
lean_inc_ref(v___x_1342_);
v___x_1347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1342_);
lean_ctor_set(v___x_1347_, 1, v___x_1344_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
lean_inc_ref(v___x_1323_);
lean_inc_ref(v___x_1347_);
lean_inc_ref(v___x_1339_);
lean_inc_ref(v___x_1225_);
lean_inc(v_toBind_1211_);
lean_inc(v_ref_1230_);
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 20, 19);
lean_closure_set(v___f_1348_, 0, v_ids_1334_);
lean_closure_set(v___f_1348_, 1, v___f_1229_);
lean_closure_set(v___f_1348_, 2, v_inst_1210_);
lean_closure_set(v___f_1348_, 3, v_ref_1230_);
lean_closure_set(v___f_1348_, 4, v_toBind_1211_);
lean_closure_set(v___f_1348_, 5, v___f_1329_);
lean_closure_set(v___f_1348_, 6, v_toPure_1209_);
lean_closure_set(v___f_1348_, 7, v___x_1335_);
lean_closure_set(v___f_1348_, 8, v_inst_1226_);
lean_closure_set(v___f_1348_, 9, v___x_1225_);
lean_closure_set(v___f_1348_, 10, v___x_1339_);
lean_closure_set(v___f_1348_, 11, v___x_1347_);
lean_closure_set(v___f_1348_, 12, v_inst_1227_);
lean_closure_set(v___f_1348_, 13, v_inst_1228_);
lean_closure_set(v___f_1348_, 14, v___x_1342_);
lean_closure_set(v___f_1348_, 15, v___x_1344_);
lean_closure_set(v___f_1348_, 16, v___x_1346_);
lean_closure_set(v___f_1348_, 17, v___f_1345_);
lean_closure_set(v___f_1348_, 18, v___x_1323_);
v___x_7377__overap_1349_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1225_, v___x_1323_, v___x_1339_, v___x_1347_, v_ns_1331_);
v___x_1350_ = lean_apply_1(v___x_7377__overap_1349_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1351_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1350_, v___f_1348_);
v___x_1352_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1351_, v___f_1231_);
return v___x_1352_;
}
}
}
}
else
{
lean_object* v___x_1355_; lean_object* v_getEnv_1356_; lean_object* v_modifyEnv_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___f_1229_);
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_inc(v_inst_1210_);
v___x_1355_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1219_, v_inst_1210_);
v_getEnv_1356_ = lean_ctor_get(v_inst_1220_, 0);
v_modifyEnv_1357_ = lean_ctor_get(v_inst_1220_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_inst_1220_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1359_ = v_inst_1220_;
v_isShared_1360_ = v_isSharedCheck_1386_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_modifyEnv_1357_);
lean_inc(v_getEnv_1356_);
lean_dec(v_inst_1220_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1386_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v_ns_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_ids_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_inc(v_ref_1230_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1361_, 0, v___f_1217_);
lean_closure_set(v___f_1361_, 1, v_ref_1230_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v_ns_1363_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1362_);
v___x_1364_ = lean_unsigned_to_nat(2u);
v___x_1365_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1364_);
lean_dec(v_stx_1216_);
v_ids_1366_ = l_Lean_Syntax_getArgs(v___x_1365_);
lean_dec(v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1368_, 0, v_modifyEnv_1357_);
lean_closure_set(v___f_1368_, 1, v___x_1367_);
v___x_1369_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1369_, 0, lean_box(0));
lean_closure_set(v___x_1369_, 1, lean_box(0));
lean_closure_set(v___x_1369_, 2, lean_box(0));
lean_closure_set(v___x_1369_, 3, lean_box(0));
lean_closure_set(v___x_1369_, 4, v_getEnv_1356_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___f_1368_);
lean_ctor_set(v___x_1359_, 0, v___x_1369_);
v___x_1371_ = v___x_1359_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___f_1368_);
v___x_1371_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___f_1372_; lean_object* v___f_1373_; lean_object* v___x_1374_; lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_7398__overap_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_inc_ref(v_inst_1218_);
v___f_1372_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1218_);
v___f_1373_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1373_, 0, v_inst_1218_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___f_1372_);
lean_ctor_set(v___x_1374_, 1, v___f_1373_);
v___f_1375_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1376_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1367_, v___f_1375_, v_inst_1223_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1377_, 0, v_inst_1224_);
lean_closure_set(v___f_1377_, 1, v___x_1367_);
lean_inc_ref(v___x_1225_);
lean_inc_ref(v___f_1377_);
v___x_1378_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1377_, v___x_1225_);
lean_inc(v___x_1378_);
lean_inc_ref(v___x_1376_);
lean_inc_ref(v___x_1374_);
v___x_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1374_);
lean_ctor_set(v___x_1379_, 1, v___x_1376_);
lean_ctor_set(v___x_1379_, 2, v___x_1378_);
lean_inc(v_ref_1230_);
lean_inc_ref(v___x_1355_);
lean_inc_ref(v___x_1379_);
lean_inc_ref(v___x_1371_);
lean_inc_ref(v___x_1225_);
lean_inc(v_toBind_1211_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 19, 18);
lean_closure_set(v___f_1380_, 0, v_toPure_1209_);
lean_closure_set(v___f_1380_, 1, v___x_1367_);
lean_closure_set(v___f_1380_, 2, v_inst_1226_);
lean_closure_set(v___f_1380_, 3, v_inst_1210_);
lean_closure_set(v___f_1380_, 4, v_toBind_1211_);
lean_closure_set(v___f_1380_, 5, v___x_1225_);
lean_closure_set(v___f_1380_, 6, v___x_1371_);
lean_closure_set(v___f_1380_, 7, v___x_1379_);
lean_closure_set(v___f_1380_, 8, v_inst_1227_);
lean_closure_set(v___f_1380_, 9, v_inst_1228_);
lean_closure_set(v___f_1380_, 10, v___x_1374_);
lean_closure_set(v___f_1380_, 11, v___x_1376_);
lean_closure_set(v___f_1380_, 12, v___x_1378_);
lean_closure_set(v___f_1380_, 13, v___f_1377_);
lean_closure_set(v___f_1380_, 14, v___x_1355_);
lean_closure_set(v___f_1380_, 15, v_ids_1366_);
lean_closure_set(v___f_1380_, 16, v_ref_1230_);
lean_closure_set(v___f_1380_, 17, v___f_1361_);
v___x_7398__overap_1381_ = l_Lean_resolveNamespace___redArg(v___x_1225_, v___x_1355_, v___x_1371_, v___x_1379_, v_ns_1363_);
v___x_1382_ = lean_apply_1(v___x_7398__overap_1381_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1383_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1382_, v___f_1380_);
v___x_1384_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1383_, v___f_1231_);
return v___x_1384_;
}
}
}
}
else
{
lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_nss_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___f_1393_; size_t v_sz_1394_; size_t v___x_1395_; lean_object* v___x_7409__overap_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec_ref(v___f_1229_);
lean_dec(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_inc(v_ref_1230_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1387_, 0, v___f_1217_);
lean_closure_set(v___f_1387_, 1, v_ref_1230_);
v___x_1388_ = lean_unsigned_to_nat(1u);
v___x_1389_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1388_);
lean_dec(v_stx_1216_);
v_nss_1390_ = l_Lean_Syntax_getArgs(v___x_1389_);
lean_dec(v___x_1389_);
v___x_1391_ = lean_box(0);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1392_, 0, v___x_1391_);
lean_closure_set(v___f_1392_, 1, v_toPure_1209_);
lean_inc_ref(v___f_1392_);
lean_inc(v_toBind_1211_);
lean_inc_ref(v___x_1225_);
v___f_1393_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30), 15, 11);
lean_closure_set(v___f_1393_, 0, v_inst_1219_);
lean_closure_set(v___f_1393_, 1, v_inst_1210_);
lean_closure_set(v___f_1393_, 2, v_inst_1220_);
lean_closure_set(v___f_1393_, 3, v___x_1225_);
lean_closure_set(v___f_1393_, 4, v_toBind_1211_);
lean_closure_set(v___f_1393_, 5, v___f_1392_);
lean_closure_set(v___f_1393_, 6, v___x_1391_);
lean_closure_set(v___f_1393_, 7, v___f_1392_);
lean_closure_set(v___f_1393_, 8, v_inst_1218_);
lean_closure_set(v___f_1393_, 9, v_inst_1223_);
lean_closure_set(v___f_1393_, 10, v_inst_1224_);
v_sz_1394_ = lean_array_size(v_nss_1390_);
v___x_1395_ = ((size_t)0ULL);
v___x_7409__overap_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1225_, v_nss_1390_, v___f_1393_, v_sz_1394_, v___x_1395_, v___x_1391_);
v___x_1397_ = lean_apply_1(v___x_7409__overap_1396_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1398_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1397_, v___f_1387_);
v___x_1399_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1398_, v___f_1231_);
return v___x_1399_;
}
}
else
{
lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_nss_1404_; lean_object* v___x_1405_; lean_object* v___f_1406_; lean_object* v___f_1407_; size_t v_sz_1408_; size_t v___x_1409_; lean_object* v___x_7421__overap_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec_ref(v___f_1229_);
lean_dec(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec_ref(v___f_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_inc(v_ref_1230_);
v___f_1400_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1400_, 0, v___f_1217_);
lean_closure_set(v___f_1400_, 1, v_ref_1230_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = l_Lean_Syntax_getArg(v_stx_1216_, v___x_1401_);
lean_dec(v_stx_1216_);
v___x_1403_ = lean_box(0);
v_nss_1404_ = l_Lean_Syntax_getArgs(v___x_1402_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1406_, 0, v___x_1405_);
lean_closure_set(v___f_1406_, 1, v_toPure_1209_);
lean_inc_ref(v___f_1406_);
lean_inc(v_toBind_1211_);
lean_inc_ref(v___x_1225_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34), 16, 12);
lean_closure_set(v___f_1407_, 0, v_inst_1219_);
lean_closure_set(v___f_1407_, 1, v_inst_1210_);
lean_closure_set(v___f_1407_, 2, v_inst_1220_);
lean_closure_set(v___f_1407_, 3, v___x_1225_);
lean_closure_set(v___f_1407_, 4, v_toBind_1211_);
lean_closure_set(v___f_1407_, 5, v___f_1406_);
lean_closure_set(v___f_1407_, 6, v___x_1403_);
lean_closure_set(v___f_1407_, 7, v___x_1405_);
lean_closure_set(v___f_1407_, 8, v___f_1406_);
lean_closure_set(v___f_1407_, 9, v_inst_1218_);
lean_closure_set(v___f_1407_, 10, v_inst_1223_);
lean_closure_set(v___f_1407_, 11, v_inst_1224_);
v_sz_1408_ = lean_array_size(v_nss_1404_);
v___x_1409_ = ((size_t)0ULL);
v___x_7421__overap_1410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1225_, v_nss_1404_, v___f_1407_, v_sz_1408_, v___x_1409_, v___x_1405_);
v___x_1411_ = lean_apply_1(v___x_7421__overap_1410_, v_ref_1230_);
lean_inc(v_toBind_1211_);
v___x_1412_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1411_, v___f_1400_);
v___x_1413_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1412_, v___f_1231_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object** _args){
lean_object* v_toPure_1414_ = _args[0];
lean_object* v_inst_1415_ = _args[1];
lean_object* v_toBind_1416_ = _args[2];
lean_object* v___x_1417_ = _args[3];
lean_object* v___x_1418_ = _args[4];
lean_object* v___x_1419_ = _args[5];
lean_object* v___x_1420_ = _args[6];
lean_object* v_stx_1421_ = _args[7];
lean_object* v___f_1422_ = _args[8];
lean_object* v_inst_1423_ = _args[9];
lean_object* v_inst_1424_ = _args[10];
lean_object* v_inst_1425_ = _args[11];
lean_object* v___f_1426_ = _args[12];
lean_object* v___f_1427_ = _args[13];
lean_object* v_inst_1428_ = _args[14];
lean_object* v_inst_1429_ = _args[15];
lean_object* v___x_1430_ = _args[16];
lean_object* v_inst_1431_ = _args[17];
lean_object* v_inst_1432_ = _args[18];
lean_object* v_inst_1433_ = _args[19];
lean_object* v___f_1434_ = _args[20];
lean_object* v_ref_1435_ = _args[21];
_start:
{
uint8_t v___x_8664__boxed_1436_; lean_object* v_res_1437_; 
v___x_8664__boxed_1436_ = lean_unbox(v___x_1417_);
v_res_1437_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v_toPure_1414_, v_inst_1415_, v_toBind_1416_, v___x_8664__boxed_1436_, v___x_1418_, v___x_1419_, v___x_1420_, v_stx_1421_, v___f_1422_, v_inst_1423_, v_inst_1424_, v_inst_1425_, v___f_1426_, v___f_1427_, v_inst_1428_, v_inst_1429_, v___x_1430_, v_inst_1431_, v_inst_1432_, v_inst_1433_, v___f_1434_, v_ref_1435_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v_toPure_1438_, lean_object* v_____x_1439_){
_start:
{
lean_object* v_fst_1440_; lean_object* v___x_1441_; 
v_fst_1440_ = lean_ctor_get(v_____x_1439_, 0);
lean_inc(v_fst_1440_);
lean_dec_ref(v_____x_1439_);
v___x_1441_ = lean_apply_2(v_toPure_1438_, lean_box(0), v_fst_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v_toApplicative_1451_, lean_object* v_stx_1452_, lean_object* v_____do__lift_1453_, lean_object* v_inst_1454_, lean_object* v_toBind_1455_, lean_object* v___f_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_, lean_object* v___f_1460_, lean_object* v___f_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v___x_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v___f_1468_, lean_object* v_____do__lift_1469_){
_start:
{
lean_object* v_toPure_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___f_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_toPure_1470_ = lean_ctor_get(v_toApplicative_1451_, 1);
lean_inc(v_toPure_1470_);
lean_dec_ref(v_toApplicative_1451_);
v___x_1471_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__0));
v___x_1472_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__1));
v___x_1473_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__2));
v___x_1474_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___closed__4));
lean_inc(v_stx_1452_);
v___x_1475_ = l_Lean_Syntax_isOfKind(v_stx_1452_, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_____do__lift_1453_);
lean_ctor_set(v___x_1476_, 1, v_____do__lift_1469_);
v___x_1477_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1477_, 0, lean_box(0));
lean_closure_set(v___x_1477_, 1, lean_box(0));
lean_closure_set(v___x_1477_, 2, v___x_1476_);
lean_inc(v_inst_1454_);
v___x_1478_ = lean_apply_2(v_inst_1454_, lean_box(0), v___x_1477_);
v___x_1479_ = lean_box(v___x_1475_);
lean_inc(v_toBind_1455_);
lean_inc(v_toPure_1470_);
v___f_1480_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 22, 21);
lean_closure_set(v___f_1480_, 0, v_toPure_1470_);
lean_closure_set(v___f_1480_, 1, v_inst_1454_);
lean_closure_set(v___f_1480_, 2, v_toBind_1455_);
lean_closure_set(v___f_1480_, 3, v___x_1479_);
lean_closure_set(v___f_1480_, 4, v___x_1471_);
lean_closure_set(v___f_1480_, 5, v___x_1472_);
lean_closure_set(v___f_1480_, 6, v___x_1473_);
lean_closure_set(v___f_1480_, 7, v_stx_1452_);
lean_closure_set(v___f_1480_, 8, v___f_1456_);
lean_closure_set(v___f_1480_, 9, v_inst_1457_);
lean_closure_set(v___f_1480_, 10, v_inst_1458_);
lean_closure_set(v___f_1480_, 11, v_inst_1459_);
lean_closure_set(v___f_1480_, 12, v___f_1460_);
lean_closure_set(v___f_1480_, 13, v___f_1461_);
lean_closure_set(v___f_1480_, 14, v_inst_1462_);
lean_closure_set(v___f_1480_, 15, v_inst_1463_);
lean_closure_set(v___f_1480_, 16, v___x_1464_);
lean_closure_set(v___f_1480_, 17, v_inst_1465_);
lean_closure_set(v___f_1480_, 18, v_inst_1466_);
lean_closure_set(v___f_1480_, 19, v_inst_1467_);
lean_closure_set(v___f_1480_, 20, v___f_1468_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36), 2, 1);
lean_closure_set(v___f_1481_, 0, v_toPure_1470_);
lean_inc(v_toBind_1455_);
v___x_1482_ = lean_apply_4(v_toBind_1455_, lean_box(0), lean_box(0), v___x_1478_, v___f_1480_);
v___x_1483_ = lean_apply_4(v_toBind_1455_, lean_box(0), lean_box(0), v___x_1482_, v___f_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object** _args){
lean_object* v_toApplicative_1484_ = _args[0];
lean_object* v_stx_1485_ = _args[1];
lean_object* v_____do__lift_1486_ = _args[2];
lean_object* v_inst_1487_ = _args[3];
lean_object* v_toBind_1488_ = _args[4];
lean_object* v___f_1489_ = _args[5];
lean_object* v_inst_1490_ = _args[6];
lean_object* v_inst_1491_ = _args[7];
lean_object* v_inst_1492_ = _args[8];
lean_object* v___f_1493_ = _args[9];
lean_object* v___f_1494_ = _args[10];
lean_object* v_inst_1495_ = _args[11];
lean_object* v_inst_1496_ = _args[12];
lean_object* v___x_1497_ = _args[13];
lean_object* v_inst_1498_ = _args[14];
lean_object* v_inst_1499_ = _args[15];
lean_object* v_inst_1500_ = _args[16];
lean_object* v___f_1501_ = _args[17];
lean_object* v_____do__lift_1502_ = _args[18];
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(v_toApplicative_1484_, v_stx_1485_, v_____do__lift_1486_, v_inst_1487_, v_toBind_1488_, v___f_1489_, v_inst_1490_, v_inst_1491_, v_inst_1492_, v___f_1493_, v___f_1494_, v_inst_1495_, v_inst_1496_, v___x_1497_, v_inst_1498_, v_inst_1499_, v_inst_1500_, v___f_1501_, v_____do__lift_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v_toApplicative_1504_, lean_object* v_stx_1505_, lean_object* v_inst_1506_, lean_object* v_toBind_1507_, lean_object* v___f_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v___f_1512_, lean_object* v___f_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v___x_1516_, lean_object* v_inst_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v___f_1520_, lean_object* v_getCurrNamespace_1521_, lean_object* v_____do__lift_1522_){
_start:
{
lean_object* v___f_1523_; lean_object* v___x_1524_; 
lean_inc(v_toBind_1507_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed), 19, 18);
lean_closure_set(v___f_1523_, 0, v_toApplicative_1504_);
lean_closure_set(v___f_1523_, 1, v_stx_1505_);
lean_closure_set(v___f_1523_, 2, v_____do__lift_1522_);
lean_closure_set(v___f_1523_, 3, v_inst_1506_);
lean_closure_set(v___f_1523_, 4, v_toBind_1507_);
lean_closure_set(v___f_1523_, 5, v___f_1508_);
lean_closure_set(v___f_1523_, 6, v_inst_1509_);
lean_closure_set(v___f_1523_, 7, v_inst_1510_);
lean_closure_set(v___f_1523_, 8, v_inst_1511_);
lean_closure_set(v___f_1523_, 9, v___f_1512_);
lean_closure_set(v___f_1523_, 10, v___f_1513_);
lean_closure_set(v___f_1523_, 11, v_inst_1514_);
lean_closure_set(v___f_1523_, 12, v_inst_1515_);
lean_closure_set(v___f_1523_, 13, v___x_1516_);
lean_closure_set(v___f_1523_, 14, v_inst_1517_);
lean_closure_set(v___f_1523_, 15, v_inst_1518_);
lean_closure_set(v___f_1523_, 16, v_inst_1519_);
lean_closure_set(v___f_1523_, 17, v___f_1520_);
v___x_1524_ = lean_apply_4(v_toBind_1507_, lean_box(0), lean_box(0), v_getCurrNamespace_1521_, v___f_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object** _args){
lean_object* v_toApplicative_1525_ = _args[0];
lean_object* v_stx_1526_ = _args[1];
lean_object* v_inst_1527_ = _args[2];
lean_object* v_toBind_1528_ = _args[3];
lean_object* v___f_1529_ = _args[4];
lean_object* v_inst_1530_ = _args[5];
lean_object* v_inst_1531_ = _args[6];
lean_object* v_inst_1532_ = _args[7];
lean_object* v___f_1533_ = _args[8];
lean_object* v___f_1534_ = _args[9];
lean_object* v_inst_1535_ = _args[10];
lean_object* v_inst_1536_ = _args[11];
lean_object* v___x_1537_ = _args[12];
lean_object* v_inst_1538_ = _args[13];
lean_object* v_inst_1539_ = _args[14];
lean_object* v_inst_1540_ = _args[15];
lean_object* v___f_1541_ = _args[16];
lean_object* v_getCurrNamespace_1542_ = _args[17];
lean_object* v_____do__lift_1543_ = _args[18];
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(v_toApplicative_1525_, v_stx_1526_, v_inst_1527_, v_toBind_1528_, v___f_1529_, v_inst_1530_, v_inst_1531_, v_inst_1532_, v___f_1533_, v___f_1534_, v_inst_1535_, v_inst_1536_, v___x_1537_, v_inst_1538_, v_inst_1539_, v_inst_1540_, v___f_1541_, v_getCurrNamespace_1542_, v_____do__lift_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1548_, lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_stx_1558_){
_start:
{
lean_object* v_toApplicative_1559_; lean_object* v_toBind_1560_; lean_object* v_getCurrNamespace_1561_; lean_object* v_getOpenDecls_1562_; lean_object* v___f_1563_; lean_object* v___f_1564_; lean_object* v___f_1565_; lean_object* v___f_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
v_toApplicative_1559_ = lean_ctor_get(v_inst_1548_, 0);
lean_inc_ref(v_toApplicative_1559_);
v_toBind_1560_ = lean_ctor_get(v_inst_1548_, 1);
lean_inc(v_toBind_1560_);
v_getCurrNamespace_1561_ = lean_ctor_get(v_inst_1556_, 0);
lean_inc(v_getCurrNamespace_1561_);
v_getOpenDecls_1562_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc(v_getOpenDecls_1562_);
lean_dec_ref(v_inst_1556_);
lean_inc_ref(v_toApplicative_1559_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1563_, 0, v_toApplicative_1559_);
lean_inc(v_toBind_1560_);
lean_inc(v_inst_1553_);
v___f_1564_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1564_, 0, v_inst_1553_);
lean_closure_set(v___f_1564_, 1, v_toBind_1560_);
lean_closure_set(v___f_1564_, 2, v___f_1563_);
v___f_1565_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__0));
v___f_1566_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__1));
v___f_1567_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__2));
lean_inc_ref(v_inst_1548_);
v___x_1568_ = l_ReaderT_instMonad___redArg(v_inst_1548_);
lean_inc(v_toBind_1560_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed), 19, 18);
lean_closure_set(v___f_1569_, 0, v_toApplicative_1559_);
lean_closure_set(v___f_1569_, 1, v_stx_1558_);
lean_closure_set(v___f_1569_, 2, v_inst_1553_);
lean_closure_set(v___f_1569_, 3, v_toBind_1560_);
lean_closure_set(v___f_1569_, 4, v___f_1564_);
lean_closure_set(v___f_1569_, 5, v_inst_1550_);
lean_closure_set(v___f_1569_, 6, v_inst_1548_);
lean_closure_set(v___f_1569_, 7, v_inst_1549_);
lean_closure_set(v___f_1569_, 8, v___f_1565_);
lean_closure_set(v___f_1569_, 9, v___f_1566_);
lean_closure_set(v___f_1569_, 10, v_inst_1551_);
lean_closure_set(v___f_1569_, 11, v_inst_1552_);
lean_closure_set(v___f_1569_, 12, v___x_1568_);
lean_closure_set(v___f_1569_, 13, v_inst_1557_);
lean_closure_set(v___f_1569_, 14, v_inst_1554_);
lean_closure_set(v___f_1569_, 15, v_inst_1555_);
lean_closure_set(v___f_1569_, 16, v___f_1567_);
lean_closure_set(v___f_1569_, 17, v_getCurrNamespace_1561_);
v___x_1570_ = lean_apply_4(v_toBind_1560_, lean_box(0), lean_box(0), v_getOpenDecls_1562_, v___f_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1571_, lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_inst_1581_, lean_object* v_stx_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1572_, v_inst_1573_, v_inst_1574_, v_inst_1575_, v_inst_1576_, v_inst_1577_, v_inst_1578_, v_inst_1579_, v_inst_1580_, v_inst_1581_, v_stx_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0(lean_object* v_a_1584_, lean_object* v_toPure_1585_, lean_object* v_s_1586_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1584_);
lean_ctor_set(v___x_1587_, 1, v_s_1586_);
v___x_1588_ = lean_apply_2(v_toPure_1585_, lean_box(0), v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1(lean_object* v_toPure_1589_, lean_object* v_ref_1590_, lean_object* v_inst_1591_, lean_object* v_toBind_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1594_, 0, v_a_1593_);
lean_closure_set(v___f_1594_, 1, v_toPure_1589_);
v___x_1595_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1595_, 0, lean_box(0));
lean_closure_set(v___x_1595_, 1, lean_box(0));
lean_closure_set(v___x_1595_, 2, v_ref_1590_);
v___x_1596_ = lean_apply_2(v_inst_1591_, lean_box(0), v___x_1595_);
v___x_1597_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1596_, v___f_1594_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2(lean_object* v_toPure_1598_, lean_object* v_inst_1599_, lean_object* v_toBind_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v___x_1603_, lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v___f_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_nss_1610_, lean_object* v_idStx_1611_, lean_object* v_ref_1612_){
_start:
{
lean_object* v___f_1613_; lean_object* v___x_101__overap_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_inc(v_toBind_1600_);
lean_inc(v_ref_1612_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1613_, 0, v_toPure_1598_);
lean_closure_set(v___f_1613_, 1, v_ref_1612_);
lean_closure_set(v___f_1613_, 2, v_inst_1599_);
lean_closure_set(v___f_1613_, 3, v_toBind_1600_);
v___x_101__overap_1614_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1601_, v___x_1602_, v___x_1603_, v___x_1604_, v___x_1605_, v___f_1606_, v___x_1607_, v___x_1608_, v___x_1609_, v_nss_1610_, v_idStx_1611_);
v___x_1615_ = lean_apply_1(v___x_101__overap_1614_, v_ref_1612_);
v___x_1616_ = lean_apply_4(v_toBind_1600_, lean_box(0), lean_box(0), v___x_1615_, v___f_1613_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3(lean_object* v_toPure_1617_, lean_object* v_____x_1618_){
_start:
{
lean_object* v_fst_1619_; lean_object* v___x_1620_; 
v_fst_1619_ = lean_ctor_get(v_____x_1618_, 0);
lean_inc(v_fst_1619_);
lean_dec_ref(v_____x_1618_);
v___x_1620_ = lean_apply_2(v_toPure_1617_, lean_box(0), v_fst_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4(lean_object* v_toApplicative_1621_, lean_object* v_____do__lift_1622_, lean_object* v_inst_1623_, lean_object* v_toBind_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v___f_1630_, lean_object* v___x_1631_, lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v_nss_1634_, lean_object* v_idStx_1635_, lean_object* v_____do__lift_1636_){
_start:
{
lean_object* v_toPure_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___f_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toPure_1637_ = lean_ctor_get(v_toApplicative_1621_, 1);
lean_inc(v_toPure_1637_);
lean_dec_ref(v_toApplicative_1621_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_____do__lift_1622_);
lean_ctor_set(v___x_1638_, 1, v_____do__lift_1636_);
v___x_1639_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1639_, 0, lean_box(0));
lean_closure_set(v___x_1639_, 1, lean_box(0));
lean_closure_set(v___x_1639_, 2, v___x_1638_);
lean_inc(v_inst_1623_);
v___x_1640_ = lean_apply_2(v_inst_1623_, lean_box(0), v___x_1639_);
lean_inc(v_toBind_1624_);
lean_inc(v_toPure_1637_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__2), 15, 14);
lean_closure_set(v___f_1641_, 0, v_toPure_1637_);
lean_closure_set(v___f_1641_, 1, v_inst_1623_);
lean_closure_set(v___f_1641_, 2, v_toBind_1624_);
lean_closure_set(v___f_1641_, 3, v___x_1625_);
lean_closure_set(v___f_1641_, 4, v___x_1626_);
lean_closure_set(v___f_1641_, 5, v___x_1627_);
lean_closure_set(v___f_1641_, 6, v___x_1628_);
lean_closure_set(v___f_1641_, 7, v___x_1629_);
lean_closure_set(v___f_1641_, 8, v___f_1630_);
lean_closure_set(v___f_1641_, 9, v___x_1631_);
lean_closure_set(v___f_1641_, 10, v___x_1632_);
lean_closure_set(v___f_1641_, 11, v___x_1633_);
lean_closure_set(v___f_1641_, 12, v_nss_1634_);
lean_closure_set(v___f_1641_, 13, v_idStx_1635_);
v___f_1642_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__3), 2, 1);
lean_closure_set(v___f_1642_, 0, v_toPure_1637_);
lean_inc(v_toBind_1624_);
v___x_1643_ = lean_apply_4(v_toBind_1624_, lean_box(0), lean_box(0), v___x_1640_, v___f_1641_);
v___x_1644_ = lean_apply_4(v_toBind_1624_, lean_box(0), lean_box(0), v___x_1643_, v___f_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5(lean_object* v_toApplicative_1645_, lean_object* v_inst_1646_, lean_object* v_toBind_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___f_1653_, lean_object* v___x_1654_, lean_object* v___x_1655_, lean_object* v___x_1656_, lean_object* v_nss_1657_, lean_object* v_idStx_1658_, lean_object* v_getCurrNamespace_1659_, lean_object* v_____do__lift_1660_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1662_; 
lean_inc(v_toBind_1647_);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__4), 16, 15);
lean_closure_set(v___f_1661_, 0, v_toApplicative_1645_);
lean_closure_set(v___f_1661_, 1, v_____do__lift_1660_);
lean_closure_set(v___f_1661_, 2, v_inst_1646_);
lean_closure_set(v___f_1661_, 3, v_toBind_1647_);
lean_closure_set(v___f_1661_, 4, v___x_1648_);
lean_closure_set(v___f_1661_, 5, v___x_1649_);
lean_closure_set(v___f_1661_, 6, v___x_1650_);
lean_closure_set(v___f_1661_, 7, v___x_1651_);
lean_closure_set(v___f_1661_, 8, v___x_1652_);
lean_closure_set(v___f_1661_, 9, v___f_1653_);
lean_closure_set(v___f_1661_, 10, v___x_1654_);
lean_closure_set(v___f_1661_, 11, v___x_1655_);
lean_closure_set(v___f_1661_, 12, v___x_1656_);
lean_closure_set(v___f_1661_, 13, v_nss_1657_);
lean_closure_set(v___f_1661_, 14, v_idStx_1658_);
v___x_1662_ = lean_apply_4(v_toBind_1647_, lean_box(0), lean_box(0), v_getCurrNamespace_1659_, v___f_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_nss_1672_, lean_object* v_idStx_1673_){
_start:
{
lean_object* v_toApplicative_1674_; lean_object* v_toBind_1675_; lean_object* v_getCurrNamespace_1676_; lean_object* v_getOpenDecls_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1708_; 
v_toApplicative_1674_ = lean_ctor_get(v_inst_1663_, 0);
lean_inc_ref(v_toApplicative_1674_);
v_toBind_1675_ = lean_ctor_get(v_inst_1663_, 1);
lean_inc(v_toBind_1675_);
v_getCurrNamespace_1676_ = lean_ctor_get(v_inst_1671_, 0);
v_getOpenDecls_1677_ = lean_ctor_get(v_inst_1671_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_inst_1671_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1679_ = v_inst_1671_;
v_isShared_1680_ = v_isSharedCheck_1708_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_getOpenDecls_1677_);
lean_inc(v_getCurrNamespace_1676_);
lean_dec(v_inst_1671_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1708_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v_getEnv_1682_; lean_object* v_modifyEnv_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1707_; 
lean_inc_ref(v_inst_1663_);
v___x_1681_ = l_ReaderT_instMonad___redArg(v_inst_1663_);
v_getEnv_1682_ = lean_ctor_get(v_inst_1664_, 0);
v_modifyEnv_1683_ = lean_ctor_get(v_inst_1664_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_inst_1664_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1685_ = v_inst_1664_;
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_modifyEnv_1683_);
lean_inc(v_getEnv_1682_);
lean_dec(v_inst_1664_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1707_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1687_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__0));
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1688_, 0, v_modifyEnv_1683_);
lean_closure_set(v___f_1688_, 1, v___x_1687_);
v___x_1689_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1689_, 0, lean_box(0));
lean_closure_set(v___x_1689_, 1, lean_box(0));
lean_closure_set(v___x_1689_, 2, lean_box(0));
lean_closure_set(v___x_1689_, 3, lean_box(0));
lean_closure_set(v___x_1689_, 4, v_getEnv_1682_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___f_1688_);
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___f_1688_);
v___x_1691_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1695_; 
lean_inc_ref(v_inst_1665_);
v___f_1692_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1692_, 0, v_inst_1665_);
v___f_1693_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1693_, 0, v_inst_1665_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___f_1693_);
lean_ctor_set(v___x_1679_, 0, v___f_1692_);
v___x_1695_ = v___x_1679_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___f_1692_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___f_1693_);
v___x_1695_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; 
v___f_1696_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___closed__1));
v___x_1697_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1687_, v___f_1696_, v_inst_1666_);
v___f_1698_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1698_, 0, v_inst_1667_);
lean_closure_set(v___f_1698_, 1, v___x_1687_);
lean_inc_ref(v___x_1681_);
lean_inc_ref(v___f_1698_);
v___x_1699_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1698_, v___x_1681_);
v___x_1700_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1687_, v_inst_1669_);
v___x_1701_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1701_, 0, lean_box(0));
lean_closure_set(v___x_1701_, 1, lean_box(0));
lean_closure_set(v___x_1701_, 2, lean_box(0));
lean_closure_set(v___x_1701_, 3, lean_box(0));
lean_closure_set(v___x_1701_, 4, v_inst_1670_);
lean_inc(v_inst_1668_);
v___x_1702_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1663_, v_inst_1668_);
lean_inc(v_toBind_1675_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__5), 16, 15);
lean_closure_set(v___f_1703_, 0, v_toApplicative_1674_);
lean_closure_set(v___f_1703_, 1, v_inst_1668_);
lean_closure_set(v___f_1703_, 2, v_toBind_1675_);
lean_closure_set(v___f_1703_, 3, v___x_1681_);
lean_closure_set(v___f_1703_, 4, v___x_1691_);
lean_closure_set(v___f_1703_, 5, v___x_1695_);
lean_closure_set(v___f_1703_, 6, v___x_1697_);
lean_closure_set(v___f_1703_, 7, v___x_1699_);
lean_closure_set(v___f_1703_, 8, v___f_1698_);
lean_closure_set(v___f_1703_, 9, v___x_1700_);
lean_closure_set(v___f_1703_, 10, v___x_1701_);
lean_closure_set(v___f_1703_, 11, v___x_1702_);
lean_closure_set(v___f_1703_, 12, v_nss_1672_);
lean_closure_set(v___f_1703_, 13, v_idStx_1673_);
lean_closure_set(v___f_1703_, 14, v_getCurrNamespace_1676_);
v___x_1704_ = lean_apply_4(v_toBind_1675_, lean_box(0), lean_box(0), v_getOpenDecls_1677_, v___f_1703_);
return v___x_1704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces(lean_object* v_m_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_nss_1719_, lean_object* v_idStx_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg(v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_inst_1714_, v_inst_1715_, v_inst_1716_, v_inst_1717_, v_inst_1718_, v_nss_1719_, v_idStx_1720_);
return v___x_1721_;
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
