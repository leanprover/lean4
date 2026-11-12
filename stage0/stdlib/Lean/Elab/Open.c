// Lean compiler output
// Module: Lean.Elab.Open
// Imports: public import Lean.Elab.Util public import Lean.Parser.Command meta import Lean.Parser.Command public import Lean.Linter.AmbiguousOpen public import Lean.Linter.Deprecated import Init.Omega
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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_bind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instFunctorOption___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_instMonadOption___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadOption___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Linter_mkReplacementHint___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__0 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__0_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "openOnly"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__1_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openHiding"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__2 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__2_value;
static const lean_string_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "openRenaming"};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__3 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__3_value;
static const lean_array_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__4 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__4_value;
static const lean_ctor_object l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed__const__1 = (const lean_object*)&l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(lean_object* v_snd_458_, lean_object* v_a_459_, lean_object* v_inst_460_, lean_object* v___y_461_, lean_object* v_toBind_462_, lean_object* v___f_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_465_ = l_Lean_Syntax_getId(v_snd_458_);
v___x_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_a_459_);
v___x_467_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_460_, v___x_466_, v___y_461_);
v___x_468_ = lean_apply_4(v_toBind_462_, lean_box(0), lean_box(0), v___x_467_, v___f_463_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed(lean_object* v_snd_469_, lean_object* v_a_470_, lean_object* v_inst_471_, lean_object* v___y_472_, lean_object* v_toBind_473_, lean_object* v___f_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10(v_snd_469_, v_a_470_, v_inst_471_, v___y_472_, v_toBind_473_, v___f_474_, v_a_475_);
lean_dec(v___y_472_);
lean_dec(v_snd_469_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(lean_object* v_snd_477_, lean_object* v_a_478_, lean_object* v_inst_479_, lean_object* v_toBind_480_, lean_object* v___f_481_, lean_object* v_reportDeprecated_482_, lean_object* v_fst_483_, lean_object* v_____r_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_toBind_480_);
lean_inc(v___y_485_);
lean_inc(v_a_478_);
v___f_486_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__10___boxed), 7, 6);
lean_closure_set(v___f_486_, 0, v_snd_477_);
lean_closure_set(v___f_486_, 1, v_a_478_);
lean_closure_set(v___f_486_, 2, v_inst_479_);
lean_closure_set(v___f_486_, 3, v___y_485_);
lean_closure_set(v___f_486_, 4, v_toBind_480_);
lean_closure_set(v___f_486_, 5, v___f_481_);
v___x_487_ = lean_apply_2(v_reportDeprecated_482_, v_fst_483_, v_a_478_);
v___x_488_ = lean_apply_4(v_toBind_480_, lean_box(0), lean_box(0), v___x_487_, v___f_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed(lean_object* v_snd_489_, lean_object* v_a_490_, lean_object* v_inst_491_, lean_object* v_toBind_492_, lean_object* v___f_493_, lean_object* v_reportDeprecated_494_, lean_object* v_fst_495_, lean_object* v_____r_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11(v_snd_489_, v_a_490_, v_inst_491_, v_toBind_492_, v___f_493_, v_reportDeprecated_494_, v_fst_495_, v_____r_496_, v___y_497_);
lean_dec(v___y_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(lean_object* v___f_499_, lean_object* v___y_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___x_502_; 
lean_inc(v___y_500_);
v___x_502_ = lean_apply_2(v___f_499_, v_a_501_, v___y_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed(lean_object* v___f_503_, lean_object* v___y_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12(v___f_503_, v___y_504_, v_a_505_);
lean_dec(v___y_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(lean_object* v___x_507_, lean_object* v___x_508_, lean_object* v___x_509_, lean_object* v___x_510_, lean_object* v_snd_511_, lean_object* v_a_512_, lean_object* v___x_513_, lean_object* v___y_514_, lean_object* v_toBind_515_, lean_object* v___f_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_3793__overap_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_3793__overap_518_ = l_Lean_Elab_addConstInfo___redArg(v___x_507_, v___x_508_, v___x_509_, v___x_510_, v_snd_511_, v_a_512_, v___x_513_);
lean_inc(v___y_514_);
v___x_519_ = lean_apply_1(v___x_3793__overap_518_, v___y_514_);
v___x_520_ = lean_apply_4(v_toBind_515_, lean_box(0), lean_box(0), v___x_519_, v___f_516_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed(lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v___x_523_, lean_object* v___x_524_, lean_object* v_snd_525_, lean_object* v_a_526_, lean_object* v___x_527_, lean_object* v___y_528_, lean_object* v_toBind_529_, lean_object* v___f_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13(v___x_521_, v___x_522_, v___x_523_, v___x_524_, v_snd_525_, v_a_526_, v___x_527_, v___y_528_, v_toBind_529_, v___f_530_, v_a_531_);
lean_dec(v___y_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(lean_object* v___f_533_, lean_object* v___x_534_, lean_object* v___y_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v_snd_540_, lean_object* v_a_541_, lean_object* v_toBind_542_, lean_object* v___f_543_, lean_object* v_fst_544_, lean_object* v_a_545_){
_start:
{
uint8_t v_enabled_546_; 
v_enabled_546_ = lean_ctor_get_uint8(v_a_545_, sizeof(void*)*3);
if (v_enabled_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec(v_fst_544_);
lean_dec(v___f_543_);
lean_dec(v_toBind_542_);
lean_dec(v_a_541_);
lean_dec(v_snd_540_);
lean_dec_ref(v___x_539_);
lean_dec_ref(v___x_538_);
lean_dec_ref(v___x_537_);
lean_dec_ref(v___x_536_);
lean_inc(v___y_535_);
v___x_547_ = lean_apply_2(v___f_533_, v___x_534_, v___y_535_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v___x_3808__overap_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec(v___f_533_);
v___x_548_ = lean_box(0);
lean_inc(v_toBind_542_);
lean_inc_n(v___y_535_, 2);
lean_inc(v_a_541_);
lean_inc_ref(v___x_539_);
lean_inc_ref(v___x_538_);
lean_inc_ref(v___x_537_);
lean_inc_ref(v___x_536_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__13___boxed), 11, 10);
lean_closure_set(v___f_549_, 0, v___x_536_);
lean_closure_set(v___f_549_, 1, v___x_537_);
lean_closure_set(v___f_549_, 2, v___x_538_);
lean_closure_set(v___f_549_, 3, v___x_539_);
lean_closure_set(v___f_549_, 4, v_snd_540_);
lean_closure_set(v___f_549_, 5, v_a_541_);
lean_closure_set(v___f_549_, 6, v___x_548_);
lean_closure_set(v___f_549_, 7, v___y_535_);
lean_closure_set(v___f_549_, 8, v_toBind_542_);
lean_closure_set(v___f_549_, 9, v___f_543_);
v___x_3808__overap_550_ = l_Lean_Elab_addConstInfo___redArg(v___x_536_, v___x_537_, v___x_538_, v___x_539_, v_fst_544_, v_a_541_, v___x_548_);
v___x_551_ = lean_apply_1(v___x_3808__overap_550_, v___y_535_);
v___x_552_ = lean_apply_4(v_toBind_542_, lean_box(0), lean_box(0), v___x_551_, v___f_549_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed(lean_object* v___f_553_, lean_object* v___x_554_, lean_object* v___y_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_snd_560_, lean_object* v_a_561_, lean_object* v_toBind_562_, lean_object* v___f_563_, lean_object* v_fst_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14(v___f_553_, v___x_554_, v___y_555_, v___x_556_, v___x_557_, v___x_558_, v___x_559_, v_snd_560_, v_a_561_, v_toBind_562_, v___f_563_, v_fst_564_, v_a_565_);
lean_dec_ref(v_a_565_);
lean_dec(v___y_555_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(lean_object* v_inst_567_, lean_object* v_snd_568_, lean_object* v_inst_569_, lean_object* v_toBind_570_, lean_object* v___f_571_, lean_object* v_reportDeprecated_572_, lean_object* v_fst_573_, lean_object* v___y_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v___x_577_, lean_object* v___x_578_, lean_object* v___x_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_getInfoState_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v_getInfoState_581_ = lean_ctor_get(v_inst_567_, 0);
lean_inc(v_getInfoState_581_);
lean_dec_ref(v_inst_567_);
lean_inc(v_fst_573_);
lean_inc_n(v_toBind_570_, 2);
lean_inc(v_a_580_);
lean_inc(v_snd_568_);
v___f_582_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_582_, 0, v_snd_568_);
lean_closure_set(v___f_582_, 1, v_a_580_);
lean_closure_set(v___f_582_, 2, v_inst_569_);
lean_closure_set(v___f_582_, 3, v_toBind_570_);
lean_closure_set(v___f_582_, 4, v___f_571_);
lean_closure_set(v___f_582_, 5, v_reportDeprecated_572_);
lean_closure_set(v___f_582_, 6, v_fst_573_);
lean_inc_n(v___y_574_, 2);
lean_inc_ref(v___f_582_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed), 3, 2);
lean_closure_set(v___f_583_, 0, v___f_582_);
lean_closure_set(v___f_583_, 1, v___y_574_);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__14___boxed), 13, 12);
lean_closure_set(v___f_584_, 0, v___f_582_);
lean_closure_set(v___f_584_, 1, v___x_575_);
lean_closure_set(v___f_584_, 2, v___y_574_);
lean_closure_set(v___f_584_, 3, v___x_576_);
lean_closure_set(v___f_584_, 4, v___x_577_);
lean_closure_set(v___f_584_, 5, v___x_578_);
lean_closure_set(v___f_584_, 6, v___x_579_);
lean_closure_set(v___f_584_, 7, v_snd_568_);
lean_closure_set(v___f_584_, 8, v_a_580_);
lean_closure_set(v___f_584_, 9, v_toBind_570_);
lean_closure_set(v___f_584_, 10, v___f_583_);
lean_closure_set(v___f_584_, 11, v_fst_573_);
v___x_585_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v_getInfoState_581_, v___f_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed(lean_object* v_inst_586_, lean_object* v_snd_587_, lean_object* v_inst_588_, lean_object* v_toBind_589_, lean_object* v___f_590_, lean_object* v_reportDeprecated_591_, lean_object* v_fst_592_, lean_object* v___y_593_, lean_object* v___x_594_, lean_object* v___x_595_, lean_object* v___x_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15(v_inst_586_, v_snd_587_, v_inst_588_, v_toBind_589_, v___f_590_, v_reportDeprecated_591_, v_fst_592_, v___y_593_, v___x_594_, v___x_595_, v___x_596_, v___x_597_, v___x_598_, v_a_599_);
lean_dec(v___y_593_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_toBind_603_, lean_object* v___f_604_, lean_object* v_reportDeprecated_605_, lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v___x_613_, lean_object* v___f_614_, lean_object* v___x_615_, lean_object* v___x_616_, lean_object* v___x_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_x_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___f_625_; lean_object* v___x_3846__overap_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_fst_623_ = lean_ctor_get(v_a_619_, 0);
lean_inc_n(v_fst_623_, 2);
v_snd_624_ = lean_ctor_get(v_a_619_, 1);
lean_inc(v_snd_624_);
lean_dec_ref(v_a_619_);
lean_inc_ref(v___x_609_);
lean_inc_ref(v___x_607_);
lean_inc_n(v___y_622_, 2);
lean_inc(v_toBind_603_);
v___f_625_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__15___boxed), 14, 13);
lean_closure_set(v___f_625_, 0, v_inst_601_);
lean_closure_set(v___f_625_, 1, v_snd_624_);
lean_closure_set(v___f_625_, 2, v_inst_602_);
lean_closure_set(v___f_625_, 3, v_toBind_603_);
lean_closure_set(v___f_625_, 4, v___f_604_);
lean_closure_set(v___f_625_, 5, v_reportDeprecated_605_);
lean_closure_set(v___f_625_, 6, v_fst_623_);
lean_closure_set(v___f_625_, 7, v___y_622_);
lean_closure_set(v___f_625_, 8, v___x_606_);
lean_closure_set(v___f_625_, 9, v___x_607_);
lean_closure_set(v___f_625_, 10, v___x_608_);
lean_closure_set(v___f_625_, 11, v___x_609_);
lean_closure_set(v___f_625_, 12, v___x_610_);
v___x_3846__overap_626_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_607_, v___x_609_, v___x_611_, v___x_612_, v___x_613_, v___f_614_, v___x_615_, v___x_616_, v___x_617_, v_a_618_, v_fst_623_);
v___x_627_ = lean_apply_1(v___x_3846__overap_626_, v___y_622_);
v___x_628_ = lean_apply_4(v_toBind_603_, lean_box(0), lean_box(0), v___x_627_, v___f_625_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_inst_629_ = _args[0];
lean_object* v_inst_630_ = _args[1];
lean_object* v_toBind_631_ = _args[2];
lean_object* v___f_632_ = _args[3];
lean_object* v_reportDeprecated_633_ = _args[4];
lean_object* v___x_634_ = _args[5];
lean_object* v___x_635_ = _args[6];
lean_object* v___x_636_ = _args[7];
lean_object* v___x_637_ = _args[8];
lean_object* v___x_638_ = _args[9];
lean_object* v___x_639_ = _args[10];
lean_object* v___x_640_ = _args[11];
lean_object* v___x_641_ = _args[12];
lean_object* v___f_642_ = _args[13];
lean_object* v___x_643_ = _args[14];
lean_object* v___x_644_ = _args[15];
lean_object* v___x_645_ = _args[16];
lean_object* v_a_646_ = _args[17];
lean_object* v_a_647_ = _args[18];
lean_object* v_x_648_ = _args[19];
lean_object* v___y_649_ = _args[20];
lean_object* v___y_650_ = _args[21];
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16(v_inst_629_, v_inst_630_, v_toBind_631_, v___f_632_, v_reportDeprecated_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v___x_638_, v___x_639_, v___x_640_, v___x_641_, v___f_642_, v___x_643_, v___x_644_, v___x_645_, v_a_646_, v_a_647_, v_x_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(lean_object* v_froms_652_, lean_object* v_tos_653_, lean_object* v_toPure_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_toBind_657_, lean_object* v_reportDeprecated_658_, lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v___x_661_, lean_object* v___x_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___f_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v_a_670_, size_t v___x_671_, lean_object* v_ref_672_, lean_object* v___f_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___f_677_; lean_object* v___f_678_; size_t v_sz_679_; lean_object* v___x_3867__overap_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_675_ = l_Array_zip___redArg(v_froms_652_, v_tos_653_);
v___x_676_ = lean_box(0);
v___f_677_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_677_, 0, v___x_676_);
lean_closure_set(v___f_677_, 1, v_toPure_654_);
lean_inc_ref(v___x_659_);
lean_inc(v_toBind_657_);
v___f_678_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__16___boxed), 22, 18);
lean_closure_set(v___f_678_, 0, v_inst_655_);
lean_closure_set(v___f_678_, 1, v_inst_656_);
lean_closure_set(v___f_678_, 2, v_toBind_657_);
lean_closure_set(v___f_678_, 3, v___f_677_);
lean_closure_set(v___f_678_, 4, v_reportDeprecated_658_);
lean_closure_set(v___f_678_, 5, v___x_676_);
lean_closure_set(v___f_678_, 6, v___x_659_);
lean_closure_set(v___f_678_, 7, v___x_660_);
lean_closure_set(v___f_678_, 8, v___x_661_);
lean_closure_set(v___f_678_, 9, v___x_662_);
lean_closure_set(v___f_678_, 10, v___x_663_);
lean_closure_set(v___f_678_, 11, v___x_664_);
lean_closure_set(v___f_678_, 12, v___x_665_);
lean_closure_set(v___f_678_, 13, v___f_666_);
lean_closure_set(v___f_678_, 14, v___x_667_);
lean_closure_set(v___f_678_, 15, v___x_668_);
lean_closure_set(v___f_678_, 16, v___x_669_);
lean_closure_set(v___f_678_, 17, v_a_670_);
v_sz_679_ = lean_array_size(v___x_675_);
v___x_3867__overap_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_659_, v___x_675_, v___f_678_, v_sz_679_, v___x_671_, v___x_676_);
v___x_681_ = lean_apply_1(v___x_3867__overap_680_, v_ref_672_);
v___x_682_ = lean_apply_4(v_toBind_657_, lean_box(0), lean_box(0), v___x_681_, v___f_673_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed(lean_object** _args){
lean_object* v_froms_683_ = _args[0];
lean_object* v_tos_684_ = _args[1];
lean_object* v_toPure_685_ = _args[2];
lean_object* v_inst_686_ = _args[3];
lean_object* v_inst_687_ = _args[4];
lean_object* v_toBind_688_ = _args[5];
lean_object* v_reportDeprecated_689_ = _args[6];
lean_object* v___x_690_ = _args[7];
lean_object* v___x_691_ = _args[8];
lean_object* v___x_692_ = _args[9];
lean_object* v___x_693_ = _args[10];
lean_object* v___x_694_ = _args[11];
lean_object* v___x_695_ = _args[12];
lean_object* v___x_696_ = _args[13];
lean_object* v___f_697_ = _args[14];
lean_object* v___x_698_ = _args[15];
lean_object* v___x_699_ = _args[16];
lean_object* v___x_700_ = _args[17];
lean_object* v_a_701_ = _args[18];
lean_object* v___x_702_ = _args[19];
lean_object* v_ref_703_ = _args[20];
lean_object* v___f_704_ = _args[21];
lean_object* v_a_705_ = _args[22];
_start:
{
size_t v___x_4760__boxed_706_; lean_object* v_res_707_; 
v___x_4760__boxed_706_ = lean_unbox_usize(v___x_702_);
lean_dec(v___x_702_);
v_res_707_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17(v_froms_683_, v_tos_684_, v_toPure_685_, v_inst_686_, v_inst_687_, v_toBind_688_, v_reportDeprecated_689_, v___x_690_, v___x_691_, v___x_692_, v___x_693_, v___x_694_, v___x_695_, v___x_696_, v___f_697_, v___x_698_, v___x_699_, v___x_700_, v_a_701_, v___x_4760__boxed_706_, v_ref_703_, v___f_704_, v_a_705_);
lean_dec_ref(v_tos_684_);
lean_dec_ref(v_froms_683_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(lean_object* v_froms_708_, lean_object* v_tos_709_, lean_object* v_toPure_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_toBind_713_, lean_object* v_reportDeprecated_714_, lean_object* v___x_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___f_722_, lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v___x_725_, size_t v___x_726_, lean_object* v_ref_727_, lean_object* v___f_728_, lean_object* v___x_729_, lean_object* v_nsStx_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_3887__overap_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = lean_box_usize(v___x_726_);
lean_inc(v_ref_727_);
lean_inc(v_a_731_);
lean_inc_ref(v___x_725_);
lean_inc_ref(v___x_724_);
lean_inc_ref(v___x_723_);
lean_inc(v___f_722_);
lean_inc_ref(v___x_717_);
lean_inc_ref(v___x_715_);
lean_inc(v_toBind_713_);
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__17___boxed), 23, 22);
lean_closure_set(v___f_733_, 0, v_froms_708_);
lean_closure_set(v___f_733_, 1, v_tos_709_);
lean_closure_set(v___f_733_, 2, v_toPure_710_);
lean_closure_set(v___f_733_, 3, v_inst_711_);
lean_closure_set(v___f_733_, 4, v_inst_712_);
lean_closure_set(v___f_733_, 5, v_toBind_713_);
lean_closure_set(v___f_733_, 6, v_reportDeprecated_714_);
lean_closure_set(v___f_733_, 7, v___x_715_);
lean_closure_set(v___f_733_, 8, v___x_716_);
lean_closure_set(v___f_733_, 9, v___x_717_);
lean_closure_set(v___f_733_, 10, v___x_718_);
lean_closure_set(v___f_733_, 11, v___x_719_);
lean_closure_set(v___f_733_, 12, v___x_720_);
lean_closure_set(v___f_733_, 13, v___x_721_);
lean_closure_set(v___f_733_, 14, v___f_722_);
lean_closure_set(v___f_733_, 15, v___x_723_);
lean_closure_set(v___f_733_, 16, v___x_724_);
lean_closure_set(v___f_733_, 17, v___x_725_);
lean_closure_set(v___f_733_, 18, v_a_731_);
lean_closure_set(v___f_733_, 19, v___x_732_);
lean_closure_set(v___f_733_, 20, v_ref_727_);
lean_closure_set(v___f_733_, 21, v___f_728_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_731_);
lean_ctor_set(v___x_734_, 1, v___x_729_);
v___x_3887__overap_735_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_715_, v___x_717_, v___x_724_, v___x_723_, v___f_722_, v___x_725_, v_nsStx_730_, v___x_734_);
v___x_736_ = lean_apply_1(v___x_3887__overap_735_, v_ref_727_);
v___x_737_ = lean_apply_4(v_toBind_713_, lean_box(0), lean_box(0), v___x_736_, v___f_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_froms_738_ = _args[0];
lean_object* v_tos_739_ = _args[1];
lean_object* v_toPure_740_ = _args[2];
lean_object* v_inst_741_ = _args[3];
lean_object* v_inst_742_ = _args[4];
lean_object* v_toBind_743_ = _args[5];
lean_object* v_reportDeprecated_744_ = _args[6];
lean_object* v___x_745_ = _args[7];
lean_object* v___x_746_ = _args[8];
lean_object* v___x_747_ = _args[9];
lean_object* v___x_748_ = _args[10];
lean_object* v___x_749_ = _args[11];
lean_object* v___x_750_ = _args[12];
lean_object* v___x_751_ = _args[13];
lean_object* v___f_752_ = _args[14];
lean_object* v___x_753_ = _args[15];
lean_object* v___x_754_ = _args[16];
lean_object* v___x_755_ = _args[17];
lean_object* v___x_756_ = _args[18];
lean_object* v_ref_757_ = _args[19];
lean_object* v___f_758_ = _args[20];
lean_object* v___x_759_ = _args[21];
lean_object* v_nsStx_760_ = _args[22];
lean_object* v_a_761_ = _args[23];
_start:
{
size_t v___x_4817__boxed_762_; lean_object* v_res_763_; 
v___x_4817__boxed_762_ = lean_unbox_usize(v___x_756_);
lean_dec(v___x_756_);
v_res_763_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18(v_froms_738_, v_tos_739_, v_toPure_740_, v_inst_741_, v_inst_742_, v_toBind_743_, v_reportDeprecated_744_, v___x_745_, v___x_746_, v___x_747_, v___x_748_, v___x_749_, v___x_750_, v___x_751_, v___f_752_, v___x_753_, v___x_754_, v___x_755_, v___x_4817__boxed_762_, v_ref_757_, v___f_758_, v___x_759_, v_nsStx_760_, v_a_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(uint8_t v___x_764_, uint8_t v___x_765_, lean_object* v_x1_766_, lean_object* v_x2_767_){
_start:
{
lean_object* v_fst_768_; uint8_t v___x_769_; 
v_fst_768_ = lean_ctor_get(v_x1_766_, 0);
v___x_769_ = lean_unbox(v_fst_768_);
if (v___x_769_ == 0)
{
lean_object* v_snd_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_x2_767_);
v_snd_770_ = lean_ctor_get(v_x1_766_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x1_766_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_x1_766_, 0);
lean_dec(v_unused_779_);
v___x_772_ = v_x1_766_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_snd_770_);
lean_dec(v_x1_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_box(v___x_764_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_snd_770_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_789_; 
v_snd_780_ = lean_ctor_get(v_x1_766_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_x1_766_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_x1_766_, 0);
lean_dec(v_unused_790_);
v___x_782_ = v_x1_766_;
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_dec(v_x1_766_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_784_ = lean_array_push(v_snd_780_, v_x2_767_);
v___x_785_ = lean_box(v___x_765_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_784_);
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_784_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed(lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v_x1_793_, lean_object* v_x2_794_){
_start:
{
uint8_t v___x_4862__boxed_795_; uint8_t v___x_4863__boxed_796_; lean_object* v_res_797_; 
v___x_4862__boxed_795_ = lean_unbox(v___x_791_);
v___x_4863__boxed_796_ = lean_unbox(v___x_792_);
v_res_797_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19(v___x_4862__boxed_795_, v___x_4863__boxed_796_, v_x1_793_, v_x2_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(lean_object* v_ids_798_, lean_object* v___f_799_, lean_object* v_a_800_, lean_object* v_inst_801_, lean_object* v_ref_802_, lean_object* v_toBind_803_, lean_object* v___f_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_806_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_807_ = lean_array_size(v_ids_798_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_806_, v___f_799_, v_sz_807_, v___x_808_, v_ids_798_);
v___x_810_ = lean_array_to_list(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v_a_800_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_801_, v___x_811_, v_ref_802_);
v___x_813_ = lean_apply_4(v_toBind_803_, lean_box(0), lean_box(0), v___x_812_, v___f_804_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed(lean_object* v_ids_814_, lean_object* v___f_815_, lean_object* v_a_816_, lean_object* v_inst_817_, lean_object* v_ref_818_, lean_object* v_toBind_819_, lean_object* v___f_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21(v_ids_814_, v___f_815_, v_a_816_, v_inst_817_, v_ref_818_, v_toBind_819_, v___f_820_, v_a_821_);
lean_dec(v_ref_818_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(lean_object* v___x_823_, lean_object* v_toPure_824_, lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v___x_827_, lean_object* v___x_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v___y_831_, lean_object* v_toBind_832_, lean_object* v___f_833_, lean_object* v_a_834_){
_start:
{
uint8_t v_enabled_835_; 
v_enabled_835_ = lean_ctor_get_uint8(v_a_834_, sizeof(void*)*3);
if (v_enabled_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v___f_833_);
lean_dec(v_toBind_832_);
lean_dec(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v___x_827_);
lean_dec_ref(v___x_826_);
lean_dec_ref(v___x_825_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_823_);
v___x_837_ = lean_apply_2(v_toPure_824_, lean_box(0), v___x_836_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_3932__overap_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_toPure_824_);
v___x_838_ = lean_box(0);
v___x_3932__overap_839_ = l_Lean_Elab_addConstInfo___redArg(v___x_825_, v___x_826_, v___x_827_, v___x_828_, v_a_829_, v_a_830_, v___x_838_);
lean_inc(v___y_831_);
v___x_840_ = lean_apply_1(v___x_3932__overap_839_, v___y_831_);
v___x_841_ = lean_apply_4(v_toBind_832_, lean_box(0), lean_box(0), v___x_840_, v___f_833_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed(lean_object* v___x_842_, lean_object* v_toPure_843_, lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v___x_846_, lean_object* v___x_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v___y_850_, lean_object* v_toBind_851_, lean_object* v___f_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22(v___x_842_, v_toPure_843_, v___x_844_, v___x_845_, v___x_846_, v___x_847_, v_a_848_, v_a_849_, v___y_850_, v_toBind_851_, v___f_852_, v_a_853_);
lean_dec_ref(v_a_853_);
lean_dec(v___y_850_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(lean_object* v_inst_855_, lean_object* v___x_856_, lean_object* v_toPure_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v___x_861_, lean_object* v_a_862_, lean_object* v___y_863_, lean_object* v_toBind_864_, lean_object* v___f_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_getInfoState_867_; lean_object* v___f_868_; lean_object* v___x_869_; 
v_getInfoState_867_ = lean_ctor_get(v_inst_855_, 0);
lean_inc(v_getInfoState_867_);
lean_dec_ref(v_inst_855_);
lean_inc(v_toBind_864_);
lean_inc(v___y_863_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__22___boxed), 12, 11);
lean_closure_set(v___f_868_, 0, v___x_856_);
lean_closure_set(v___f_868_, 1, v_toPure_857_);
lean_closure_set(v___f_868_, 2, v___x_858_);
lean_closure_set(v___f_868_, 3, v___x_859_);
lean_closure_set(v___f_868_, 4, v___x_860_);
lean_closure_set(v___f_868_, 5, v___x_861_);
lean_closure_set(v___f_868_, 6, v_a_862_);
lean_closure_set(v___f_868_, 7, v_a_866_);
lean_closure_set(v___f_868_, 8, v___y_863_);
lean_closure_set(v___f_868_, 9, v_toBind_864_);
lean_closure_set(v___f_868_, 10, v___f_865_);
v___x_869_ = lean_apply_4(v_toBind_864_, lean_box(0), lean_box(0), v_getInfoState_867_, v___f_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed(lean_object* v_inst_870_, lean_object* v___x_871_, lean_object* v_toPure_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v_a_877_, lean_object* v___y_878_, lean_object* v_toBind_879_, lean_object* v___f_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20(v_inst_870_, v___x_871_, v_toPure_872_, v___x_873_, v___x_874_, v___x_875_, v___x_876_, v_a_877_, v___y_878_, v_toBind_879_, v___f_880_, v_a_881_);
lean_dec(v___y_878_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(lean_object* v_inst_883_, lean_object* v___x_884_, lean_object* v_toPure_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_toBind_890_, lean_object* v___f_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v___x_894_, lean_object* v___f_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___f_904_; lean_object* v___x_3962__overap_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
lean_inc(v_toBind_890_);
lean_inc_n(v___y_903_, 2);
lean_inc(v_a_900_);
lean_inc_ref(v___x_888_);
lean_inc_ref(v___x_886_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__20___boxed), 12, 11);
lean_closure_set(v___f_904_, 0, v_inst_883_);
lean_closure_set(v___f_904_, 1, v___x_884_);
lean_closure_set(v___f_904_, 2, v_toPure_885_);
lean_closure_set(v___f_904_, 3, v___x_886_);
lean_closure_set(v___f_904_, 4, v___x_887_);
lean_closure_set(v___f_904_, 5, v___x_888_);
lean_closure_set(v___f_904_, 6, v___x_889_);
lean_closure_set(v___f_904_, 7, v_a_900_);
lean_closure_set(v___f_904_, 8, v___y_903_);
lean_closure_set(v___f_904_, 9, v_toBind_890_);
lean_closure_set(v___f_904_, 10, v___f_891_);
v___x_3962__overap_905_ = l_Lean_Elab_OpenDecl_resolveId___redArg(v___x_886_, v___x_888_, v___x_892_, v___x_893_, v___x_894_, v___f_895_, v___x_896_, v___x_897_, v___x_898_, v_a_899_, v_a_900_);
v___x_906_ = lean_apply_1(v___x_3962__overap_905_, v___y_903_);
v___x_907_ = lean_apply_4(v_toBind_890_, lean_box(0), lean_box(0), v___x_906_, v___f_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_inst_908_ = _args[0];
lean_object* v___x_909_ = _args[1];
lean_object* v_toPure_910_ = _args[2];
lean_object* v___x_911_ = _args[3];
lean_object* v___x_912_ = _args[4];
lean_object* v___x_913_ = _args[5];
lean_object* v___x_914_ = _args[6];
lean_object* v_toBind_915_ = _args[7];
lean_object* v___f_916_ = _args[8];
lean_object* v___x_917_ = _args[9];
lean_object* v___x_918_ = _args[10];
lean_object* v___x_919_ = _args[11];
lean_object* v___f_920_ = _args[12];
lean_object* v___x_921_ = _args[13];
lean_object* v___x_922_ = _args[14];
lean_object* v___x_923_ = _args[15];
lean_object* v_a_924_ = _args[16];
lean_object* v_a_925_ = _args[17];
lean_object* v_x_926_ = _args[18];
lean_object* v___y_927_ = _args[19];
lean_object* v___y_928_ = _args[20];
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23(v_inst_908_, v___x_909_, v_toPure_910_, v___x_911_, v___x_912_, v___x_913_, v___x_914_, v_toBind_915_, v___f_916_, v___x_917_, v___x_918_, v___x_919_, v___f_920_, v___x_921_, v___x_922_, v___x_923_, v_a_924_, v_a_925_, v_x_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(lean_object* v_toPure_930_, lean_object* v_inst_931_, lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v_toBind_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v___f_940_, lean_object* v___x_941_, lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v_a_944_, lean_object* v_ids_945_, lean_object* v_ref_946_, lean_object* v___f_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___f_951_; size_t v_sz_952_; size_t v___x_953_; lean_object* v___x_3981__overap_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_949_ = lean_box(0);
lean_inc(v_toPure_930_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_950_, 0, v___x_949_);
lean_closure_set(v___f_950_, 1, v_toPure_930_);
lean_inc(v_toBind_936_);
lean_inc_ref(v___x_932_);
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__23___boxed), 21, 17);
lean_closure_set(v___f_951_, 0, v_inst_931_);
lean_closure_set(v___f_951_, 1, v___x_949_);
lean_closure_set(v___f_951_, 2, v_toPure_930_);
lean_closure_set(v___f_951_, 3, v___x_932_);
lean_closure_set(v___f_951_, 4, v___x_933_);
lean_closure_set(v___f_951_, 5, v___x_934_);
lean_closure_set(v___f_951_, 6, v___x_935_);
lean_closure_set(v___f_951_, 7, v_toBind_936_);
lean_closure_set(v___f_951_, 8, v___f_950_);
lean_closure_set(v___f_951_, 9, v___x_937_);
lean_closure_set(v___f_951_, 10, v___x_938_);
lean_closure_set(v___f_951_, 11, v___x_939_);
lean_closure_set(v___f_951_, 12, v___f_940_);
lean_closure_set(v___f_951_, 13, v___x_941_);
lean_closure_set(v___f_951_, 14, v___x_942_);
lean_closure_set(v___f_951_, 15, v___x_943_);
lean_closure_set(v___f_951_, 16, v_a_944_);
v_sz_952_ = lean_array_size(v_ids_945_);
v___x_953_ = ((size_t)0ULL);
v___x_3981__overap_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_932_, v_ids_945_, v___f_951_, v_sz_952_, v___x_953_, v___x_949_);
v___x_955_ = lean_apply_1(v___x_3981__overap_954_, v_ref_946_);
v___x_956_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_955_, v___f_947_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed(lean_object** _args){
lean_object* v_toPure_957_ = _args[0];
lean_object* v_inst_958_ = _args[1];
lean_object* v___x_959_ = _args[2];
lean_object* v___x_960_ = _args[3];
lean_object* v___x_961_ = _args[4];
lean_object* v___x_962_ = _args[5];
lean_object* v_toBind_963_ = _args[6];
lean_object* v___x_964_ = _args[7];
lean_object* v___x_965_ = _args[8];
lean_object* v___x_966_ = _args[9];
lean_object* v___f_967_ = _args[10];
lean_object* v___x_968_ = _args[11];
lean_object* v___x_969_ = _args[12];
lean_object* v___x_970_ = _args[13];
lean_object* v_a_971_ = _args[14];
lean_object* v_ids_972_ = _args[15];
lean_object* v_ref_973_ = _args[16];
lean_object* v___f_974_ = _args[17];
lean_object* v_a_975_ = _args[18];
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24(v_toPure_957_, v_inst_958_, v___x_959_, v___x_960_, v___x_961_, v___x_962_, v_toBind_963_, v___x_964_, v___x_965_, v___x_966_, v___f_967_, v___x_968_, v___x_969_, v___x_970_, v_a_971_, v_ids_972_, v_ref_973_, v___f_974_, v_a_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25(lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v___f_979_, lean_object* v_a_980_, lean_object* v_ref_981_, lean_object* v_toBind_982_, lean_object* v___f_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_3987__overap_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_3987__overap_985_ = l_Lean_activateScoped___redArg(v___x_977_, v___x_978_, v___f_979_, v_a_980_);
v___x_986_ = lean_apply_1(v___x_3987__overap_985_, v_ref_981_);
v___x_987_ = lean_apply_4(v_toBind_982_, lean_box(0), lean_box(0), v___x_986_, v___f_983_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(lean_object* v_ids_988_, lean_object* v___f_989_, lean_object* v_inst_990_, lean_object* v_ref_991_, lean_object* v_toBind_992_, lean_object* v___f_993_, lean_object* v_toPure_994_, lean_object* v_inst_995_, lean_object* v___x_996_, lean_object* v___x_997_, lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v___x_1002_, lean_object* v___f_1003_, lean_object* v___x_1004_, lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___f_1007_, lean_object* v___x_1008_, lean_object* v_nsStx_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___x_4010__overap_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_inc_n(v_toBind_992_, 3);
lean_inc_n(v_ref_991_, 3);
lean_inc_n(v_a_1010_, 3);
lean_inc_ref(v_ids_988_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__21___boxed), 8, 7);
lean_closure_set(v___f_1011_, 0, v_ids_988_);
lean_closure_set(v___f_1011_, 1, v___f_989_);
lean_closure_set(v___f_1011_, 2, v_a_1010_);
lean_closure_set(v___f_1011_, 3, v_inst_990_);
lean_closure_set(v___f_1011_, 4, v_ref_991_);
lean_closure_set(v___f_1011_, 5, v_toBind_992_);
lean_closure_set(v___f_1011_, 6, v___f_993_);
lean_inc_ref(v___x_1006_);
lean_inc_ref(v___x_1005_);
lean_inc_ref(v___x_1004_);
lean_inc(v___f_1003_);
lean_inc_ref_n(v___x_998_, 2);
lean_inc_ref_n(v___x_996_, 2);
v___f_1012_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__24___boxed), 19, 18);
lean_closure_set(v___f_1012_, 0, v_toPure_994_);
lean_closure_set(v___f_1012_, 1, v_inst_995_);
lean_closure_set(v___f_1012_, 2, v___x_996_);
lean_closure_set(v___f_1012_, 3, v___x_997_);
lean_closure_set(v___f_1012_, 4, v___x_998_);
lean_closure_set(v___f_1012_, 5, v___x_999_);
lean_closure_set(v___f_1012_, 6, v_toBind_992_);
lean_closure_set(v___f_1012_, 7, v___x_1000_);
lean_closure_set(v___f_1012_, 8, v___x_1001_);
lean_closure_set(v___f_1012_, 9, v___x_1002_);
lean_closure_set(v___f_1012_, 10, v___f_1003_);
lean_closure_set(v___f_1012_, 11, v___x_1004_);
lean_closure_set(v___f_1012_, 12, v___x_1005_);
lean_closure_set(v___f_1012_, 13, v___x_1006_);
lean_closure_set(v___f_1012_, 14, v_a_1010_);
lean_closure_set(v___f_1012_, 15, v_ids_988_);
lean_closure_set(v___f_1012_, 16, v_ref_991_);
lean_closure_set(v___f_1012_, 17, v___f_1011_);
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__25), 8, 7);
lean_closure_set(v___f_1013_, 0, v___x_996_);
lean_closure_set(v___f_1013_, 1, v___x_998_);
lean_closure_set(v___f_1013_, 2, v___f_1007_);
lean_closure_set(v___f_1013_, 3, v_a_1010_);
lean_closure_set(v___f_1013_, 4, v_ref_991_);
lean_closure_set(v___f_1013_, 5, v_toBind_992_);
lean_closure_set(v___f_1013_, 6, v___f_1012_);
v___x_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_a_1010_);
lean_ctor_set(v___x_1014_, 1, v___x_1008_);
v___x_4010__overap_1015_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_996_, v___x_998_, v___x_1005_, v___x_1004_, v___f_1003_, v___x_1006_, v_nsStx_1009_, v___x_1014_);
v___x_1016_ = lean_apply_1(v___x_4010__overap_1015_, v_ref_991_);
v___x_1017_ = lean_apply_4(v_toBind_992_, lean_box(0), lean_box(0), v___x_1016_, v___f_1013_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed(lean_object** _args){
lean_object* v_ids_1018_ = _args[0];
lean_object* v___f_1019_ = _args[1];
lean_object* v_inst_1020_ = _args[2];
lean_object* v_ref_1021_ = _args[3];
lean_object* v_toBind_1022_ = _args[4];
lean_object* v___f_1023_ = _args[5];
lean_object* v_toPure_1024_ = _args[6];
lean_object* v_inst_1025_ = _args[7];
lean_object* v___x_1026_ = _args[8];
lean_object* v___x_1027_ = _args[9];
lean_object* v___x_1028_ = _args[10];
lean_object* v___x_1029_ = _args[11];
lean_object* v___x_1030_ = _args[12];
lean_object* v___x_1031_ = _args[13];
lean_object* v___x_1032_ = _args[14];
lean_object* v___f_1033_ = _args[15];
lean_object* v___x_1034_ = _args[16];
lean_object* v___x_1035_ = _args[17];
lean_object* v___x_1036_ = _args[18];
lean_object* v___f_1037_ = _args[19];
lean_object* v___x_1038_ = _args[20];
lean_object* v_nsStx_1039_ = _args[21];
lean_object* v_a_1040_ = _args[22];
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26(v_ids_1018_, v___f_1019_, v_inst_1020_, v_ref_1021_, v_toBind_1022_, v___f_1023_, v_toPure_1024_, v_inst_1025_, v___x_1026_, v___x_1027_, v___x_1028_, v___x_1029_, v___x_1030_, v___x_1031_, v___x_1032_, v___f_1033_, v___x_1034_, v___x_1035_, v___x_1036_, v___f_1037_, v___x_1038_, v_nsStx_1039_, v_a_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_inst_1044_, lean_object* v___y_1045_, lean_object* v_toBind_1046_, lean_object* v___f_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = l_Lean_TSyntax_getId(v_a_1042_);
v___x_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1043_);
v___x_1051_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1044_, v___x_1050_, v___y_1045_);
v___x_1052_ = lean_apply_4(v_toBind_1046_, lean_box(0), lean_box(0), v___x_1051_, v___f_1047_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed(lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_inst_1055_, lean_object* v___y_1056_, lean_object* v_toBind_1057_, lean_object* v___f_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29(v_a_1053_, v_a_1054_, v_inst_1055_, v___y_1056_, v_toBind_1057_, v___f_1058_, v_a_1059_);
lean_dec(v___y_1056_);
lean_dec(v_a_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_inst_1063_, lean_object* v_toBind_1064_, lean_object* v___f_1065_, lean_object* v_reportDeprecated_1066_, lean_object* v_____r_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_inc(v_toBind_1064_);
lean_inc(v___y_1068_);
lean_inc(v_a_1062_);
lean_inc(v_a_1061_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__29___boxed), 7, 6);
lean_closure_set(v___f_1069_, 0, v_a_1061_);
lean_closure_set(v___f_1069_, 1, v_a_1062_);
lean_closure_set(v___f_1069_, 2, v_inst_1063_);
lean_closure_set(v___f_1069_, 3, v___y_1068_);
lean_closure_set(v___f_1069_, 4, v_toBind_1064_);
lean_closure_set(v___f_1069_, 5, v___f_1065_);
v___x_1070_ = lean_apply_2(v_reportDeprecated_1066_, v_a_1061_, v_a_1062_);
v___x_1071_ = lean_apply_4(v_toBind_1064_, lean_box(0), lean_box(0), v___x_1070_, v___f_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed(lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_inst_1074_, lean_object* v_toBind_1075_, lean_object* v___f_1076_, lean_object* v_reportDeprecated_1077_, lean_object* v_____r_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27(v_a_1072_, v_a_1073_, v_inst_1074_, v_toBind_1075_, v___f_1076_, v_reportDeprecated_1077_, v_____r_1078_, v___y_1079_);
lean_dec(v___y_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(lean_object* v___f_1081_, lean_object* v___x_1082_, lean_object* v___y_1083_, lean_object* v___x_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_toBind_1090_, lean_object* v___f_1091_, lean_object* v_a_1092_){
_start:
{
uint8_t v_enabled_1093_; 
v_enabled_1093_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
if (v_enabled_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec(v___f_1091_);
lean_dec(v_toBind_1090_);
lean_dec(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v___x_1087_);
lean_dec_ref(v___x_1086_);
lean_dec_ref(v___x_1085_);
lean_dec_ref(v___x_1084_);
lean_inc(v___y_1083_);
v___x_1094_ = lean_apply_2(v___f_1081_, v___x_1082_, v___y_1083_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; lean_object* v___x_4045__overap_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v___f_1081_);
v___x_1095_ = lean_box(0);
v___x_4045__overap_1096_ = l_Lean_Elab_addConstInfo___redArg(v___x_1084_, v___x_1085_, v___x_1086_, v___x_1087_, v_a_1088_, v_a_1089_, v___x_1095_);
lean_inc(v___y_1083_);
v___x_1097_ = lean_apply_1(v___x_4045__overap_1096_, v___y_1083_);
v___x_1098_ = lean_apply_4(v_toBind_1090_, lean_box(0), lean_box(0), v___x_1097_, v___f_1091_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed(lean_object* v___f_1099_, lean_object* v___x_1100_, lean_object* v___y_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_toBind_1108_, lean_object* v___f_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30(v___f_1099_, v___x_1100_, v___y_1101_, v___x_1102_, v___x_1103_, v___x_1104_, v___x_1105_, v_a_1106_, v_a_1107_, v_toBind_1108_, v___f_1109_, v_a_1110_);
lean_dec_ref(v_a_1110_);
lean_dec(v___y_1101_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(lean_object* v_inst_1112_, lean_object* v_a_1113_, lean_object* v_inst_1114_, lean_object* v_toBind_1115_, lean_object* v___f_1116_, lean_object* v_reportDeprecated_1117_, lean_object* v___y_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v___x_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_getInfoState_1125_; lean_object* v___f_1126_; lean_object* v___f_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; 
v_getInfoState_1125_ = lean_ctor_get(v_inst_1112_, 0);
lean_inc(v_getInfoState_1125_);
lean_dec_ref(v_inst_1112_);
lean_inc_n(v_toBind_1115_, 2);
lean_inc(v_a_1124_);
lean_inc(v_a_1113_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__27___boxed), 8, 6);
lean_closure_set(v___f_1126_, 0, v_a_1113_);
lean_closure_set(v___f_1126_, 1, v_a_1124_);
lean_closure_set(v___f_1126_, 2, v_inst_1114_);
lean_closure_set(v___f_1126_, 3, v_toBind_1115_);
lean_closure_set(v___f_1126_, 4, v___f_1116_);
lean_closure_set(v___f_1126_, 5, v_reportDeprecated_1117_);
lean_inc_n(v___y_1118_, 2);
lean_inc_ref(v___f_1126_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__12___boxed), 3, 2);
lean_closure_set(v___f_1127_, 0, v___f_1126_);
lean_closure_set(v___f_1127_, 1, v___y_1118_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__30___boxed), 12, 11);
lean_closure_set(v___f_1128_, 0, v___f_1126_);
lean_closure_set(v___f_1128_, 1, v___x_1119_);
lean_closure_set(v___f_1128_, 2, v___y_1118_);
lean_closure_set(v___f_1128_, 3, v___x_1120_);
lean_closure_set(v___f_1128_, 4, v___x_1121_);
lean_closure_set(v___f_1128_, 5, v___x_1122_);
lean_closure_set(v___f_1128_, 6, v___x_1123_);
lean_closure_set(v___f_1128_, 7, v_a_1113_);
lean_closure_set(v___f_1128_, 8, v_a_1124_);
lean_closure_set(v___f_1128_, 9, v_toBind_1115_);
lean_closure_set(v___f_1128_, 10, v___f_1127_);
v___x_1129_ = lean_apply_4(v_toBind_1115_, lean_box(0), lean_box(0), v_getInfoState_1125_, v___f_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed(lean_object* v_inst_1130_, lean_object* v_a_1131_, lean_object* v_inst_1132_, lean_object* v_toBind_1133_, lean_object* v___f_1134_, lean_object* v_reportDeprecated_1135_, lean_object* v___y_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v___x_1139_, lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28(v_inst_1130_, v_a_1131_, v_inst_1132_, v_toBind_1133_, v___f_1134_, v_reportDeprecated_1135_, v___y_1136_, v___x_1137_, v___x_1138_, v___x_1139_, v___x_1140_, v___x_1141_, v_a_1142_);
lean_dec(v___y_1136_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_toBind_1146_, lean_object* v___f_1147_, lean_object* v_reportDeprecated_1148_, lean_object* v___x_1149_, lean_object* v___x_1150_, lean_object* v___x_1151_, lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v___f_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v___x_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___x_4079__overap_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v___x_1152_);
lean_inc_ref(v___x_1150_);
lean_inc_n(v___y_1165_, 2);
lean_inc(v_toBind_1146_);
lean_inc(v_a_1162_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__28___boxed), 13, 12);
lean_closure_set(v___f_1166_, 0, v_inst_1144_);
lean_closure_set(v___f_1166_, 1, v_a_1162_);
lean_closure_set(v___f_1166_, 2, v_inst_1145_);
lean_closure_set(v___f_1166_, 3, v_toBind_1146_);
lean_closure_set(v___f_1166_, 4, v___f_1147_);
lean_closure_set(v___f_1166_, 5, v_reportDeprecated_1148_);
lean_closure_set(v___f_1166_, 6, v___y_1165_);
lean_closure_set(v___f_1166_, 7, v___x_1149_);
lean_closure_set(v___f_1166_, 8, v___x_1150_);
lean_closure_set(v___f_1166_, 9, v___x_1151_);
lean_closure_set(v___f_1166_, 10, v___x_1152_);
lean_closure_set(v___f_1166_, 11, v___x_1153_);
v___x_4079__overap_1167_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1150_, v___x_1152_, v___x_1154_, v___x_1155_, v___x_1156_, v___f_1157_, v___x_1158_, v___x_1159_, v___x_1160_, v_a_1161_, v_a_1162_);
v___x_1168_ = lean_apply_1(v___x_4079__overap_1167_, v___y_1165_);
v___x_1169_ = lean_apply_4(v_toBind_1146_, lean_box(0), lean_box(0), v___x_1168_, v___f_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_inst_1170_ = _args[0];
lean_object* v_inst_1171_ = _args[1];
lean_object* v_toBind_1172_ = _args[2];
lean_object* v___f_1173_ = _args[3];
lean_object* v_reportDeprecated_1174_ = _args[4];
lean_object* v___x_1175_ = _args[5];
lean_object* v___x_1176_ = _args[6];
lean_object* v___x_1177_ = _args[7];
lean_object* v___x_1178_ = _args[8];
lean_object* v___x_1179_ = _args[9];
lean_object* v___x_1180_ = _args[10];
lean_object* v___x_1181_ = _args[11];
lean_object* v___x_1182_ = _args[12];
lean_object* v___f_1183_ = _args[13];
lean_object* v___x_1184_ = _args[14];
lean_object* v___x_1185_ = _args[15];
lean_object* v___x_1186_ = _args[16];
lean_object* v_a_1187_ = _args[17];
lean_object* v_a_1188_ = _args[18];
lean_object* v_x_1189_ = _args[19];
lean_object* v___y_1190_ = _args[20];
lean_object* v___y_1191_ = _args[21];
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31(v_inst_1170_, v_inst_1171_, v_toBind_1172_, v___f_1173_, v_reportDeprecated_1174_, v___x_1175_, v___x_1176_, v___x_1177_, v___x_1178_, v___x_1179_, v___x_1180_, v___x_1181_, v___x_1182_, v___f_1183_, v___x_1184_, v___x_1185_, v___x_1186_, v_a_1187_, v_a_1188_, v_x_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(lean_object* v_toPure_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_toBind_1196_, lean_object* v_reportDeprecated_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v___f_1205_, lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_a_1209_, lean_object* v_ids_1210_, lean_object* v_ref_1211_, lean_object* v___f_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; size_t v_sz_1217_; size_t v___x_1218_; lean_object* v___x_4099__overap_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = lean_box(0);
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1215_, 0, v___x_1214_);
lean_closure_set(v___f_1215_, 1, v_toPure_1193_);
lean_inc_ref(v___x_1198_);
lean_inc(v_toBind_1196_);
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__31___boxed), 22, 18);
lean_closure_set(v___f_1216_, 0, v_inst_1194_);
lean_closure_set(v___f_1216_, 1, v_inst_1195_);
lean_closure_set(v___f_1216_, 2, v_toBind_1196_);
lean_closure_set(v___f_1216_, 3, v___f_1215_);
lean_closure_set(v___f_1216_, 4, v_reportDeprecated_1197_);
lean_closure_set(v___f_1216_, 5, v___x_1214_);
lean_closure_set(v___f_1216_, 6, v___x_1198_);
lean_closure_set(v___f_1216_, 7, v___x_1199_);
lean_closure_set(v___f_1216_, 8, v___x_1200_);
lean_closure_set(v___f_1216_, 9, v___x_1201_);
lean_closure_set(v___f_1216_, 10, v___x_1202_);
lean_closure_set(v___f_1216_, 11, v___x_1203_);
lean_closure_set(v___f_1216_, 12, v___x_1204_);
lean_closure_set(v___f_1216_, 13, v___f_1205_);
lean_closure_set(v___f_1216_, 14, v___x_1206_);
lean_closure_set(v___f_1216_, 15, v___x_1207_);
lean_closure_set(v___f_1216_, 16, v___x_1208_);
lean_closure_set(v___f_1216_, 17, v_a_1209_);
v_sz_1217_ = lean_array_size(v_ids_1210_);
v___x_1218_ = ((size_t)0ULL);
v___x_4099__overap_1219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v_ids_1210_, v___f_1216_, v_sz_1217_, v___x_1218_, v___x_1214_);
v___x_1220_ = lean_apply_1(v___x_4099__overap_1219_, v_ref_1211_);
v___x_1221_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v___x_1220_, v___f_1212_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed(lean_object** _args){
lean_object* v_toPure_1222_ = _args[0];
lean_object* v_inst_1223_ = _args[1];
lean_object* v_inst_1224_ = _args[2];
lean_object* v_toBind_1225_ = _args[3];
lean_object* v_reportDeprecated_1226_ = _args[4];
lean_object* v___x_1227_ = _args[5];
lean_object* v___x_1228_ = _args[6];
lean_object* v___x_1229_ = _args[7];
lean_object* v___x_1230_ = _args[8];
lean_object* v___x_1231_ = _args[9];
lean_object* v___x_1232_ = _args[10];
lean_object* v___x_1233_ = _args[11];
lean_object* v___f_1234_ = _args[12];
lean_object* v___x_1235_ = _args[13];
lean_object* v___x_1236_ = _args[14];
lean_object* v___x_1237_ = _args[15];
lean_object* v_a_1238_ = _args[16];
lean_object* v_ids_1239_ = _args[17];
lean_object* v_ref_1240_ = _args[18];
lean_object* v___f_1241_ = _args[19];
lean_object* v_a_1242_ = _args[20];
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32(v_toPure_1222_, v_inst_1223_, v_inst_1224_, v_toBind_1225_, v_reportDeprecated_1226_, v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_, v___x_1231_, v___x_1232_, v___x_1233_, v___f_1234_, v___x_1235_, v___x_1236_, v___x_1237_, v_a_1238_, v_ids_1239_, v_ref_1240_, v___f_1241_, v_a_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(lean_object* v_toPure_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_toBind_1247_, lean_object* v_reportDeprecated_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v___x_1251_, lean_object* v___x_1252_, lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v___f_1256_, lean_object* v___x_1257_, lean_object* v___x_1258_, lean_object* v___x_1259_, lean_object* v_ids_1260_, lean_object* v_ref_1261_, lean_object* v___f_1262_, lean_object* v_ns_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___f_1265_; lean_object* v___x_4116__overap_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_inc(v_ref_1261_);
lean_inc(v_a_1264_);
lean_inc_ref(v___x_1259_);
lean_inc_ref(v___x_1258_);
lean_inc_ref(v___x_1257_);
lean_inc(v___f_1256_);
lean_inc_ref(v___x_1251_);
lean_inc_ref(v___x_1249_);
lean_inc(v_toBind_1247_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__32___boxed), 21, 20);
lean_closure_set(v___f_1265_, 0, v_toPure_1244_);
lean_closure_set(v___f_1265_, 1, v_inst_1245_);
lean_closure_set(v___f_1265_, 2, v_inst_1246_);
lean_closure_set(v___f_1265_, 3, v_toBind_1247_);
lean_closure_set(v___f_1265_, 4, v_reportDeprecated_1248_);
lean_closure_set(v___f_1265_, 5, v___x_1249_);
lean_closure_set(v___f_1265_, 6, v___x_1250_);
lean_closure_set(v___f_1265_, 7, v___x_1251_);
lean_closure_set(v___f_1265_, 8, v___x_1252_);
lean_closure_set(v___f_1265_, 9, v___x_1253_);
lean_closure_set(v___f_1265_, 10, v___x_1254_);
lean_closure_set(v___f_1265_, 11, v___x_1255_);
lean_closure_set(v___f_1265_, 12, v___f_1256_);
lean_closure_set(v___f_1265_, 13, v___x_1257_);
lean_closure_set(v___f_1265_, 14, v___x_1258_);
lean_closure_set(v___f_1265_, 15, v___x_1259_);
lean_closure_set(v___f_1265_, 16, v_a_1264_);
lean_closure_set(v___f_1265_, 17, v_ids_1260_);
lean_closure_set(v___f_1265_, 18, v_ref_1261_);
lean_closure_set(v___f_1265_, 19, v___f_1262_);
v___x_4116__overap_1266_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1249_, v___x_1251_, v___x_1258_, v___x_1257_, v___f_1256_, v___x_1259_, v_ns_1263_, v_a_1264_);
v___x_1267_ = lean_apply_1(v___x_4116__overap_1266_, v_ref_1261_);
v___x_1268_ = lean_apply_4(v_toBind_1247_, lean_box(0), lean_box(0), v___x_1267_, v___f_1265_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed(lean_object** _args){
lean_object* v_toPure_1269_ = _args[0];
lean_object* v_inst_1270_ = _args[1];
lean_object* v_inst_1271_ = _args[2];
lean_object* v_toBind_1272_ = _args[3];
lean_object* v_reportDeprecated_1273_ = _args[4];
lean_object* v___x_1274_ = _args[5];
lean_object* v___x_1275_ = _args[6];
lean_object* v___x_1276_ = _args[7];
lean_object* v___x_1277_ = _args[8];
lean_object* v___x_1278_ = _args[9];
lean_object* v___x_1279_ = _args[10];
lean_object* v___x_1280_ = _args[11];
lean_object* v___f_1281_ = _args[12];
lean_object* v___x_1282_ = _args[13];
lean_object* v___x_1283_ = _args[14];
lean_object* v___x_1284_ = _args[15];
lean_object* v_ids_1285_ = _args[16];
lean_object* v_ref_1286_ = _args[17];
lean_object* v___f_1287_ = _args[18];
lean_object* v_ns_1288_ = _args[19];
lean_object* v_a_1289_ = _args[20];
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33(v_toPure_1269_, v_inst_1270_, v_inst_1271_, v_toBind_1272_, v_reportDeprecated_1273_, v___x_1274_, v___x_1275_, v___x_1276_, v___x_1277_, v___x_1278_, v___x_1279_, v___x_1280_, v___f_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v_ids_1285_, v_ref_1286_, v___f_1287_, v_ns_1288_, v_a_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v___f_1293_, lean_object* v_toBind_1294_, lean_object* v___f_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_4131__overap_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_4131__overap_1300_ = l_Lean_activateScoped___redArg(v___x_1291_, v___x_1292_, v___f_1293_, v_a_1296_);
lean_inc(v___y_1299_);
v___x_1301_ = lean_apply_1(v___x_4131__overap_1300_, v___y_1299_);
v___x_1302_ = lean_apply_4(v_toBind_1294_, lean_box(0), lean_box(0), v___x_1301_, v___f_1295_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed(lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___f_1305_, lean_object* v_toBind_1306_, lean_object* v___f_1307_, lean_object* v_a_1308_, lean_object* v_x_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36(v___x_1303_, v___x_1304_, v___f_1305_, v_toBind_1306_, v___f_1307_, v_a_1308_, v_x_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(lean_object* v___x_1313_, lean_object* v___f_1314_, lean_object* v_a_1315_, lean_object* v___x_1316_, lean_object* v___y_1317_, lean_object* v_toBind_1318_, lean_object* v___f_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_4141__overap_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_4141__overap_1321_ = l_List_forIn_x27_loop___redArg(v___x_1313_, v___f_1314_, v_a_1315_, v___x_1316_);
lean_inc(v___y_1317_);
v___x_1322_ = lean_apply_1(v___x_4141__overap_1321_, v___y_1317_);
v___x_1323_ = lean_apply_4(v_toBind_1318_, lean_box(0), lean_box(0), v___x_1322_, v___f_1319_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed(lean_object* v___x_1324_, lean_object* v___f_1325_, lean_object* v_a_1326_, lean_object* v___x_1327_, lean_object* v___y_1328_, lean_object* v_toBind_1329_, lean_object* v___f_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35(v___x_1324_, v___f_1325_, v_a_1326_, v___x_1327_, v___y_1328_, v_toBind_1329_, v___f_1330_, v_a_1331_);
lean_dec(v___y_1328_);
lean_dec(v_a_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(lean_object* v___x_1333_, lean_object* v___f_1334_, lean_object* v___x_1335_, lean_object* v___y_1336_, lean_object* v_toBind_1337_, lean_object* v___f_1338_, lean_object* v___x_1339_, lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___f_1342_, lean_object* v___x_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___f_1346_; lean_object* v___x_4154__overap_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_inc(v_toBind_1337_);
lean_inc_n(v___y_1336_, 2);
lean_inc(v_a_1345_);
lean_inc_ref(v___x_1333_);
v___f_1346_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__35___boxed), 8, 7);
lean_closure_set(v___f_1346_, 0, v___x_1333_);
lean_closure_set(v___f_1346_, 1, v___f_1334_);
lean_closure_set(v___f_1346_, 2, v_a_1345_);
lean_closure_set(v___f_1346_, 3, v___x_1335_);
lean_closure_set(v___f_1346_, 4, v___y_1336_);
lean_closure_set(v___f_1346_, 5, v_toBind_1337_);
lean_closure_set(v___f_1346_, 6, v___f_1338_);
v___x_4154__overap_1347_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v___x_1333_, v___x_1339_, v___x_1340_, v___x_1341_, v___f_1342_, v___x_1343_, v_a_1344_, v_a_1345_);
v___x_1348_ = lean_apply_1(v___x_4154__overap_1347_, v___y_1336_);
v___x_1349_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v___x_1348_, v___f_1346_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed(lean_object* v___x_1350_, lean_object* v___f_1351_, lean_object* v___x_1352_, lean_object* v___y_1353_, lean_object* v_toBind_1354_, lean_object* v___f_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v___f_1359_, lean_object* v___x_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34(v___x_1350_, v___f_1351_, v___x_1352_, v___y_1353_, v_toBind_1354_, v___f_1355_, v___x_1356_, v___x_1357_, v___x_1358_, v___f_1359_, v___x_1360_, v_a_1361_, v_a_1362_);
lean_dec(v___y_1353_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(lean_object* v___x_1364_, lean_object* v___f_1365_, lean_object* v___x_1366_, lean_object* v_toBind_1367_, lean_object* v___f_1368_, lean_object* v___x_1369_, lean_object* v___x_1370_, lean_object* v___x_1371_, lean_object* v___f_1372_, lean_object* v___x_1373_, lean_object* v___x_1374_, lean_object* v_a_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___f_1379_; lean_object* v___x_4170__overap_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_inc(v_a_1375_);
lean_inc_ref(v___x_1373_);
lean_inc_ref(v___x_1369_);
lean_inc(v_toBind_1367_);
lean_inc_n(v___y_1378_, 2);
lean_inc_ref(v___x_1364_);
v___f_1379_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__34___boxed), 13, 12);
lean_closure_set(v___f_1379_, 0, v___x_1364_);
lean_closure_set(v___f_1379_, 1, v___f_1365_);
lean_closure_set(v___f_1379_, 2, v___x_1366_);
lean_closure_set(v___f_1379_, 3, v___y_1378_);
lean_closure_set(v___f_1379_, 4, v_toBind_1367_);
lean_closure_set(v___f_1379_, 5, v___f_1368_);
lean_closure_set(v___f_1379_, 6, v___x_1369_);
lean_closure_set(v___f_1379_, 7, v___x_1370_);
lean_closure_set(v___f_1379_, 8, v___x_1371_);
lean_closure_set(v___f_1379_, 9, v___f_1372_);
lean_closure_set(v___f_1379_, 10, v___x_1373_);
lean_closure_set(v___f_1379_, 11, v_a_1375_);
v___x_4170__overap_1380_ = l_Lean_resolveNamespace___redArg(v___x_1364_, v___x_1373_, v___x_1369_, v___x_1374_, v_a_1375_);
v___x_1381_ = lean_apply_1(v___x_4170__overap_1380_, v___y_1378_);
v___x_1382_ = lean_apply_4(v_toBind_1367_, lean_box(0), lean_box(0), v___x_1381_, v___f_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed(lean_object* v___x_1383_, lean_object* v___f_1384_, lean_object* v___x_1385_, lean_object* v_toBind_1386_, lean_object* v___f_1387_, lean_object* v___x_1388_, lean_object* v___x_1389_, lean_object* v___x_1390_, lean_object* v___f_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v_a_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37(v___x_1383_, v___f_1384_, v___x_1385_, v_toBind_1386_, v___f_1387_, v___x_1388_, v___x_1389_, v___x_1390_, v___f_1391_, v___x_1392_, v___x_1393_, v_a_1394_, v_x_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(lean_object* v___x_1399_, lean_object* v___x_1400_, lean_object* v___f_1401_, lean_object* v_a_1402_, lean_object* v___y_1403_, lean_object* v_toBind_1404_, lean_object* v___f_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_4183__overap_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_4183__overap_1407_ = l_Lean_activateScoped___redArg(v___x_1399_, v___x_1400_, v___f_1401_, v_a_1402_);
lean_inc(v___y_1403_);
v___x_1408_ = lean_apply_1(v___x_4183__overap_1407_, v___y_1403_);
v___x_1409_ = lean_apply_4(v_toBind_1404_, lean_box(0), lean_box(0), v___x_1408_, v___f_1405_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed(lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___f_1412_, lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v_toBind_1415_, lean_object* v___f_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40(v___x_1410_, v___x_1411_, v___f_1412_, v_a_1413_, v___y_1414_, v_toBind_1415_, v___f_1416_, v_a_1417_);
lean_dec(v___y_1414_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v___f_1421_, lean_object* v_toBind_1422_, lean_object* v___f_1423_, lean_object* v___x_1424_, lean_object* v_inst_1425_, lean_object* v_a_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___f_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_inc(v_toBind_1422_);
lean_inc(v___y_1429_);
lean_inc(v_a_1426_);
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__40___boxed), 8, 7);
lean_closure_set(v___f_1430_, 0, v___x_1419_);
lean_closure_set(v___f_1430_, 1, v___x_1420_);
lean_closure_set(v___f_1430_, 2, v___f_1421_);
lean_closure_set(v___f_1430_, 3, v_a_1426_);
lean_closure_set(v___f_1430_, 4, v___y_1429_);
lean_closure_set(v___f_1430_, 5, v_toBind_1422_);
lean_closure_set(v___f_1430_, 6, v___f_1423_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_a_1426_);
lean_ctor_set(v___x_1431_, 1, v___x_1424_);
v___x_1432_ = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___redArg(v_inst_1425_, v___x_1431_, v___y_1429_);
v___x_1433_ = lean_apply_4(v_toBind_1422_, lean_box(0), lean_box(0), v___x_1432_, v___f_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed(lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v___f_1436_, lean_object* v_toBind_1437_, lean_object* v___f_1438_, lean_object* v___x_1439_, lean_object* v_inst_1440_, lean_object* v_a_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38(v___x_1434_, v___x_1435_, v___f_1436_, v_toBind_1437_, v___f_1438_, v___x_1439_, v_inst_1440_, v_a_1441_, v_x_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44(lean_object* v_toPure_1454_, lean_object* v_inst_1455_, lean_object* v_toBind_1456_, uint8_t v___x_1457_, lean_object* v___x_1458_, lean_object* v___x_1459_, lean_object* v___x_1460_, lean_object* v_stx_1461_, lean_object* v___f_1462_, lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v___f_1465_, lean_object* v___f_1466_, lean_object* v_inst_1467_, lean_object* v_reportDeprecated_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v___f_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___f_1479_, lean_object* v___f_1480_, lean_object* v_ref_1481_){
_start:
{
lean_object* v___f_1482_; 
lean_inc(v_toBind_1456_);
lean_inc(v_inst_1455_);
lean_inc(v_ref_1481_);
lean_inc(v_toPure_1454_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__5), 5, 4);
lean_closure_set(v___f_1482_, 0, v_toPure_1454_);
lean_closure_set(v___f_1482_, 1, v_ref_1481_);
lean_closure_set(v___f_1482_, 2, v_inst_1455_);
lean_closure_set(v___f_1482_, 3, v_toBind_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__0));
lean_inc_ref(v___x_1460_);
lean_inc_ref(v___x_1459_);
lean_inc_ref(v___x_1458_);
v___x_1484_ = l_Lean_Name_mkStr4(v___x_1458_, v___x_1459_, v___x_1460_, v___x_1483_);
lean_inc(v_stx_1461_);
v___x_1485_ = l_Lean_Syntax_isOfKind(v_stx_1461_, v___x_1484_);
lean_dec(v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1486_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__1));
lean_inc_ref(v___x_1460_);
lean_inc_ref(v___x_1459_);
lean_inc_ref(v___x_1458_);
v___x_1487_ = l_Lean_Name_mkStr4(v___x_1458_, v___x_1459_, v___x_1460_, v___x_1486_);
lean_inc(v_stx_1461_);
v___x_1488_ = l_Lean_Syntax_isOfKind(v_stx_1461_, v___x_1487_);
lean_dec(v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__2));
lean_inc_ref(v___x_1460_);
lean_inc_ref(v___x_1459_);
lean_inc_ref(v___x_1458_);
v___x_1490_ = l_Lean_Name_mkStr4(v___x_1458_, v___x_1459_, v___x_1460_, v___x_1489_);
lean_inc(v_stx_1461_);
v___x_1491_ = l_Lean_Syntax_isOfKind(v_stx_1461_, v___x_1490_);
lean_dec(v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
lean_dec(v___f_1480_);
lean_dec_ref(v___f_1479_);
v___x_1492_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__3));
lean_inc_ref(v___x_1460_);
lean_inc_ref(v___x_1459_);
lean_inc_ref(v___x_1458_);
v___x_1493_ = l_Lean_Name_mkStr4(v___x_1458_, v___x_1459_, v___x_1460_, v___x_1492_);
lean_inc(v_stx_1461_);
v___x_1494_ = l_Lean_Syntax_isOfKind(v_stx_1461_, v___x_1493_);
lean_dec(v___x_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___f_1495_; lean_object* v___x_4274__overap_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v___x_1476_);
lean_dec(v___f_1475_);
lean_dec(v___x_1474_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v___x_1469_);
lean_dec(v_reportDeprecated_1468_);
lean_dec_ref(v_inst_1467_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1464_);
lean_dec(v_stx_1461_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___x_1458_);
lean_dec(v_inst_1455_);
lean_dec(v_toPure_1454_);
lean_inc(v_ref_1481_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1495_, 0, v___f_1462_);
lean_closure_set(v___f_1495_, 1, v_ref_1481_);
v___x_4274__overap_1496_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1463_);
v___x_1497_ = lean_apply_1(v___x_4274__overap_1496_, v_ref_1481_);
lean_inc(v_toBind_1456_);
v___x_1498_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1497_, v___f_1495_);
v___x_1499_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1498_, v___f_1482_);
return v___x_1499_;
}
else
{
lean_object* v___f_1500_; lean_object* v___f_1501_; lean_object* v___x_1502_; lean_object* v_nsStx_1503_; lean_object* v___x_1504_; lean_object* v___f_1505_; lean_object* v___y_1507_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
lean_inc_n(v_ref_1481_, 2);
lean_inc(v___f_1462_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1500_, 0, v___f_1462_);
lean_closure_set(v___f_1500_, 1, v_ref_1481_);
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1501_, 0, v___f_1462_);
lean_closure_set(v___f_1501_, 1, v_ref_1481_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v_nsStx_1503_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1502_);
v___x_1504_ = lean_unsigned_to_nat(2u);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1505_, 0, v___x_1458_);
lean_closure_set(v___f_1505_, 1, v___x_1459_);
lean_closure_set(v___f_1505_, 2, v___x_1460_);
lean_closure_set(v___f_1505_, 3, v___x_1502_);
lean_closure_set(v___f_1505_, 4, v___x_1504_);
v___x_1527_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1504_);
lean_dec(v_stx_1461_);
v___x_1528_ = l_Lean_Syntax_getArgs(v___x_1527_);
lean_dec(v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___closed__4));
v___x_1530_ = lean_array_get_size(v___x_1528_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v___x_1532_ = lean_nat_dec_lt(v___x_1502_, v___x_1530_);
if (v___x_1532_ == 0)
{
lean_dec_ref(v___x_1528_);
v___y_1507_ = v___x_1529_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; lean_object* v_snd_1541_; 
v___x_1533_ = lean_box(v___x_1494_);
v___x_1534_ = lean_box(v___x_1491_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__19___boxed), 4, 2);
lean_closure_set(v___f_1535_, 0, v___x_1533_);
lean_closure_set(v___f_1535_, 1, v___x_1534_);
v___x_1536_ = lean_box(v___x_1532_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1529_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = lean_usize_of_nat(v___x_1530_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1531_, v___f_1535_, v___x_1528_, v___x_1538_, v___x_1539_, v___x_1537_);
v_snd_1541_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_snd_1541_);
lean_dec(v___x_1540_);
v___y_1507_ = v_snd_1541_;
goto v___jp_1506_;
}
v___jp_1506_:
{
size_t v_sz_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v_sz_1508_ = lean_array_size(v___y_1507_);
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1464_, v___f_1505_, v_sz_1508_, v___x_1509_, v___y_1507_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_4286__overap_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_nsStx_1503_);
lean_dec_ref(v___f_1500_);
lean_dec_ref(v___x_1478_);
lean_dec_ref(v___x_1477_);
lean_dec_ref(v___x_1476_);
lean_dec(v___f_1475_);
lean_dec(v___x_1474_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1472_);
lean_dec_ref(v___x_1471_);
lean_dec_ref(v___x_1470_);
lean_dec_ref(v___x_1469_);
lean_dec(v_reportDeprecated_1468_);
lean_dec_ref(v_inst_1467_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec(v_inst_1455_);
lean_dec(v_toPure_1454_);
v___x_4286__overap_1511_ = l_Lean_Elab_throwUnsupportedSyntax___redArg(v___x_1463_);
v___x_1512_ = lean_apply_1(v___x_4286__overap_1511_, v_ref_1481_);
lean_inc(v_toBind_1456_);
v___x_1513_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1512_, v___f_1501_);
v___x_1514_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1513_, v___f_1482_);
return v___x_1514_;
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1516_; size_t v_sz_1517_; lean_object* v_tos_1518_; lean_object* v_froms_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___f_1522_; lean_object* v___x_4302__overap_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v___f_1501_);
v_val_1515_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_n(v_val_1515_, 2);
lean_dec_ref_known(v___x_1510_, 1);
v___x_1516_ = ((lean_object*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg___lam__6___closed__9));
v_sz_1517_ = lean_array_size(v_val_1515_);
v_tos_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v___f_1465_, v_sz_1517_, v___x_1509_, v_val_1515_);
v_froms_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v___f_1466_, v_sz_1517_, v___x_1509_, v_val_1515_);
v___x_1520_ = lean_box(0);
v___x_1521_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed__const__1));
lean_inc(v_nsStx_1503_);
lean_inc(v_ref_1481_);
lean_inc_ref(v___x_1478_);
lean_inc_ref(v___x_1472_);
lean_inc_ref(v___x_1471_);
lean_inc_ref(v___x_1469_);
lean_inc_n(v_toBind_1456_, 2);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__18___boxed), 24, 23);
lean_closure_set(v___f_1522_, 0, v_froms_1519_);
lean_closure_set(v___f_1522_, 1, v_tos_1518_);
lean_closure_set(v___f_1522_, 2, v_toPure_1454_);
lean_closure_set(v___f_1522_, 3, v_inst_1467_);
lean_closure_set(v___f_1522_, 4, v_inst_1455_);
lean_closure_set(v___f_1522_, 5, v_toBind_1456_);
lean_closure_set(v___f_1522_, 6, v_reportDeprecated_1468_);
lean_closure_set(v___f_1522_, 7, v___x_1469_);
lean_closure_set(v___f_1522_, 8, v___x_1470_);
lean_closure_set(v___f_1522_, 9, v___x_1471_);
lean_closure_set(v___f_1522_, 10, v___x_1472_);
lean_closure_set(v___f_1522_, 11, v___x_1463_);
lean_closure_set(v___f_1522_, 12, v___x_1473_);
lean_closure_set(v___f_1522_, 13, v___x_1474_);
lean_closure_set(v___f_1522_, 14, v___f_1475_);
lean_closure_set(v___f_1522_, 15, v___x_1476_);
lean_closure_set(v___f_1522_, 16, v___x_1477_);
lean_closure_set(v___f_1522_, 17, v___x_1478_);
lean_closure_set(v___f_1522_, 18, v___x_1521_);
lean_closure_set(v___f_1522_, 19, v_ref_1481_);
lean_closure_set(v___f_1522_, 20, v___f_1500_);
lean_closure_set(v___f_1522_, 21, v___x_1520_);
lean_closure_set(v___f_1522_, 22, v_nsStx_1503_);
v___x_4302__overap_1523_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1469_, v___x_1478_, v___x_1471_, v___x_1472_, v_nsStx_1503_);
v___x_1524_ = lean_apply_1(v___x_4302__overap_1523_, v_ref_1481_);
v___x_1525_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1524_, v___f_1522_);
v___x_1526_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1525_, v___f_1482_);
return v___x_1526_;
}
}
}
}
else
{
lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v_nsStx_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_ids_1548_; lean_object* v___f_1549_; lean_object* v___x_4331__overap_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_reportDeprecated_1468_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___x_1458_);
lean_inc_n(v_ref_1481_, 2);
v___f_1542_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__6), 3, 2);
lean_closure_set(v___f_1542_, 0, v___f_1462_);
lean_closure_set(v___f_1542_, 1, v_ref_1481_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v_nsStx_1544_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1543_);
v___x_1545_ = lean_unsigned_to_nat(2u);
v___x_1546_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1545_);
lean_dec(v_stx_1461_);
v___x_1547_ = lean_box(0);
v_ids_1548_ = l_Lean_Syntax_getArgs(v___x_1546_);
lean_dec(v___x_1546_);
lean_inc(v_nsStx_1544_);
lean_inc_ref(v___x_1478_);
lean_inc_ref(v___x_1472_);
lean_inc_ref(v___x_1471_);
lean_inc_ref(v___x_1469_);
lean_inc_n(v_toBind_1456_, 2);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__26___boxed), 23, 22);
lean_closure_set(v___f_1549_, 0, v_ids_1548_);
lean_closure_set(v___f_1549_, 1, v___f_1479_);
lean_closure_set(v___f_1549_, 2, v_inst_1455_);
lean_closure_set(v___f_1549_, 3, v_ref_1481_);
lean_closure_set(v___f_1549_, 4, v_toBind_1456_);
lean_closure_set(v___f_1549_, 5, v___f_1542_);
lean_closure_set(v___f_1549_, 6, v_toPure_1454_);
lean_closure_set(v___f_1549_, 7, v_inst_1467_);
lean_closure_set(v___f_1549_, 8, v___x_1469_);
lean_closure_set(v___f_1549_, 9, v___x_1470_);
lean_closure_set(v___f_1549_, 10, v___x_1471_);
lean_closure_set(v___f_1549_, 11, v___x_1472_);
lean_closure_set(v___f_1549_, 12, v___x_1463_);
lean_closure_set(v___f_1549_, 13, v___x_1473_);
lean_closure_set(v___f_1549_, 14, v___x_1474_);
lean_closure_set(v___f_1549_, 15, v___f_1475_);
lean_closure_set(v___f_1549_, 16, v___x_1476_);
lean_closure_set(v___f_1549_, 17, v___x_1477_);
lean_closure_set(v___f_1549_, 18, v___x_1478_);
lean_closure_set(v___f_1549_, 19, v___f_1480_);
lean_closure_set(v___f_1549_, 20, v___x_1547_);
lean_closure_set(v___f_1549_, 21, v_nsStx_1544_);
v___x_4331__overap_1550_ = l_Lean_resolveUniqueNamespace___redArg(v___x_1469_, v___x_1478_, v___x_1471_, v___x_1472_, v_nsStx_1544_);
v___x_1551_ = lean_apply_1(v___x_4331__overap_1550_, v_ref_1481_);
v___x_1552_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1551_, v___f_1549_);
v___x_1553_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1552_, v___f_1482_);
return v___x_1553_;
}
}
else
{
lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v_ns_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_ids_1559_; lean_object* v___f_1560_; lean_object* v___x_4339__overap_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v___f_1480_);
lean_dec_ref(v___f_1479_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___x_1458_);
lean_inc_n(v_ref_1481_, 2);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1554_, 0, v___f_1462_);
lean_closure_set(v___f_1554_, 1, v_ref_1481_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v_ns_1556_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1555_);
v___x_1557_ = lean_unsigned_to_nat(2u);
v___x_1558_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1557_);
lean_dec(v_stx_1461_);
v_ids_1559_ = l_Lean_Syntax_getArgs(v___x_1558_);
lean_dec(v___x_1558_);
lean_inc(v_ns_1556_);
lean_inc_ref(v___x_1478_);
lean_inc_ref(v___x_1472_);
lean_inc_ref(v___x_1471_);
lean_inc_ref(v___x_1469_);
lean_inc_n(v_toBind_1456_, 2);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__33___boxed), 21, 20);
lean_closure_set(v___f_1560_, 0, v_toPure_1454_);
lean_closure_set(v___f_1560_, 1, v_inst_1467_);
lean_closure_set(v___f_1560_, 2, v_inst_1455_);
lean_closure_set(v___f_1560_, 3, v_toBind_1456_);
lean_closure_set(v___f_1560_, 4, v_reportDeprecated_1468_);
lean_closure_set(v___f_1560_, 5, v___x_1469_);
lean_closure_set(v___f_1560_, 6, v___x_1470_);
lean_closure_set(v___f_1560_, 7, v___x_1471_);
lean_closure_set(v___f_1560_, 8, v___x_1472_);
lean_closure_set(v___f_1560_, 9, v___x_1463_);
lean_closure_set(v___f_1560_, 10, v___x_1473_);
lean_closure_set(v___f_1560_, 11, v___x_1474_);
lean_closure_set(v___f_1560_, 12, v___f_1475_);
lean_closure_set(v___f_1560_, 13, v___x_1476_);
lean_closure_set(v___f_1560_, 14, v___x_1477_);
lean_closure_set(v___f_1560_, 15, v___x_1478_);
lean_closure_set(v___f_1560_, 16, v_ids_1559_);
lean_closure_set(v___f_1560_, 17, v_ref_1481_);
lean_closure_set(v___f_1560_, 18, v___f_1554_);
lean_closure_set(v___f_1560_, 19, v_ns_1556_);
v___x_4339__overap_1561_ = l_Lean_resolveNamespace___redArg(v___x_1469_, v___x_1478_, v___x_1471_, v___x_1472_, v_ns_1556_);
v___x_1562_ = lean_apply_1(v___x_4339__overap_1561_, v_ref_1481_);
v___x_1563_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1562_, v___f_1560_);
v___x_1564_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1563_, v___f_1482_);
return v___x_1564_;
}
}
else
{
lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_nss_1568_; lean_object* v___x_1569_; lean_object* v___f_1570_; lean_object* v___f_1571_; lean_object* v___f_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_4351__overap_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref(v___f_1479_);
lean_dec(v___x_1474_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1470_);
lean_dec(v_reportDeprecated_1468_);
lean_dec_ref(v_inst_1467_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___x_1458_);
lean_dec(v_inst_1455_);
lean_inc(v_ref_1481_);
v___f_1565_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1565_, 0, v___f_1462_);
lean_closure_set(v___f_1565_, 1, v_ref_1481_);
v___x_1566_ = lean_unsigned_to_nat(1u);
v___x_1567_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1566_);
lean_dec(v_stx_1461_);
v_nss_1568_ = l_Lean_Syntax_getArgs(v___x_1567_);
lean_dec(v___x_1567_);
v___x_1569_ = lean_box(0);
v___f_1570_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1570_, 0, v___x_1569_);
lean_closure_set(v___f_1570_, 1, v_toPure_1454_);
lean_inc_ref(v___f_1570_);
lean_inc_n(v_toBind_1456_, 3);
lean_inc_ref(v___x_1471_);
lean_inc_ref_n(v___x_1469_, 2);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__36___boxed), 9, 5);
lean_closure_set(v___f_1571_, 0, v___x_1469_);
lean_closure_set(v___f_1571_, 1, v___x_1471_);
lean_closure_set(v___f_1571_, 2, v___f_1480_);
lean_closure_set(v___f_1571_, 3, v_toBind_1456_);
lean_closure_set(v___f_1571_, 4, v___f_1570_);
v___f_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed), 15, 11);
lean_closure_set(v___f_1572_, 0, v___x_1469_);
lean_closure_set(v___f_1572_, 1, v___f_1571_);
lean_closure_set(v___f_1572_, 2, v___x_1569_);
lean_closure_set(v___f_1572_, 3, v_toBind_1456_);
lean_closure_set(v___f_1572_, 4, v___f_1570_);
lean_closure_set(v___f_1572_, 5, v___x_1471_);
lean_closure_set(v___f_1572_, 6, v___x_1477_);
lean_closure_set(v___f_1572_, 7, v___x_1476_);
lean_closure_set(v___f_1572_, 8, v___f_1475_);
lean_closure_set(v___f_1572_, 9, v___x_1478_);
lean_closure_set(v___f_1572_, 10, v___x_1472_);
v_sz_1573_ = lean_array_size(v_nss_1568_);
v___x_1574_ = ((size_t)0ULL);
v___x_4351__overap_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1469_, v_nss_1568_, v___f_1572_, v_sz_1573_, v___x_1574_, v___x_1569_);
v___x_1576_ = lean_apply_1(v___x_4351__overap_1575_, v_ref_1481_);
v___x_1577_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1576_, v___f_1565_);
v___x_1578_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1577_, v___f_1482_);
return v___x_1578_;
}
}
else
{
lean_object* v___f_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_nss_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___f_1586_; lean_object* v___f_1587_; size_t v_sz_1588_; size_t v___x_1589_; lean_object* v___x_4364__overap_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v___f_1479_);
lean_dec(v___x_1474_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1470_);
lean_dec(v_reportDeprecated_1468_);
lean_dec_ref(v_inst_1467_);
lean_dec_ref(v___f_1466_);
lean_dec_ref(v___f_1465_);
lean_dec_ref(v___x_1464_);
lean_dec_ref(v___x_1463_);
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___x_1458_);
lean_inc(v_ref_1481_);
v___f_1579_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__7), 3, 2);
lean_closure_set(v___f_1579_, 0, v___f_1462_);
lean_closure_set(v___f_1579_, 1, v_ref_1481_);
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = l_Lean_Syntax_getArg(v_stx_1461_, v___x_1580_);
lean_dec(v_stx_1461_);
v___x_1582_ = lean_box(0);
v_nss_1583_ = l_Lean_Syntax_getArgs(v___x_1581_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__8), 3, 2);
lean_closure_set(v___f_1585_, 0, v___x_1584_);
lean_closure_set(v___f_1585_, 1, v_toPure_1454_);
lean_inc_ref(v___f_1585_);
lean_inc_n(v_toBind_1456_, 3);
lean_inc_ref(v___x_1471_);
lean_inc_ref_n(v___x_1469_, 2);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__38___boxed), 11, 7);
lean_closure_set(v___f_1586_, 0, v___x_1469_);
lean_closure_set(v___f_1586_, 1, v___x_1471_);
lean_closure_set(v___f_1586_, 2, v___f_1480_);
lean_closure_set(v___f_1586_, 3, v_toBind_1456_);
lean_closure_set(v___f_1586_, 4, v___f_1585_);
lean_closure_set(v___f_1586_, 5, v___x_1582_);
lean_closure_set(v___f_1586_, 6, v_inst_1455_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__37___boxed), 15, 11);
lean_closure_set(v___f_1587_, 0, v___x_1469_);
lean_closure_set(v___f_1587_, 1, v___f_1586_);
lean_closure_set(v___f_1587_, 2, v___x_1584_);
lean_closure_set(v___f_1587_, 3, v_toBind_1456_);
lean_closure_set(v___f_1587_, 4, v___f_1585_);
lean_closure_set(v___f_1587_, 5, v___x_1471_);
lean_closure_set(v___f_1587_, 6, v___x_1477_);
lean_closure_set(v___f_1587_, 7, v___x_1476_);
lean_closure_set(v___f_1587_, 8, v___f_1475_);
lean_closure_set(v___f_1587_, 9, v___x_1478_);
lean_closure_set(v___f_1587_, 10, v___x_1472_);
v_sz_1588_ = lean_array_size(v_nss_1583_);
v___x_1589_ = ((size_t)0ULL);
v___x_4364__overap_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1469_, v_nss_1583_, v___f_1587_, v_sz_1588_, v___x_1589_, v___x_1584_);
v___x_1591_ = lean_apply_1(v___x_4364__overap_1590_, v_ref_1481_);
v___x_1592_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1591_, v___f_1579_);
v___x_1593_ = lean_apply_4(v_toBind_1456_, lean_box(0), lean_box(0), v___x_1592_, v___f_1482_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed(lean_object** _args){
lean_object* v_toPure_1594_ = _args[0];
lean_object* v_inst_1595_ = _args[1];
lean_object* v_toBind_1596_ = _args[2];
lean_object* v___x_1597_ = _args[3];
lean_object* v___x_1598_ = _args[4];
lean_object* v___x_1599_ = _args[5];
lean_object* v___x_1600_ = _args[6];
lean_object* v_stx_1601_ = _args[7];
lean_object* v___f_1602_ = _args[8];
lean_object* v___x_1603_ = _args[9];
lean_object* v___x_1604_ = _args[10];
lean_object* v___f_1605_ = _args[11];
lean_object* v___f_1606_ = _args[12];
lean_object* v_inst_1607_ = _args[13];
lean_object* v_reportDeprecated_1608_ = _args[14];
lean_object* v___x_1609_ = _args[15];
lean_object* v___x_1610_ = _args[16];
lean_object* v___x_1611_ = _args[17];
lean_object* v___x_1612_ = _args[18];
lean_object* v___x_1613_ = _args[19];
lean_object* v___x_1614_ = _args[20];
lean_object* v___f_1615_ = _args[21];
lean_object* v___x_1616_ = _args[22];
lean_object* v___x_1617_ = _args[23];
lean_object* v___x_1618_ = _args[24];
lean_object* v___f_1619_ = _args[25];
lean_object* v___f_1620_ = _args[26];
lean_object* v_ref_1621_ = _args[27];
_start:
{
uint8_t v___x_5707__boxed_1622_; lean_object* v_res_1623_; 
v___x_5707__boxed_1622_ = lean_unbox(v___x_1597_);
v_res_1623_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44(v_toPure_1594_, v_inst_1595_, v_toBind_1596_, v___x_5707__boxed_1622_, v___x_1598_, v___x_1599_, v___x_1600_, v_stx_1601_, v___f_1602_, v___x_1603_, v___x_1604_, v___f_1605_, v___f_1606_, v_inst_1607_, v_reportDeprecated_1608_, v___x_1609_, v___x_1610_, v___x_1611_, v___x_1612_, v___x_1613_, v___x_1614_, v___f_1615_, v___x_1616_, v___x_1617_, v___x_1618_, v___f_1619_, v___f_1620_, v_ref_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39(lean_object* v_toPure_1624_, lean_object* v_____x_1625_){
_start:
{
lean_object* v_fst_1626_; lean_object* v___x_1627_; 
v_fst_1626_ = lean_ctor_get(v_____x_1625_, 0);
lean_inc(v_fst_1626_);
lean_dec_ref(v_____x_1625_);
v___x_1627_ = lean_apply_2(v_toPure_1624_, lean_box(0), v_fst_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(lean_object* v_toApplicative_1637_, lean_object* v_stx_1638_, lean_object* v_____do__lift_1639_, lean_object* v_inst_1640_, lean_object* v_toBind_1641_, lean_object* v___f_1642_, lean_object* v___x_1643_, lean_object* v___x_1644_, lean_object* v___f_1645_, lean_object* v___f_1646_, lean_object* v_inst_1647_, lean_object* v_reportDeprecated_1648_, lean_object* v___x_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, lean_object* v___f_1655_, lean_object* v___x_1656_, lean_object* v___x_1657_, lean_object* v___x_1658_, lean_object* v___f_1659_, lean_object* v___f_1660_, lean_object* v_____do__lift_1661_){
_start:
{
lean_object* v_toPure_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_toPure_1662_ = lean_ctor_get(v_toApplicative_1637_, 1);
lean_inc_n(v_toPure_1662_, 2);
lean_dec_ref(v_toApplicative_1637_);
v___x_1663_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__0));
v___x_1664_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__1));
v___x_1665_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__2));
v___x_1666_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___closed__4));
lean_inc(v_stx_1638_);
v___x_1667_ = l_Lean_Syntax_isOfKind(v_stx_1638_, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v_____do__lift_1639_);
lean_ctor_set(v___x_1668_, 1, v_____do__lift_1661_);
v___x_1669_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1669_, 0, lean_box(0));
lean_closure_set(v___x_1669_, 1, lean_box(0));
lean_closure_set(v___x_1669_, 2, v___x_1668_);
lean_inc(v_inst_1640_);
v___x_1670_ = lean_apply_2(v_inst_1640_, lean_box(0), v___x_1669_);
v___x_1671_ = lean_box(v___x_1667_);
lean_inc_n(v_toBind_1641_, 2);
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__44___boxed), 28, 27);
lean_closure_set(v___f_1672_, 0, v_toPure_1662_);
lean_closure_set(v___f_1672_, 1, v_inst_1640_);
lean_closure_set(v___f_1672_, 2, v_toBind_1641_);
lean_closure_set(v___f_1672_, 3, v___x_1671_);
lean_closure_set(v___f_1672_, 4, v___x_1663_);
lean_closure_set(v___f_1672_, 5, v___x_1664_);
lean_closure_set(v___f_1672_, 6, v___x_1665_);
lean_closure_set(v___f_1672_, 7, v_stx_1638_);
lean_closure_set(v___f_1672_, 8, v___f_1642_);
lean_closure_set(v___f_1672_, 9, v___x_1643_);
lean_closure_set(v___f_1672_, 10, v___x_1644_);
lean_closure_set(v___f_1672_, 11, v___f_1645_);
lean_closure_set(v___f_1672_, 12, v___f_1646_);
lean_closure_set(v___f_1672_, 13, v_inst_1647_);
lean_closure_set(v___f_1672_, 14, v_reportDeprecated_1648_);
lean_closure_set(v___f_1672_, 15, v___x_1649_);
lean_closure_set(v___f_1672_, 16, v___x_1650_);
lean_closure_set(v___f_1672_, 17, v___x_1651_);
lean_closure_set(v___f_1672_, 18, v___x_1652_);
lean_closure_set(v___f_1672_, 19, v___x_1653_);
lean_closure_set(v___f_1672_, 20, v___x_1654_);
lean_closure_set(v___f_1672_, 21, v___f_1655_);
lean_closure_set(v___f_1672_, 22, v___x_1656_);
lean_closure_set(v___f_1672_, 23, v___x_1657_);
lean_closure_set(v___f_1672_, 24, v___x_1658_);
lean_closure_set(v___f_1672_, 25, v___f_1659_);
lean_closure_set(v___f_1672_, 26, v___f_1660_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__39), 2, 1);
lean_closure_set(v___f_1673_, 0, v_toPure_1662_);
v___x_1674_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1670_, v___f_1672_);
v___x_1675_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1674_, v___f_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed(lean_object** _args){
lean_object* v_toApplicative_1676_ = _args[0];
lean_object* v_stx_1677_ = _args[1];
lean_object* v_____do__lift_1678_ = _args[2];
lean_object* v_inst_1679_ = _args[3];
lean_object* v_toBind_1680_ = _args[4];
lean_object* v___f_1681_ = _args[5];
lean_object* v___x_1682_ = _args[6];
lean_object* v___x_1683_ = _args[7];
lean_object* v___f_1684_ = _args[8];
lean_object* v___f_1685_ = _args[9];
lean_object* v_inst_1686_ = _args[10];
lean_object* v_reportDeprecated_1687_ = _args[11];
lean_object* v___x_1688_ = _args[12];
lean_object* v___x_1689_ = _args[13];
lean_object* v___x_1690_ = _args[14];
lean_object* v___x_1691_ = _args[15];
lean_object* v___x_1692_ = _args[16];
lean_object* v___x_1693_ = _args[17];
lean_object* v___f_1694_ = _args[18];
lean_object* v___x_1695_ = _args[19];
lean_object* v___x_1696_ = _args[20];
lean_object* v___x_1697_ = _args[21];
lean_object* v___f_1698_ = _args[22];
lean_object* v___f_1699_ = _args[23];
lean_object* v_____do__lift_1700_ = _args[24];
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41(v_toApplicative_1676_, v_stx_1677_, v_____do__lift_1678_, v_inst_1679_, v_toBind_1680_, v___f_1681_, v___x_1682_, v___x_1683_, v___f_1684_, v___f_1685_, v_inst_1686_, v_reportDeprecated_1687_, v___x_1688_, v___x_1689_, v___x_1690_, v___x_1691_, v___x_1692_, v___x_1693_, v___f_1694_, v___x_1695_, v___x_1696_, v___x_1697_, v___f_1698_, v___f_1699_, v_____do__lift_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(lean_object* v_toApplicative_1702_, lean_object* v_stx_1703_, lean_object* v_inst_1704_, lean_object* v_toBind_1705_, lean_object* v___f_1706_, lean_object* v___x_1707_, lean_object* v___x_1708_, lean_object* v___f_1709_, lean_object* v___f_1710_, lean_object* v_inst_1711_, lean_object* v_reportDeprecated_1712_, lean_object* v___x_1713_, lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v___f_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v___f_1723_, lean_object* v___f_1724_, lean_object* v_getCurrNamespace_1725_, lean_object* v_____do__lift_1726_){
_start:
{
lean_object* v___f_1727_; lean_object* v___x_1728_; 
lean_inc(v_toBind_1705_);
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__41___boxed), 25, 24);
lean_closure_set(v___f_1727_, 0, v_toApplicative_1702_);
lean_closure_set(v___f_1727_, 1, v_stx_1703_);
lean_closure_set(v___f_1727_, 2, v_____do__lift_1726_);
lean_closure_set(v___f_1727_, 3, v_inst_1704_);
lean_closure_set(v___f_1727_, 4, v_toBind_1705_);
lean_closure_set(v___f_1727_, 5, v___f_1706_);
lean_closure_set(v___f_1727_, 6, v___x_1707_);
lean_closure_set(v___f_1727_, 7, v___x_1708_);
lean_closure_set(v___f_1727_, 8, v___f_1709_);
lean_closure_set(v___f_1727_, 9, v___f_1710_);
lean_closure_set(v___f_1727_, 10, v_inst_1711_);
lean_closure_set(v___f_1727_, 11, v_reportDeprecated_1712_);
lean_closure_set(v___f_1727_, 12, v___x_1713_);
lean_closure_set(v___f_1727_, 13, v___x_1714_);
lean_closure_set(v___f_1727_, 14, v___x_1715_);
lean_closure_set(v___f_1727_, 15, v___x_1716_);
lean_closure_set(v___f_1727_, 16, v___x_1717_);
lean_closure_set(v___f_1727_, 17, v___x_1718_);
lean_closure_set(v___f_1727_, 18, v___f_1719_);
lean_closure_set(v___f_1727_, 19, v___x_1720_);
lean_closure_set(v___f_1727_, 20, v___x_1721_);
lean_closure_set(v___f_1727_, 21, v___x_1722_);
lean_closure_set(v___f_1727_, 22, v___f_1723_);
lean_closure_set(v___f_1727_, 23, v___f_1724_);
v___x_1728_ = lean_apply_4(v_toBind_1705_, lean_box(0), lean_box(0), v_getCurrNamespace_1725_, v___f_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed(lean_object** _args){
lean_object* v_toApplicative_1729_ = _args[0];
lean_object* v_stx_1730_ = _args[1];
lean_object* v_inst_1731_ = _args[2];
lean_object* v_toBind_1732_ = _args[3];
lean_object* v___f_1733_ = _args[4];
lean_object* v___x_1734_ = _args[5];
lean_object* v___x_1735_ = _args[6];
lean_object* v___f_1736_ = _args[7];
lean_object* v___f_1737_ = _args[8];
lean_object* v_inst_1738_ = _args[9];
lean_object* v_reportDeprecated_1739_ = _args[10];
lean_object* v___x_1740_ = _args[11];
lean_object* v___x_1741_ = _args[12];
lean_object* v___x_1742_ = _args[13];
lean_object* v___x_1743_ = _args[14];
lean_object* v___x_1744_ = _args[15];
lean_object* v___x_1745_ = _args[16];
lean_object* v___f_1746_ = _args[17];
lean_object* v___x_1747_ = _args[18];
lean_object* v___x_1748_ = _args[19];
lean_object* v___x_1749_ = _args[20];
lean_object* v___f_1750_ = _args[21];
lean_object* v___f_1751_ = _args[22];
lean_object* v_getCurrNamespace_1752_ = _args[23];
lean_object* v_____do__lift_1753_ = _args[24];
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42(v_toApplicative_1729_, v_stx_1730_, v_inst_1731_, v_toBind_1732_, v___f_1733_, v___x_1734_, v___x_1735_, v___f_1736_, v___f_1737_, v_inst_1738_, v_reportDeprecated_1739_, v___x_1740_, v___x_1741_, v___x_1742_, v___x_1743_, v___x_1744_, v___x_1745_, v___f_1746_, v___x_1747_, v___x_1748_, v___x_1749_, v___f_1750_, v___f_1751_, v_getCurrNamespace_1752_, v_____do__lift_1753_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_stx_1789_, lean_object* v_reportDeprecated_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v_toApplicative_1792_; lean_object* v_toBind_1793_; lean_object* v_getCurrNamespace_1794_; lean_object* v_getOpenDecls_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1834_; 
v___x_1791_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__9));
v_toApplicative_1792_ = lean_ctor_get(v_inst_1779_, 0);
lean_inc_ref(v_toApplicative_1792_);
v_toBind_1793_ = lean_ctor_get(v_inst_1779_, 1);
lean_inc(v_toBind_1793_);
v_getCurrNamespace_1794_ = lean_ctor_get(v_inst_1787_, 0);
v_getOpenDecls_1795_ = lean_ctor_get(v_inst_1787_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_inst_1787_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1797_ = v_inst_1787_;
v_isShared_1798_ = v_isSharedCheck_1834_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_getOpenDecls_1795_);
lean_inc(v_getCurrNamespace_1794_);
lean_dec(v_inst_1787_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1834_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___f_1801_; lean_object* v___x_1803_; 
lean_inc_ref(v_inst_1779_);
v___x_1799_ = l_StateRefT_x27_instMonad___redArg(v_inst_1779_);
lean_inc_ref(v_inst_1781_);
v___f_1800_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1800_, 0, v_inst_1781_);
v___f_1801_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1801_, 0, v_inst_1781_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 1, v___f_1801_);
lean_ctor_set(v___x_1797_, 0, v___f_1800_);
v___x_1803_ = v___x_1797_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___f_1800_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___f_1801_);
v___x_1803_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v_getEnv_1805_; lean_object* v_modifyEnv_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1832_; 
lean_inc(v_inst_1784_);
v___x_1804_ = l_Lean_Elab_OpenDecl_instMonadResolveNameM___redArg(v_inst_1779_, v_inst_1784_);
v_getEnv_1805_ = lean_ctor_get(v_inst_1780_, 0);
v_modifyEnv_1806_ = lean_ctor_get(v_inst_1780_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_inst_1780_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1808_ = v_inst_1780_;
v_isShared_1809_ = v_isSharedCheck_1832_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_modifyEnv_1806_);
lean_inc(v_getEnv_1805_);
lean_dec(v_inst_1780_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1832_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___f_1810_; lean_object* v___f_1811_; lean_object* v___f_1812_; lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_inc_ref(v_toApplicative_1792_);
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1810_, 0, v_toApplicative_1792_);
lean_inc(v_toBind_1793_);
lean_inc(v_inst_1784_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1811_, 0, v_inst_1784_);
lean_closure_set(v___f_1811_, 1, v_toBind_1793_);
lean_closure_set(v___f_1811_, 2, v___f_1810_);
v___f_1812_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__10));
v___f_1813_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__11));
v___f_1814_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__12));
v___x_1815_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1816_, 0, v_modifyEnv_1806_);
lean_closure_set(v___f_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_1817_, 0, lean_box(0));
lean_closure_set(v___x_1817_, 1, lean_box(0));
lean_closure_set(v___x_1817_, 2, lean_box(0));
lean_closure_set(v___x_1817_, 3, lean_box(0));
lean_closure_set(v___x_1817_, 4, v_getEnv_1805_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v___f_1816_);
lean_ctor_set(v___x_1808_, 0, v___x_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___f_1816_);
v___x_1819_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v___x_1820_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_1821_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_1815_, v___x_1820_, v_inst_1782_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1822_, 0, v_inst_1783_);
lean_closure_set(v___f_1822_, 1, v___x_1815_);
lean_inc_ref(v___x_1799_);
lean_inc_ref(v___f_1822_);
v___x_1823_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_1822_, v___x_1799_);
lean_inc(v___x_1823_);
lean_inc_ref(v___x_1821_);
lean_inc_ref(v___x_1803_);
v___x_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1803_);
lean_ctor_set(v___x_1824_, 1, v___x_1821_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
v___x_1825_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_1815_, v_inst_1786_);
v___x_1826_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_1815_, v_inst_1785_);
lean_inc_ref(v_inst_1788_);
v___x_1827_ = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(v___x_1815_, v_inst_1788_);
lean_inc(v_inst_1784_);
v___f_1828_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1828_, 0, v_inst_1784_);
lean_closure_set(v___f_1828_, 1, v___x_1815_);
lean_inc(v_toBind_1793_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___lam__42___boxed), 25, 24);
lean_closure_set(v___f_1829_, 0, v_toApplicative_1792_);
lean_closure_set(v___f_1829_, 1, v_stx_1789_);
lean_closure_set(v___f_1829_, 2, v_inst_1784_);
lean_closure_set(v___f_1829_, 3, v_toBind_1793_);
lean_closure_set(v___f_1829_, 4, v___f_1811_);
lean_closure_set(v___f_1829_, 5, v___x_1803_);
lean_closure_set(v___f_1829_, 6, v___x_1791_);
lean_closure_set(v___f_1829_, 7, v___f_1814_);
lean_closure_set(v___f_1829_, 8, v___f_1813_);
lean_closure_set(v___f_1829_, 9, v_inst_1788_);
lean_closure_set(v___f_1829_, 10, v_reportDeprecated_1790_);
lean_closure_set(v___f_1829_, 11, v___x_1799_);
lean_closure_set(v___f_1829_, 12, v___x_1827_);
lean_closure_set(v___f_1829_, 13, v___x_1819_);
lean_closure_set(v___f_1829_, 14, v___x_1824_);
lean_closure_set(v___f_1829_, 15, v___x_1821_);
lean_closure_set(v___f_1829_, 16, v___x_1823_);
lean_closure_set(v___f_1829_, 17, v___f_1822_);
lean_closure_set(v___f_1829_, 18, v___x_1826_);
lean_closure_set(v___f_1829_, 19, v___x_1825_);
lean_closure_set(v___f_1829_, 20, v___x_1804_);
lean_closure_set(v___f_1829_, 21, v___f_1812_);
lean_closure_set(v___f_1829_, 22, v___f_1828_);
lean_closure_set(v___f_1829_, 23, v_getCurrNamespace_1794_);
v___x_1830_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v_getOpenDecls_1795_, v___f_1829_);
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl(lean_object* v_m_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_stx_1846_, lean_object* v_reportDeprecated_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Elab_OpenDecl_elabOpenDecl___redArg(v_inst_1836_, v_inst_1837_, v_inst_1838_, v_inst_1839_, v_inst_1840_, v_inst_1841_, v_inst_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_stx_1846_, v_reportDeprecated_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0(lean_object* v_ns_1849_, lean_object* v_idStx_1850_, lean_object* v_newName_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Name_isPrefixOf(v_ns_1849_, v_newName_1851_);
if (v___x_1860_ == 0)
{
lean_dec(v_newName_1851_);
lean_dec(v_idStx_1850_);
goto v___jp_1857_;
}
else
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_name_eq(v_newName_1851_, v_ns_1849_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = lean_box(0);
v___x_1863_ = l_Lean_Name_replacePrefix(v_newName_1851_, v_ns_1849_, v___x_1862_);
v___x_1864_ = l_Lean_Name_toString(v___x_1863_, v___x_1860_);
v___x_1865_ = l_Lean_Linter_mkReplacementHint___redArg(v_idStx_1850_, v___x_1864_, v___y_1854_, v___y_1855_);
return v___x_1865_;
}
else
{
lean_dec(v_newName_1851_);
lean_dec(v_idStx_1850_);
goto v___jp_1857_;
}
}
v___jp_1857_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = l_Lean_MessageData_nil;
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0___boxed(lean_object* v_ns_1866_, lean_object* v_idStx_1867_, lean_object* v_newName_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0(v_ns_1866_, v_idStx_1867_, v_newName_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v_ns_1866_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0(lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
return v_x_1875_;
}
else
{
lean_object* v_tail_1877_; lean_object* v___x_1878_; 
v_tail_1877_ = lean_ctor_get(v_x_1876_, 1);
v___x_1878_ = l_Lean_Name_getPrefix(v_x_1875_);
lean_dec(v_x_1875_);
v_x_1875_ = v___x_1878_;
v_x_1876_ = v_tail_1877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0___boxed(lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0(v_x_1880_, v_x_1881_);
lean_dec(v_x_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName(lean_object* v_idStx_1883_, lean_object* v_declName_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_numParts_1892_; lean_object* v___x_1893_; lean_object* v_ns_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1890_ = l_Lean_Syntax_getId(v_idStx_1883_);
v___x_1891_ = l_Lean_Name_eraseMacroScopes(v___x_1890_);
lean_dec(v___x_1890_);
v_numParts_1892_ = l_Lean_Name_getNumParts(v___x_1891_);
lean_dec(v___x_1891_);
v___x_1893_ = l_List_range(v_numParts_1892_);
lean_inc(v_declName_1884_);
v_ns_1894_ = l_List_foldl___at___00Lean_Elab_OpenDecl_checkDeprecatedOpenedName_spec__0(v_declName_1884_, v___x_1893_);
lean_dec(v___x_1893_);
lean_inc(v_idStx_1883_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1895_, 0, v_ns_1894_);
lean_closure_set(v___f_1895_, 1, v_idStx_1883_);
v___x_1896_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___f_1895_);
v___x_1897_ = l_Lean_Linter_checkDeprecatedAt(v_idStx_1883_, v_declName_1884_, v___x_1896_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_idStx_1883_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName___boxed(lean_object* v_idStx_1898_, lean_object* v_declName_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Elab_OpenDecl_checkDeprecatedOpenedName(v_idStx_1898_, v_declName_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
return v_res_1905_;
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
lean_object* v___f_1935_; lean_object* v___x_107__overap_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_inc(v_toBind_1922_);
lean_inc(v_ref_1934_);
v___f_1935_ = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1935_, 0, v_toPure_1920_);
lean_closure_set(v___f_1935_, 1, v_ref_1934_);
lean_closure_set(v___f_1935_, 2, v_inst_1921_);
lean_closure_set(v___f_1935_, 3, v_toBind_1922_);
v___x_107__overap_1936_ = l_Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___redArg(v___x_1923_, v___x_1924_, v___x_1925_, v___x_1926_, v___x_1927_, v___f_1928_, v___x_1929_, v___x_1930_, v___x_1931_, v_nss_1932_, v_idStx_1933_);
v___x_1937_ = lean_apply_1(v___x_107__overap_1936_, v_ref_1934_);
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
v___x_2009_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__13));
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
v___x_2018_ = ((lean_object*)(l_Lean_Elab_OpenDecl_elabOpenDecl___redArg___closed__14));
v___x_2019_ = l_Lean_instMonadRefOfMonadLiftOfMonadFunctor___redArg(v___x_2009_, v___x_2018_, v_inst_1988_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2020_, 0, v_inst_1989_);
lean_closure_set(v___f_2020_, 1, v___x_2009_);
lean_inc_ref(v___x_2003_);
lean_inc_ref(v___f_2020_);
v___x_2021_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___f_2020_, v___x_2003_);
v___x_2022_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_2009_, v_inst_1991_);
v___x_2023_ = l_Lean_instMonadOptionsOfMonadLift___redArg(v___x_2009_, v_inst_1992_);
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
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
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
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
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
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
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
res = initialize_Lean_Linter_Deprecated(builtin);
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
