// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Postponed
// Imports: public import Lean.Elab.Term.TermElabM
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
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
size_t lean_usize_sub(size_t, size_t);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_getBuiltinVersoDocStrings();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPostponedImport_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPostponedImport_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instBEqPostponedImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instBEqPostponedImport_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instBEqPostponedImport___closed__0 = (const lean_object*)&l_Lean_Doc_instBEqPostponedImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instBEqPostponedImport = (const lean_object*)&l_Lean_Doc_instBEqPostponedImport___closed__0_value;
static lean_once_cell_t l_Lean_Doc_instHashablePostponedImport_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Doc_instHashablePostponedImport_hash___closed__0;
static lean_once_cell_t l_Lean_Doc_instHashablePostponedImport_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Doc_instHashablePostponedImport_hash___closed__1;
LEAN_EXPORT uint64_t l_Lean_Doc_instHashablePostponedImport_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instHashablePostponedImport_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instHashablePostponedImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instHashablePostponedImport_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instHashablePostponedImport___closed__0 = (const lean_object*)&l_Lean_Doc_instHashablePostponedImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instHashablePostponedImport = (const lean_object*)&l_Lean_Doc_instHashablePostponedImport___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Doc_instReprPostponedImport_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7;
static const lean_string_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instReprPostponedImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instReprPostponedImport_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instReprPostponedImport___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPostponedImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instReprPostponedImport = (const lean_object*)&l_Lean_Doc_instReprPostponedImport___closed__0_value;
static const lean_string_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PostponedImport"};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value;
static const lean_string_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 22, 81, 184, 235, 228, 245, 197)}};
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(118, 204, 135, 112, 44, 189, 39, 200)}};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instToExprPostponedImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instToExprPostponedImport___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instToExprPostponedImport___closed__0 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instToExprPostponedImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instToExprPostponedImport___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 22, 81, 184, 235, 228, 245, 197)}};
static const lean_object* l_Lean_Doc_instToExprPostponedImport___closed__1 = (const lean_object*)&l_Lean_Doc_instToExprPostponedImport___closed__1_value;
static lean_once_cell_t l_Lean_Doc_instToExprPostponedImport___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instToExprPostponedImport___closed__2;
static lean_once_cell_t l_Lean_Doc_instToExprPostponedImport___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_instToExprPostponedImport___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_instToExprPostponedImport;
static const lean_closure_object l_Lean_Doc_instOrdPostponedImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instOrdPostponedImport___closed__0 = (const lean_object*)&l_Lean_Doc_instOrdPostponedImport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instOrdPostponedImport = (const lean_object*)&l_Lean_Doc_instOrdPostponedImport___closed__0_value;
static const lean_string_object l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "PostponedCheck"};
static const lean_object* l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value;
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(119, 166, 252, 99, 21, 247, 131, 141)}};
static const lean_object* l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instTypeNamePostponedCheck = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13__value;
static const lean_string_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ handler := "};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", imports := "};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3_value;
static const lean_string_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instReprPostponedCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instReprPostponedCheck___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_instReprPostponedImport___closed__0_value)} };
static const lean_object* l_Lean_Doc_instReprPostponedCheck___closed__0 = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instReprPostponedCheck = (const lean_object*)&l_Lean_Doc_instReprPostponedCheck___closed__0_value;
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "PostponedCheckHandler"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 205, 228, 246, 199, 230, 222, 104)}};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Check in `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` requires that `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is imported, but it is not."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__0_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 105, 224, 152, 247, 148, 58, 69)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " passed, "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " failed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_checkPostponed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "checks"};
static const lean_object* l_Lean_Doc_checkPostponed___closed__0 = (const lean_object*)&l_Lean_Doc_checkPostponed___closed__0_value;
static const lean_ctor_object l_Lean_Doc_checkPostponed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_checkPostponed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 43, 61, 84, 108, 97, 184, 96)}};
static const lean_object* l_Lean_Doc_checkPostponed___closed__1 = (const lean_object*)&l_Lean_Doc_checkPostponed___closed__1_value;
static lean_once_cell_t l_Lean_Doc_checkPostponed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_checkPostponed___closed__2;
static const lean_string_object l_Lean_Doc_checkPostponed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Postponed checks: "};
static const lean_object* l_Lean_Doc_checkPostponed___closed__3 = (const lean_object*)&l_Lean_Doc_checkPostponed___closed__3_value;
static lean_once_cell_t l_Lean_Doc_checkPostponed___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_checkPostponed___closed__4;
static const lean_string_object l_Lean_Doc_checkPostponed___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " declarations, "};
static const lean_object* l_Lean_Doc_checkPostponed___closed__5 = (const lean_object*)&l_Lean_Doc_checkPostponed___closed__5_value;
static lean_once_cell_t l_Lean_Doc_checkPostponed___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_checkPostponed___closed__6;
static const lean_array_object l_Lean_Doc_checkPostponed___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_checkPostponed___closed__7 = (const lean_object*)&l_Lean_Doc_checkPostponed___closed__7_value;
static lean_once_cell_t l_Lean_Doc_checkPostponed___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_checkPostponed___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_checkPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_checkPostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PostponedKind"};
static const lean_object* l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(4, 126, 152, 146, 251, 151, 37, 250)}};
static const lean_object* l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instTypeNamePostponedKind = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1858815893____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PostponedName"};
static const lean_object* l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Lean_Doc_instImpl___closed__0_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(167, 68, 121, 121, 24, 14, 202, 161)}};
static const lean_object* l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instTypeNamePostponedName = (const lean_object*)&l_Lean_Doc_instImpl___closed__1_00___x40_Lean_Elab_DocString_Builtin_Postponed_1706582166____hygCtx___hyg_8__value;
LEAN_EXPORT uint8_t l_Lean_Doc_instBEqPostponedImport_beq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_name_eq(v_x_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instBEqPostponedImport_beq___boxed(lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
uint8_t v_res_6_; lean_object* v_r_7_; 
v_res_6_ = l_Lean_Doc_instBEqPostponedImport_beq(v_x_4_, v_x_5_);
lean_dec(v_x_5_);
lean_dec(v_x_4_);
v_r_7_ = lean_box(v_res_6_);
return v_r_7_;
}
}
static uint64_t _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__0(void){
_start:
{
lean_object* v___x_10_; uint64_t v___x_11_; 
v___x_10_ = lean_unsigned_to_nat(1723u);
v___x_11_ = lean_uint64_of_nat(v___x_10_);
return v___x_11_;
}
}
static uint64_t _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__1(void){
_start:
{
uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; 
v___x_12_ = lean_uint64_once(&l_Lean_Doc_instHashablePostponedImport_hash___closed__0, &l_Lean_Doc_instHashablePostponedImport_hash___closed__0_once, _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__0);
v___x_13_ = 0ULL;
v___x_14_ = lean_uint64_mix_hash(v___x_13_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT uint64_t l_Lean_Doc_instHashablePostponedImport_hash(lean_object* v_x_15_){
_start:
{
uint64_t v___x_16_; 
v___x_16_ = 0ULL;
if (lean_obj_tag(v_x_15_) == 0)
{
uint64_t v___x_17_; 
v___x_17_ = lean_uint64_once(&l_Lean_Doc_instHashablePostponedImport_hash___closed__1, &l_Lean_Doc_instHashablePostponedImport_hash___closed__1_once, _init_l_Lean_Doc_instHashablePostponedImport_hash___closed__1);
return v___x_17_;
}
else
{
uint64_t v_hash_18_; uint64_t v___x_19_; 
v_hash_18_ = lean_ctor_get_uint64(v_x_15_, sizeof(void*)*2);
v___x_19_ = lean_uint64_mix_hash(v___x_16_, v_hash_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instHashablePostponedImport_hash___boxed(lean_object* v_x_20_){
_start:
{
uint64_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_Lean_Doc_instHashablePostponedImport_hash(v_x_20_);
lean_dec(v_x_20_);
v_r_22_ = lean_box_uint64(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Doc_instReprPostponedImport_repr_spec__0(lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_nat_to_int(v_a_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(8u);
v___x_41_ = lean_nat_to_int(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__0));
v___x_44_ = lean_string_length(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9, &l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9_once, _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__9);
v___x_46_ = lean_nat_to_int(v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr___redArg(lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_52_ = ((lean_object*)(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__6));
v___x_53_ = lean_obj_once(&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7, &l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7_once, _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__7);
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Lean_Name_reprPrec(v_x_51_, v___x_54_);
v___x_56_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_53_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = 0;
v___x_58_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v___x_57_);
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_52_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_obj_once(&l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10, &l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10_once, _init_l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__10);
v___x_61_ = ((lean_object*)(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__11));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_59_);
v___x_63_ = ((lean_object*)(l_Lean_Doc_instReprPostponedImport_repr___redArg___closed__12));
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_60_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*1, v___x_57_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr(lean_object* v_x_67_, lean_object* v_prec_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Doc_instReprPostponedImport_repr___redArg(v_x_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedImport_repr___boxed(lean_object* v_x_70_, lean_object* v_prec_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Doc_instReprPostponedImport_repr(v_x_70_, v_prec_71_);
lean_dec(v_prec_71_);
return v_res_72_;
}
}
static lean_object* _init_l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_box(0);
v___x_85_ = ((lean_object*)(l_Lean_Doc_instToExprPostponedImport___lam__0___closed__4));
v___x_86_ = l_Lean_Expr_const___override(v___x_85_, v___x_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instToExprPostponedImport___lam__0(lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_obj_once(&l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5, &l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5_once, _init_l_Lean_Doc_instToExprPostponedImport___lam__0___closed__5);
v___x_89_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_x_87_);
v___x_90_ = l_Lean_Expr_app___override(v___x_88_, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Doc_instToExprPostponedImport___closed__2(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = ((lean_object*)(l_Lean_Doc_instToExprPostponedImport___closed__1));
v___x_98_ = l_Lean_Expr_const___override(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Doc_instToExprPostponedImport___closed__3(void){
_start:
{
lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_Lean_Doc_instToExprPostponedImport___closed__2, &l_Lean_Doc_instToExprPostponedImport___closed__2_once, _init_l_Lean_Doc_instToExprPostponedImport___closed__2);
v___f_100_ = ((lean_object*)(l_Lean_Doc_instToExprPostponedImport___closed__0));
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___f_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Doc_instToExprPostponedImport(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Doc_instToExprPostponedImport___closed__3, &l_Lean_Doc_instToExprPostponedImport___closed__3_once, _init_l_Lean_Doc_instToExprPostponedImport___closed__3);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0(lean_object* v___x_121_, lean_object* v_v_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_handler_124_; lean_object* v_imports_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_handler_124_ = lean_ctor_get(v_v_122_, 0);
lean_inc(v_handler_124_);
v_imports_125_ = lean_ctor_get(v_v_122_, 1);
lean_inc_ref(v_imports_125_);
lean_dec_ref(v_v_122_);
v___x_126_ = ((lean_object*)(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__1));
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = l_Lean_Name_reprPrec(v_handler_124_, v___x_127_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = ((lean_object*)(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__3));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = l_Array_repr___redArg(v___x_121_, v_imports_125_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = ((lean_object*)(l_Lean_Doc_instReprPostponedCheck___lam__0___closed__5));
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPostponedCheck___lam__0___boxed(lean_object* v___x_136_, lean_object* v_v_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Doc_instReprPostponedCheck___lam__0(v___x_136_, v_v_137_, v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_box(0);
v___x_144_ = l_Lean_Elab_abortCommandExceptionId;
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v___x_159_; lean_object* v_mctx_160_; lean_object* v_lctx_161_; lean_object* v_options_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_157_ = lean_st_ref_get(v___y_155_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_env_158_);
lean_dec(v___x_157_);
v___x_159_ = lean_st_ref_get(v___y_153_);
v_mctx_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_mctx_160_);
lean_dec(v___x_159_);
v_lctx_161_ = lean_ctor_get(v___y_152_, 2);
v_options_162_ = lean_ctor_get(v___y_154_, 2);
lean_inc_ref(v_options_162_);
lean_inc_ref(v_lctx_161_);
v___x_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_163_, 0, v_env_158_);
lean_ctor_set(v___x_163_, 1, v_mctx_160_);
lean_ctor_set(v___x_163_, 2, v_lctx_161_);
lean_ctor_set(v___x_163_, 3, v_options_162_);
v___x_164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_msgData_151_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_172_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_box(1);
v___x_174_ = l_Lean_MessageData_ofFormat(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__2));
v___x_179_ = l_Lean_MessageData_ofFormat(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
return v_x_180_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_205_; 
v_head_182_ = lean_ctor_get(v_x_181_, 0);
v_tail_183_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_205_ == 0)
{
v___x_185_ = v_x_181_;
v_isShared_186_ = v_isSharedCheck_205_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_tail_183_);
lean_inc(v_head_182_);
lean_dec(v_x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_205_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_before_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_203_; 
v_before_187_ = lean_ctor_get(v_head_182_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_head_182_);
if (v_isSharedCheck_203_ == 0)
{
lean_object* v_unused_204_; 
v_unused_204_ = lean_ctor_get(v_head_182_, 1);
lean_dec(v_unused_204_);
v___x_189_ = v_head_182_;
v_isShared_190_ = v_isSharedCheck_203_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_before_187_);
lean_dec(v_head_182_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_203_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 7);
lean_ctor_set(v___x_189_, 1, v___x_191_);
lean_ctor_set(v___x_189_, 0, v_x_180_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_x_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_202_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__3);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 7);
lean_ctor_set(v___x_185_, 1, v___x_194_);
lean_ctor_set(v___x_185_, 0, v___x_193_);
v___x_196_ = v___x_185_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_201_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = l_Lean_MessageData_ofSyntax(v_before_187_);
v___x_198_ = l_Lean_indentD(v___x_197_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_196_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v_x_180_ = v___x_199_;
v_x_181_ = v_tail_183_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_opts_206_, lean_object* v_opt_207_){
_start:
{
lean_object* v_name_208_; lean_object* v_defValue_209_; lean_object* v_map_210_; lean_object* v___x_211_; 
v_name_208_ = lean_ctor_get(v_opt_207_, 0);
v_defValue_209_ = lean_ctor_get(v_opt_207_, 1);
v_map_210_ = lean_ctor_get(v_opts_206_, 0);
v___x_211_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_210_, v_name_208_);
if (lean_obj_tag(v___x_211_) == 0)
{
uint8_t v___x_212_; 
v___x_212_ = lean_unbox(v_defValue_209_);
return v___x_212_;
}
else
{
lean_object* v_val_213_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_213_);
lean_dec_ref(v___x_211_);
if (lean_obj_tag(v_val_213_) == 1)
{
uint8_t v_v_214_; 
v_v_214_ = lean_ctor_get_uint8(v_val_213_, 0);
lean_dec_ref(v_val_213_);
return v_v_214_;
}
else
{
uint8_t v___x_215_; 
lean_dec(v_val_213_);
v___x_215_ = lean_unbox(v_defValue_209_);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_opts_216_, lean_object* v_opt_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_opts_216_, v_opt_217_);
lean_dec_ref(v_opt_217_);
lean_dec_ref(v_opts_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__1));
v___x_224_ = l_Lean_MessageData_ofFormat(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_msgData_225_, lean_object* v_macroStack_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_options_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_options_229_ = lean_ctor_get(v___y_227_, 2);
v___x_230_ = l_Lean_Elab_pp_macroStack;
v___x_231_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_options_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v_macroStack_226_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_msgData_225_);
return v___x_232_;
}
else
{
if (lean_obj_tag(v_macroStack_226_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_msgData_225_);
return v___x_233_;
}
else
{
lean_object* v_head_234_; lean_object* v_after_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_250_; 
v_head_234_ = lean_ctor_get(v_macroStack_226_, 0);
lean_inc(v_head_234_);
v_after_235_ = lean_ctor_get(v_head_234_, 1);
v_isSharedCheck_250_ = !lean_is_exclusive(v_head_234_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_head_234_, 0);
lean_dec(v_unused_251_);
v___x_237_ = v_head_234_;
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_after_235_);
lean_dec(v_head_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_250_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6___closed__0);
if (v_isShared_238_ == 0)
{
lean_ctor_set_tag(v___x_237_, 7);
lean_ctor_set(v___x_237_, 1, v___x_239_);
lean_ctor_set(v___x_237_, 0, v_msgData_225_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_msgData_225_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_249_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_msgData_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_242_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___closed__2);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = l_Lean_MessageData_ofSyntax(v_after_235_);
v___x_245_ = l_Lean_indentD(v___x_244_);
v_msgData_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_246_, 0, v___x_243_);
lean_ctor_set(v_msgData_246_, 1, v___x_245_);
v___x_247_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__6(v_msgData_246_, v_macroStack_226_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_252_, lean_object* v_macroStack_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_msgData_252_, v_macroStack_253_, v___y_254_);
lean_dec_ref(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_ref_265_; lean_object* v___x_266_; lean_object* v_a_267_; lean_object* v_macroStack_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_279_; 
v_ref_265_ = lean_ctor_get(v___y_262_, 5);
v___x_266_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_257_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v___x_266_);
v_macroStack_268_ = lean_ctor_get(v___y_258_, 1);
lean_inc_n(v_macroStack_268_, 2);
v___x_269_ = l_Lean_Elab_getBetterRef(v_ref_265_, v_macroStack_268_);
v___x_270_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_a_267_, v_macroStack_268_, v___y_262_);
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_279_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_279_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_269_);
lean_ctor_set(v___x_275_, 1, v_a_271_);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 1);
lean_ctor_set(v___x_273_, 0, v___x_275_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_a_297_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v_x_289_);
v___x_298_ = l_Lean_stringToMessageData(v_a_297_);
v___x_299_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v___x_298_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_299_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v_x_289_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_289_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v_x_289_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v_x_289_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 0);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(lean_object* v_typeName_317_, lean_object* v_constName_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
lean_inc(v_constName_318_);
v___x_328_ = lean_has_compile_error(v_env_327_, v_constName_318_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v_options_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = lean_st_ref_get(v___y_324_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
v_options_331_ = lean_ctor_get(v___y_323_, 2);
v___x_332_ = l_Lean_Environment_evalConstCheck___redArg(v_env_330_, v_options_331_, v_typeName_317_, v_constName_318_);
v___x_333_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_332_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; lean_object* v_env_336_; lean_object* v_options_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v___x_334_);
v___x_335_ = lean_st_ref_get(v___y_324_);
v_env_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_env_336_);
lean_dec(v___x_335_);
v_options_337_ = lean_ctor_get(v___y_323_, 2);
v___x_338_ = l_Lean_Environment_evalConstCheck___redArg(v_env_336_, v_options_337_, v_typeName_317_, v_constName_318_);
v___x_339_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v___x_338_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_constName_318_);
lean_dec(v_typeName_317_);
v_a_340_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_334_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_334_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_348_, lean_object* v_constName_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v_typeName_348_, v_constName_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(lean_object* v_name_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___closed__1));
v___x_372_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v___x_371_, v_name_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe___boxed(lean_object* v_name_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(v_name_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___redArg();
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__1(v_00_u03b1_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0(lean_object* v_00_u03b1_400_, lean_object* v_typeName_401_, lean_object* v_constName_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___redArg(v_typeName_401_, v_constName_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_411_, lean_object* v_typeName_412_, lean_object* v_constName_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0(v_00_u03b1_411_, v_typeName_412_, v_constName_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___redArg(v_x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_432_, lean_object* v_x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0(v_00_u03b1_432_, v_x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_452_, lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_452_, v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_462_, lean_object* v_macroStack_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___redArg(v_msgData_462_, v_macroStack_463_, v___y_468_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_472_, lean_object* v_macroStack_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4(v_msgData_472_, v_macroStack_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(lean_object* v_s_482_){
_start:
{
lean_object* v_passed_483_; lean_object* v_failed_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_passed_483_ = lean_ctor_get(v_s_482_, 0);
v_failed_484_ = lean_ctor_get(v_s_482_, 1);
v___x_485_ = lean_array_get_size(v_failed_484_);
v___x_486_ = lean_nat_add(v_passed_483_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total___boxed(lean_object* v_s_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v_s_487_);
lean_dec_ref(v_s_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(lean_object* v_act_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc(v_a_492_);
lean_inc_ref(v_a_491_);
v___x_498_ = lean_apply_7(v_act_489_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, lean_box(0));
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_519_; 
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_520_);
v___x_500_ = v___x_498_;
v_isShared_501_ = v_isSharedCheck_519_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_498_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_519_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v_passed_503_; lean_object* v_failed_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_518_; 
v___x_502_ = lean_st_ref_take(v_a_490_);
v_passed_503_ = lean_ctor_get(v___x_502_, 0);
v_failed_504_ = lean_ctor_get(v___x_502_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_518_ == 0)
{
v___x_506_ = v___x_502_;
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_failed_504_);
lean_inc(v_passed_503_);
lean_dec(v___x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_518_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_passed_503_, v___x_508_);
lean_dec(v_passed_503_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_failed_504_);
v___x_511_ = v_reuseFailAlloc_517_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_st_ref_set(v_a_490_, v___x_511_);
v___x_513_ = lean_box(0);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_513_);
v___x_515_ = v___x_500_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_521_; uint8_t v___y_523_; uint8_t v___x_545_; 
v_a_521_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_521_);
v___x_545_ = l_Lean_Exception_isInterrupt(v_a_521_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
lean_inc(v_a_521_);
v___x_546_ = l_Lean_Exception_isRuntime(v_a_521_);
v___y_523_ = v___x_546_;
goto v___jp_522_;
}
else
{
v___y_523_ = v___x_545_;
goto v___jp_522_;
}
v___jp_522_:
{
if (v___y_523_ == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_543_; 
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_544_);
v___x_525_ = v___x_498_;
v_isShared_526_ = v_isSharedCheck_543_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_498_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_543_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_passed_528_; lean_object* v_failed_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_542_; 
v___x_527_ = lean_st_ref_take(v_a_490_);
v_passed_528_ = lean_ctor_get(v___x_527_, 0);
v_failed_529_ = lean_ctor_get(v___x_527_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_542_ == 0)
{
v___x_531_ = v___x_527_;
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_failed_529_);
lean_inc(v_passed_528_);
lean_dec(v___x_527_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = lean_array_push(v_failed_529_, v_a_521_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_passed_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_541_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_536_ = lean_st_ref_set(v_a_490_, v___x_535_);
v___x_537_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 0);
lean_ctor_set(v___x_525_, 0, v___x_537_);
v___x_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_dec(v_a_521_);
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck___boxed(lean_object* v_act_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(v_act_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 5);
v___x_564_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_ref_563_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_ref_563_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg___boxed(lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v_msg_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_580_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(lean_object* v_a_581_, lean_object* v_as_582_, size_t v_i_583_, size_t v_stop_584_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = lean_usize_dec_eq(v_i_583_, v_stop_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_array_uget_borrowed(v_as_582_, v_i_583_);
v___x_587_ = lean_name_eq(v_a_581_, v___x_586_);
if (v___x_587_ == 0)
{
size_t v___x_588_; size_t v___x_589_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_583_, v___x_588_);
v_i_583_ = v___x_589_;
goto _start;
}
else
{
return v___x_587_;
}
}
else
{
uint8_t v___x_591_; 
v___x_591_ = 0;
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1___boxed(lean_object* v_a_592_, lean_object* v_as_593_, lean_object* v_i_594_, lean_object* v_stop_595_){
_start:
{
size_t v_i_boxed_596_; size_t v_stop_boxed_597_; uint8_t v_res_598_; lean_object* v_r_599_; 
v_i_boxed_596_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_stop_boxed_597_ = lean_unbox_usize(v_stop_595_);
lean_dec(v_stop_595_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(v_a_592_, v_as_593_, v_i_boxed_596_, v_stop_boxed_597_);
lean_dec_ref(v_as_593_);
lean_dec(v_a_592_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(lean_object* v_as_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_array_get_size(v_as_600_);
v___x_604_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
return v___x_604_;
}
else
{
if (v___x_604_ == 0)
{
return v___x_604_;
}
else
{
size_t v___x_605_; size_t v___x_606_; uint8_t v___x_607_; 
v___x_605_ = ((size_t)0ULL);
v___x_606_ = lean_usize_of_nat(v___x_603_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1_spec__1(v_a_601_, v_as_600_, v___x_605_, v___x_606_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1___boxed(lean_object* v_as_608_, lean_object* v_a_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(v_as_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_as_608_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__0));
v___x_614_ = l_Lean_stringToMessageData(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__2));
v___x_617_ = l_Lean_stringToMessageData(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__4));
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(lean_object* v_declName_621_, lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_a_635_; uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec(v_declName_621_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_b_625_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v_env_642_; lean_object* v___x_643_; lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_641_ = lean_st_ref_get(v___y_632_);
v_env_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc_ref(v_env_642_);
lean_dec(v___x_641_);
v___x_643_ = lean_box(0);
v_a_644_ = lean_array_uget_borrowed(v_as_622_, v_i_624_);
v___x_645_ = l_Lean_Environment_header(v_env_642_);
lean_dec_ref(v_env_642_);
v___x_646_ = l_Lean_EnvironmentHeader_moduleNames(v___x_645_);
v___x_647_ = l_Array_contains___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__1(v___x_646_, v_a_644_);
lean_dec_ref(v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__1);
lean_inc(v_declName_621_);
v___x_649_ = l_Lean_MessageData_ofConstName(v_declName_621_, v___x_647_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__3);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_inc(v_a_644_);
v___x_653_ = l_Lean_MessageData_ofName(v_a_644_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___closed__5);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v___x_656_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
v_a_635_ = v___x_643_;
goto v___jp_634_;
}
else
{
lean_dec(v_declName_621_);
return v___x_657_;
}
}
else
{
v_a_635_ = v___x_643_;
goto v___jp_634_;
}
}
v___jp_634_:
{
size_t v___x_636_; size_t v___x_637_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_624_, v___x_636_);
v_i_624_ = v___x_637_;
v_b_625_ = v_a_635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3___boxed(lean_object* v_declName_658_, lean_object* v_as_659_, lean_object* v_sz_660_, lean_object* v_i_661_, lean_object* v_b_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_660_);
lean_dec(v_sz_660_);
v_i_boxed_672_ = lean_unbox_usize(v_i_661_);
lean_dec(v_i_661_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_658_, v_as_659_, v_sz_boxed_671_, v_i_boxed_672_, v_b_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v_as_659_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(lean_object* v_declName_674_, lean_object* v_inline_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_is_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; 
switch(lean_obj_tag(v_inline_675_))
{
case 0:
{
lean_dec(v_declName_674_);
goto v___jp_684_;
}
case 1:
{
lean_object* v_content_708_; 
v_content_708_ = lean_ctor_get(v_inline_675_, 0);
v_is_688_ = v_content_708_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
v___y_695_ = v_a_682_;
goto v___jp_687_;
}
case 2:
{
lean_object* v_content_709_; 
v_content_709_ = lean_ctor_get(v_inline_675_, 0);
v_is_688_ = v_content_709_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
v___y_695_ = v_a_682_;
goto v___jp_687_;
}
case 3:
{
lean_dec(v_declName_674_);
goto v___jp_684_;
}
case 5:
{
lean_dec(v_declName_674_);
goto v___jp_684_;
}
case 6:
{
lean_object* v_content_710_; lean_object* v___x_711_; size_t v_sz_712_; size_t v___x_713_; lean_object* v___x_714_; 
v_content_710_ = lean_ctor_get(v_inline_675_, 0);
v___x_711_ = lean_box(0);
v_sz_712_ = lean_array_size(v_content_710_);
v___x_713_ = ((size_t)0ULL);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_674_, v_content_710_, v_sz_712_, v___x_713_, v___x_711_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_714_, 0);
lean_dec(v_unused_722_);
v___x_716_ = v___x_714_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_dec(v___x_714_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_711_);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_711_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
return v___x_714_;
}
}
case 7:
{
lean_object* v_content_723_; lean_object* v___x_724_; size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_content_723_ = lean_ctor_get(v_inline_675_, 1);
v___x_724_ = lean_box(0);
v_sz_725_ = lean_array_size(v_content_723_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_674_, v_content_723_, v_sz_725_, v___x_726_, v___x_724_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_727_, 0);
lean_dec(v_unused_735_);
v___x_729_ = v___x_727_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_dec(v___x_727_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_724_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_724_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
return v___x_727_;
}
}
case 9:
{
lean_object* v_content_736_; 
v_content_736_ = lean_ctor_get(v_inline_675_, 0);
v_is_688_ = v_content_736_;
v___y_689_ = v_a_676_;
v___y_690_ = v_a_677_;
v___y_691_ = v_a_678_;
v___y_692_ = v_a_679_;
v___y_693_ = v_a_680_;
v___y_694_ = v_a_681_;
v___y_695_ = v_a_682_;
goto v___jp_687_;
}
case 10:
{
lean_object* v_container_737_; lean_object* v_content_738_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v_val_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_container_737_ = lean_ctor_get(v_inline_675_, 0);
v_content_738_ = lean_ctor_get(v_inline_675_, 1);
v_val_759_ = lean_ctor_get(v_container_737_, 1);
v___x_760_ = ((lean_object*)(l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_));
v___x_761_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_759_, v___x_760_);
if (lean_obj_tag(v___x_761_) == 1)
{
lean_object* v_val_762_; lean_object* v_handler_763_; lean_object* v_imports_764_; lean_object* v_info_765_; lean_object* v___x_766_; size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; 
v_val_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_val_762_);
lean_dec_ref(v___x_761_);
v_handler_763_ = lean_ctor_get(v_val_762_, 0);
lean_inc(v_handler_763_);
v_imports_764_ = lean_ctor_get(v_val_762_, 1);
lean_inc_ref(v_imports_764_);
v_info_765_ = lean_ctor_get(v_val_762_, 2);
lean_inc(v_info_765_);
lean_dec(v_val_762_);
v___x_766_ = lean_box(0);
v_sz_767_ = lean_array_size(v_imports_764_);
v___x_768_ = ((size_t)0ULL);
lean_inc(v_declName_674_);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_674_, v_imports_764_, v_sz_767_, v___x_768_, v___x_766_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec_ref(v_imports_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_769_);
v___x_770_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(v_handler_763_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
lean_inc(v_declName_674_);
v___x_772_ = lean_apply_2(v_a_771_, v_declName_674_, v_info_765_);
v___x_773_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(v___x_772_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec_ref(v___x_773_);
v___y_740_ = v_a_676_;
v___y_741_ = v_a_677_;
v___y_742_ = v_a_678_;
v___y_743_ = v_a_679_;
v___y_744_ = v_a_680_;
v___y_745_ = v_a_681_;
v___y_746_ = v_a_682_;
goto v___jp_739_;
}
else
{
lean_dec(v_declName_674_);
return v___x_773_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_info_765_);
lean_dec(v_declName_674_);
v_a_774_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_770_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_770_);
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
lean_dec(v_info_765_);
lean_dec(v_handler_763_);
lean_dec(v_declName_674_);
return v___x_769_;
}
}
else
{
lean_dec(v___x_761_);
v___y_740_ = v_a_676_;
v___y_741_ = v_a_677_;
v___y_742_ = v_a_678_;
v___y_743_ = v_a_679_;
v___y_744_ = v_a_680_;
v___y_745_ = v_a_681_;
v___y_746_ = v_a_682_;
goto v___jp_739_;
}
v___jp_739_:
{
lean_object* v___x_747_; size_t v_sz_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_747_ = lean_box(0);
v_sz_748_ = lean_array_size(v_content_738_);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_674_, v_content_738_, v_sz_748_, v___x_749_, v___x_747_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_758_);
v___x_752_ = v___x_750_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_dec(v___x_750_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_747_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_747_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
return v___x_750_;
}
}
}
default: 
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec(v_declName_674_);
v___x_782_ = lean_box(0);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
v___jp_684_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
v___jp_687_:
{
lean_object* v___x_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_696_ = lean_box(0);
v_sz_697_ = lean_array_size(v_is_688_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_674_, v_is_688_, v_sz_697_, v___x_698_, v___x_696_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_699_, 0);
lean_dec(v_unused_707_);
v___x_701_ = v___x_699_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_dec(v___x_699_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_696_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_696_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(lean_object* v_declName_784_, lean_object* v_as_785_, size_t v_sz_786_, size_t v_i_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v_declName_784_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_b_788_);
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_array_uget_borrowed(v_as_785_, v_i_787_);
lean_inc(v_declName_784_);
v___x_800_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(v_declName_784_, v_a_799_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; 
lean_dec_ref(v___x_800_);
v___x_801_ = lean_box(0);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_787_, v___x_802_);
v_i_787_ = v___x_803_;
v_b_788_ = v___x_801_;
goto _start;
}
else
{
lean_dec(v_declName_784_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0___boxed(lean_object* v_declName_805_, lean_object* v_as_806_, lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
size_t v_sz_boxed_818_; size_t v_i_boxed_819_; lean_object* v_res_820_; 
v_sz_boxed_818_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_819_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_805_, v_as_806_, v_sz_boxed_818_, v_i_boxed_819_, v_b_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v_as_806_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed___boxed(lean_object* v_declName_821_, lean_object* v_inline_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed(v_declName_821_, v_inline_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_inline_822_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2(lean_object* v_00_u03b1_832_, lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___redArg(v_msg_833_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2___boxed(lean_object* v_00_u03b1_843_, lean_object* v_msg_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_throwError___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__2(v_00_u03b1_843_, v_msg_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(lean_object* v_declName_854_, lean_object* v_as_855_, size_t v_sz_856_, size_t v_i_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_857_, v_sz_856_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_declName_854_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_b_858_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v_a_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; 
v___x_869_ = lean_box(0);
v_a_870_ = lean_array_uget_borrowed(v_as_855_, v_i_857_);
v_sz_871_ = lean_array_size(v_a_870_);
v___x_872_ = ((size_t)0ULL);
lean_inc(v_declName_854_);
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_854_, v_a_870_, v_sz_871_, v___x_872_, v___x_869_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_873_) == 0)
{
size_t v___x_874_; size_t v___x_875_; 
lean_dec_ref(v___x_873_);
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_857_, v___x_874_);
v_i_857_ = v___x_875_;
v_b_858_ = v___x_869_;
goto _start;
}
else
{
lean_dec(v_declName_854_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(lean_object* v_declName_877_, lean_object* v_as_878_, size_t v_sz_879_, size_t v_i_880_, lean_object* v_b_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_lt(v_i_880_, v_sz_879_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_declName_877_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_b_881_);
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v_term_893_; lean_object* v_desc_894_; lean_object* v___x_895_; size_t v_sz_896_; size_t v___x_897_; lean_object* v___x_898_; 
v_a_892_ = lean_array_uget_borrowed(v_as_878_, v_i_880_);
v_term_893_ = lean_ctor_get(v_a_892_, 0);
v_desc_894_ = lean_ctor_get(v_a_892_, 1);
v___x_895_ = lean_box(0);
v_sz_896_ = lean_array_size(v_term_893_);
v___x_897_ = ((size_t)0ULL);
lean_inc(v_declName_877_);
v___x_898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_877_, v_term_893_, v_sz_896_, v___x_897_, v___x_895_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_898_) == 0)
{
size_t v_sz_899_; lean_object* v___x_900_; 
lean_dec_ref(v___x_898_);
v_sz_899_ = lean_array_size(v_desc_894_);
lean_inc(v_declName_877_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_877_, v_desc_894_, v_sz_899_, v___x_897_, v___x_895_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_900_) == 0)
{
size_t v___x_901_; size_t v___x_902_; 
lean_dec_ref(v___x_900_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_880_, v___x_901_);
v_i_880_ = v___x_902_;
v_b_881_ = v___x_895_;
goto _start;
}
else
{
lean_dec(v_declName_877_);
return v___x_900_;
}
}
else
{
lean_dec(v_declName_877_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(lean_object* v_declName_904_, lean_object* v_doc_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_bs_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; 
switch(lean_obj_tag(v_doc_905_))
{
case 0:
{
lean_object* v_contents_935_; lean_object* v___x_936_; size_t v_sz_937_; size_t v___x_938_; lean_object* v___x_939_; 
v_contents_935_ = lean_ctor_get(v_doc_905_, 0);
lean_inc_ref(v_contents_935_);
lean_dec_ref(v_doc_905_);
v___x_936_ = lean_box(0);
v_sz_937_ = lean_array_size(v_contents_935_);
v___x_938_ = ((size_t)0ULL);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__0(v_declName_904_, v_contents_935_, v_sz_937_, v___x_938_, v___x_936_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_contents_935_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_939_, 0);
lean_dec(v_unused_947_);
v___x_941_ = v___x_939_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_dec(v___x_939_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_936_);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_936_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
return v___x_939_;
}
}
case 1:
{
lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_declName_904_);
v_isSharedCheck_955_ = !lean_is_exclusive(v_doc_905_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_doc_905_, 0);
lean_dec(v_unused_956_);
v___x_949_ = v_doc_905_;
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
else
{
lean_dec(v_doc_905_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 0);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
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
case 2:
{
lean_object* v_items_957_; lean_object* v___x_958_; size_t v_sz_959_; size_t v___x_960_; lean_object* v___x_961_; 
v_items_957_ = lean_ctor_get(v_doc_905_, 0);
lean_inc_ref(v_items_957_);
lean_dec_ref(v_doc_905_);
v___x_958_ = lean_box(0);
v_sz_959_ = lean_array_size(v_items_957_);
v___x_960_ = ((size_t)0ULL);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_904_, v_items_957_, v_sz_959_, v___x_960_, v___x_958_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_items_957_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v___x_961_, 0);
lean_dec(v_unused_969_);
v___x_963_ = v___x_961_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_dec(v___x_961_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_958_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_958_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
else
{
return v___x_961_;
}
}
case 3:
{
lean_object* v_items_970_; lean_object* v___x_971_; size_t v_sz_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_items_970_ = lean_ctor_get(v_doc_905_, 1);
lean_inc_ref(v_items_970_);
lean_dec_ref(v_doc_905_);
v___x_971_ = lean_box(0);
v_sz_972_ = lean_array_size(v_items_970_);
v___x_973_ = ((size_t)0ULL);
v___x_974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_904_, v_items_970_, v_sz_972_, v___x_973_, v___x_971_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_items_970_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_982_);
v___x_976_ = v___x_974_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_974_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_971_);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_971_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
else
{
return v___x_974_;
}
}
case 4:
{
lean_object* v_items_983_; lean_object* v___x_984_; size_t v_sz_985_; size_t v___x_986_; lean_object* v___x_987_; 
v_items_983_ = lean_ctor_get(v_doc_905_, 0);
lean_inc_ref(v_items_983_);
lean_dec_ref(v_doc_905_);
v___x_984_ = lean_box(0);
v_sz_985_ = lean_array_size(v_items_983_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(v_declName_904_, v_items_983_, v_sz_985_, v___x_986_, v___x_984_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_items_983_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_987_, 0);
lean_dec(v_unused_995_);
v___x_989_ = v___x_987_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_dec(v___x_987_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_984_);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_984_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
return v___x_987_;
}
}
case 7:
{
lean_object* v_container_996_; lean_object* v_content_997_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v_val_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_container_996_ = lean_ctor_get(v_doc_905_, 0);
lean_inc(v_container_996_);
v_content_997_ = lean_ctor_get(v_doc_905_, 1);
lean_inc_ref(v_content_997_);
lean_dec_ref(v_doc_905_);
v_val_1018_ = lean_ctor_get(v_container_996_, 1);
lean_inc(v_val_1018_);
lean_dec(v_container_996_);
v___x_1019_ = ((lean_object*)(l_Lean_Doc_instImpl_00___x40_Lean_Elab_DocString_Builtin_Postponed_1250074310____hygCtx___hyg_13_));
v___x_1020_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_val_1018_, v___x_1019_);
lean_dec(v_val_1018_);
if (lean_obj_tag(v___x_1020_) == 1)
{
lean_object* v_val_1021_; lean_object* v_handler_1022_; lean_object* v_imports_1023_; lean_object* v_info_1024_; lean_object* v___x_1025_; size_t v_sz_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v_val_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_val_1021_);
lean_dec_ref(v___x_1020_);
v_handler_1022_ = lean_ctor_get(v_val_1021_, 0);
lean_inc(v_handler_1022_);
v_imports_1023_ = lean_ctor_get(v_val_1021_, 1);
lean_inc_ref(v_imports_1023_);
v_info_1024_ = lean_ctor_get(v_val_1021_, 2);
lean_inc(v_info_1024_);
lean_dec(v_val_1021_);
v___x_1025_ = lean_box(0);
v_sz_1026_ = lean_array_size(v_imports_1023_);
v___x_1027_ = ((size_t)0ULL);
lean_inc(v_declName_904_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkInlinePostponed_spec__3(v_declName_904_, v_imports_1023_, v_sz_1026_, v___x_1027_, v___x_1025_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec_ref(v_imports_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_1028_);
v___x_1029_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe(v_handler_1022_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
lean_inc(v_declName_904_);
v___x_1031_ = lean_apply_2(v_a_1030_, v_declName_904_, v_info_1024_);
v___x_1032_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_runCheck(v___x_1031_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_dec_ref(v___x_1032_);
v___y_999_ = v_a_906_;
v___y_1000_ = v_a_907_;
v___y_1001_ = v_a_908_;
v___y_1002_ = v_a_909_;
v___y_1003_ = v_a_910_;
v___y_1004_ = v_a_911_;
v___y_1005_ = v_a_912_;
goto v___jp_998_;
}
else
{
lean_dec_ref(v_content_997_);
lean_dec(v_declName_904_);
return v___x_1032_;
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_info_1024_);
lean_dec_ref(v_content_997_);
lean_dec(v_declName_904_);
v_a_1033_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1029_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1029_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_dec(v_info_1024_);
lean_dec(v_handler_1022_);
lean_dec_ref(v_content_997_);
lean_dec(v_declName_904_);
return v___x_1028_;
}
}
else
{
lean_dec(v___x_1020_);
v___y_999_ = v_a_906_;
v___y_1000_ = v_a_907_;
v___y_1001_ = v_a_908_;
v___y_1002_ = v_a_909_;
v___y_1003_ = v_a_910_;
v___y_1004_ = v_a_911_;
v___y_1005_ = v_a_912_;
goto v___jp_998_;
}
v___jp_998_:
{
lean_object* v___x_1006_; size_t v_sz_1007_; size_t v___x_1008_; lean_object* v___x_1009_; 
v___x_1006_ = lean_box(0);
v_sz_1007_ = lean_array_size(v_content_997_);
v___x_1008_ = ((size_t)0ULL);
v___x_1009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_904_, v_content_997_, v_sz_1007_, v___x_1008_, v___x_1006_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec_ref(v_content_997_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v___x_1009_, 0);
lean_dec(v_unused_1017_);
v___x_1011_ = v___x_1009_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_dec(v___x_1009_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1006_);
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1006_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
else
{
return v___x_1009_;
}
}
}
default: 
{
lean_object* v_items_1041_; 
v_items_1041_ = lean_ctor_get(v_doc_905_, 0);
lean_inc_ref(v_items_1041_);
lean_dec_ref(v_doc_905_);
v_bs_915_ = v_items_1041_;
v___y_916_ = v_a_906_;
v___y_917_ = v_a_907_;
v___y_918_ = v_a_908_;
v___y_919_ = v_a_909_;
v___y_920_ = v_a_910_;
v___y_921_ = v_a_911_;
v___y_922_ = v_a_912_;
goto v___jp_914_;
}
}
v___jp_914_:
{
lean_object* v___x_923_; size_t v_sz_924_; size_t v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_box(0);
v_sz_924_ = lean_array_size(v_bs_915_);
v___x_925_ = ((size_t)0ULL);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_904_, v_bs_915_, v_sz_924_, v___x_925_, v___x_923_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec_ref(v_bs_915_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_934_);
v___x_928_ = v___x_926_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_926_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_923_);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_923_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(lean_object* v_declName_1042_, lean_object* v_as_1043_, size_t v_sz_1044_, size_t v_i_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_usize_dec_lt(v_i_1045_, v_sz_1044_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v_declName_1042_);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v_b_1046_);
return v___x_1056_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1058_; 
v_a_1057_ = lean_array_uget_borrowed(v_as_1043_, v_i_1045_);
lean_inc(v_a_1057_);
lean_inc(v_declName_1042_);
v___x_1058_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(v_declName_1042_, v_a_1057_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; 
lean_dec_ref(v___x_1058_);
v___x_1059_ = lean_box(0);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_add(v_i_1045_, v___x_1060_);
v_i_1045_ = v___x_1061_;
v_b_1046_ = v___x_1059_;
goto _start;
}
else
{
lean_dec(v_declName_1042_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0___boxed(lean_object* v_declName_1063_, lean_object* v_as_1064_, lean_object* v_sz_1065_, lean_object* v_i_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
size_t v_sz_boxed_1076_; size_t v_i_boxed_1077_; lean_object* v_res_1078_; 
v_sz_boxed_1076_ = lean_unbox_usize(v_sz_1065_);
lean_dec(v_sz_1065_);
v_i_boxed_1077_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_1063_, v_as_1064_, v_sz_boxed_1076_, v_i_boxed_1077_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v_as_1064_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1___boxed(lean_object* v_declName_1079_, lean_object* v_as_1080_, lean_object* v_sz_1081_, lean_object* v_i_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
size_t v_sz_boxed_1092_; size_t v_i_boxed_1093_; lean_object* v_res_1094_; 
v_sz_boxed_1092_ = lean_unbox_usize(v_sz_1081_);
lean_dec(v_sz_1081_);
v_i_boxed_1093_ = lean_unbox_usize(v_i_1082_);
lean_dec(v_i_1082_);
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__1(v_declName_1079_, v_as_1080_, v_sz_boxed_1092_, v_i_boxed_1093_, v_b_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v_as_1080_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2___boxed(lean_object* v_declName_1095_, lean_object* v_as_1096_, lean_object* v_sz_1097_, lean_object* v_i_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1097_);
lean_dec(v_sz_1097_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__2(v_declName_1095_, v_as_1096_, v_sz_boxed_1108_, v_i_boxed_1109_, v_b_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v_as_1096_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed___boxed(lean_object* v_declName_1111_, lean_object* v_doc_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed(v_declName_1111_, v_doc_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(lean_object* v_declName_1122_, lean_object* v_doc_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_content_1132_; lean_object* v_subParts_1133_; lean_object* v___x_1134_; size_t v_sz_1135_; size_t v___x_1136_; lean_object* v___x_1137_; 
v_content_1132_ = lean_ctor_get(v_doc_1123_, 3);
v_subParts_1133_ = lean_ctor_get(v_doc_1123_, 4);
v___x_1134_ = lean_box(0);
v_sz_1135_ = lean_array_size(v_content_1132_);
v___x_1136_ = ((size_t)0ULL);
lean_inc(v_declName_1122_);
v___x_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_1122_, v_content_1132_, v_sz_1135_, v___x_1136_, v___x_1134_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1137_) == 0)
{
size_t v_sz_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_1137_);
v_sz_1138_ = lean_array_size(v_subParts_1133_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_1122_, v_subParts_1133_, v_sz_1138_, v___x_1136_, v___x_1134_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1147_);
v___x_1141_ = v___x_1139_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1134_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1134_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
else
{
return v___x_1139_;
}
}
else
{
lean_dec(v_declName_1122_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(lean_object* v_declName_1148_, lean_object* v_as_1149_, size_t v_sz_1150_, size_t v_i_1151_, lean_object* v_b_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_usize_dec_lt(v_i_1151_, v_sz_1150_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec(v_declName_1148_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1152_);
return v___x_1162_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_array_uget_borrowed(v_as_1149_, v_i_1151_);
lean_inc(v_declName_1148_);
v___x_1164_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(v_declName_1148_, v_a_1163_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; 
lean_dec_ref(v___x_1164_);
v___x_1165_ = lean_box(0);
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1151_, v___x_1166_);
v_i_1151_ = v___x_1167_;
v_b_1152_ = v___x_1165_;
goto _start;
}
else
{
lean_dec(v_declName_1148_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0___boxed(lean_object* v_declName_1169_, lean_object* v_as_1170_, lean_object* v_sz_1171_, lean_object* v_i_1172_, lean_object* v_b_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
size_t v_sz_boxed_1182_; size_t v_i_boxed_1183_; lean_object* v_res_1184_; 
v_sz_boxed_1182_ = lean_unbox_usize(v_sz_1171_);
lean_dec(v_sz_1171_);
v_i_boxed_1183_ = lean_unbox_usize(v_i_1172_);
lean_dec(v_i_1172_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_1169_, v_as_1170_, v_sz_boxed_1182_, v_i_boxed_1183_, v_b_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v_as_1170_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed___boxed(lean_object* v_declName_1185_, lean_object* v_doc_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed(v_declName_1185_, v_doc_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_doc_1186_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(lean_object* v_declName_1196_, lean_object* v_doc_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_text_1206_; lean_object* v_subsections_1207_; lean_object* v___x_1208_; size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v_text_1206_ = lean_ctor_get(v_doc_1197_, 0);
v_subsections_1207_ = lean_ctor_get(v_doc_1197_, 1);
v___x_1208_ = lean_box(0);
v_sz_1209_ = lean_array_size(v_text_1206_);
v___x_1210_ = ((size_t)0ULL);
lean_inc(v_declName_1196_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkBlockPostponed_spec__0(v_declName_1196_, v_text_1206_, v_sz_1209_, v___x_1210_, v___x_1208_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1211_) == 0)
{
size_t v_sz_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v___x_1211_);
v_sz_1212_ = lean_array_size(v_subsections_1207_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkPartPostponed_spec__0(v_declName_1196_, v_subsections_1207_, v_sz_1212_, v___x_1210_, v___x_1208_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1213_, 0);
lean_dec(v_unused_1221_);
v___x_1215_ = v___x_1213_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_dec(v___x_1213_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1208_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1208_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
return v___x_1213_;
}
}
else
{
lean_dec(v_declName_1196_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed___boxed(lean_object* v_declName_1222_, lean_object* v_doc_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_declName_1222_, v_doc_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_doc_1223_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(lean_object* v_init_1238_, lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
if (lean_obj_tag(v_x_1239_) == 0)
{
lean_object* v_k_1247_; lean_object* v_v_1248_; lean_object* v_l_1249_; lean_object* v_r_1250_; lean_object* v___x_1251_; 
v_k_1247_ = lean_ctor_get(v_x_1239_, 1);
lean_inc(v_k_1247_);
v_v_1248_ = lean_ctor_get(v_x_1239_, 2);
lean_inc(v_v_1248_);
v_l_1249_ = lean_ctor_get(v_x_1239_, 3);
lean_inc(v_l_1249_);
v_r_1250_ = lean_ctor_get(v_x_1239_, 4);
lean_inc(v_r_1250_);
lean_dec_ref(v_x_1239_);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_init_1238_, v_l_1249_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v_a_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v_a_1253_ = lean_ctor_get(v_a_1252_, 0);
lean_inc(v_a_1253_);
lean_dec(v_a_1252_);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1));
v___x_1256_ = lean_st_mk_ref(v___x_1255_);
lean_inc(v_k_1247_);
v___x_1257_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_k_1247_, v_v_1248_, v___x_1256_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v_v_1248_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
lean_dec_ref(v___x_1257_);
v___x_1258_ = lean_st_ref_get(v___x_1256_);
lean_dec(v___x_1256_);
v___x_1259_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_1258_);
v___x_1260_ = lean_nat_dec_lt(v___x_1254_, v___x_1259_);
lean_dec(v___x_1259_);
if (v___x_1260_ == 0)
{
lean_dec(v___x_1258_);
lean_dec(v_k_1247_);
v_init_1238_ = v_a_1253_;
v_x_1239_ = v_r_1250_;
goto _start;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_k_1247_);
lean_ctor_set(v___x_1262_, 1, v___x_1258_);
v___x_1263_ = lean_array_push(v_a_1253_, v___x_1262_);
v_init_1238_ = v___x_1263_;
v_x_1239_ = v_r_1250_;
goto _start;
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v___x_1256_);
lean_dec(v_a_1253_);
lean_dec(v_r_1250_);
lean_dec(v_k_1247_);
v_a_1265_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1257_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1257_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
else
{
lean_dec(v_r_1250_);
lean_dec(v_v_1248_);
lean_dec(v_k_1247_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v_init_1238_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___boxed(lean_object* v_init_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_init_1275_, v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(lean_object* v_init_1285_, lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_object* v_k_1294_; lean_object* v_v_1295_; lean_object* v_l_1296_; lean_object* v_r_1297_; lean_object* v___x_1298_; 
v_k_1294_ = lean_ctor_get(v_x_1286_, 1);
lean_inc(v_k_1294_);
v_v_1295_ = lean_ctor_get(v_x_1286_, 2);
lean_inc(v_v_1295_);
v_l_1296_ = lean_ctor_get(v_x_1286_, 3);
lean_inc(v_l_1296_);
v_r_1297_ = lean_ctor_get(v_x_1286_, 4);
lean_inc(v_r_1297_);
lean_dec_ref(v_x_1286_);
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_init_1285_, v_l_1296_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v_a_1300_ = lean_ctor_get(v_a_1299_, 0);
lean_inc(v_a_1300_);
lean_dec(v_a_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1));
v___x_1303_ = lean_st_mk_ref(v___x_1302_);
lean_inc(v_k_1294_);
v___x_1304_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_k_1294_, v_v_1295_, v___x_1303_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v_v_1295_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
lean_dec_ref(v___x_1304_);
v___x_1305_ = lean_st_ref_get(v___x_1303_);
lean_dec(v___x_1303_);
v___x_1306_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_1305_);
v___x_1307_ = lean_nat_dec_lt(v___x_1301_, v___x_1306_);
lean_dec(v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec(v___x_1305_);
lean_dec(v_k_1294_);
v___x_1308_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_a_1300_, v_r_1297_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_k_1294_);
lean_ctor_set(v___x_1309_, 1, v___x_1305_);
v___x_1310_ = lean_array_push(v_a_1300_, v___x_1309_);
v___x_1311_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v___x_1310_, v_r_1297_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1311_;
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v___x_1303_);
lean_dec(v_a_1300_);
lean_dec(v_r_1297_);
lean_dec(v_k_1294_);
v_a_1312_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1304_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1304_);
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
else
{
lean_dec(v_r_1297_);
lean_dec(v_v_1295_);
lean_dec(v_k_1294_);
return v___x_1298_;
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_init_1285_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9___boxed(lean_object* v_init_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(v_init_1322_, v_x_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(lean_object* v_as_1332_, size_t v_sz_1333_, size_t v_i_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1334_, v_sz_1333_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1335_);
return v___x_1344_;
}
else
{
lean_object* v_a_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1375_; 
v_a_1345_ = lean_array_uget(v_as_1332_, v_i_1334_);
v_fst_1346_ = lean_ctor_get(v_a_1345_, 0);
v_snd_1347_ = lean_ctor_get(v_a_1345_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1349_ = v_a_1345_;
v_isShared_1350_ = v_isSharedCheck_1375_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1346_);
lean_dec(v_a_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1375_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1));
v___x_1353_ = lean_st_mk_ref(v___x_1352_);
lean_inc(v_fst_1346_);
v___x_1354_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_fst_1346_, v_snd_1347_, v___x_1353_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v_snd_1347_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; lean_object* v_a_1357_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
lean_dec_ref(v___x_1354_);
v___x_1355_ = lean_st_ref_get(v___x_1353_);
lean_dec(v___x_1353_);
v___x_1361_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_1355_);
v___x_1362_ = lean_nat_dec_lt(v___x_1351_, v___x_1361_);
lean_dec(v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v___x_1355_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1346_);
v_a_1357_ = v_b_1335_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1364_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1355_);
v___x_1364_ = v___x_1349_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_fst_1346_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1355_);
v___x_1364_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_array_push(v_b_1335_, v___x_1364_);
v_a_1357_ = v___x_1365_;
goto v___jp_1356_;
}
}
v___jp_1356_:
{
size_t v___x_1358_; size_t v___x_1359_; 
v___x_1358_ = ((size_t)1ULL);
v___x_1359_ = lean_usize_add(v_i_1334_, v___x_1358_);
v_i_1334_ = v___x_1359_;
v_b_1335_ = v_a_1357_;
goto _start;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1353_);
lean_del_object(v___x_1349_);
lean_dec(v_fst_1346_);
lean_dec_ref(v_b_1335_);
v_a_1367_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1354_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1354_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0___boxed(lean_object* v_as_1376_, lean_object* v_sz_1377_, lean_object* v_i_1378_, lean_object* v_b_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1377_);
lean_dec(v_sz_1377_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1378_);
lean_dec(v_i_1378_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(v_as_1376_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v_as_1376_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
uint8_t v___x_1401_; 
v___x_1401_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_b_1393_);
return v___x_1402_;
}
else
{
lean_object* v_a_1403_; lean_object* v_fst_1404_; lean_object* v_snd_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1433_; 
v_a_1403_ = lean_array_uget(v_as_1390_, v_i_1392_);
v_fst_1404_ = lean_ctor_get(v_a_1403_, 0);
v_snd_1405_ = lean_ctor_get(v_a_1403_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_a_1403_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1407_ = v_a_1403_;
v_isShared_1408_ = v_isSharedCheck_1433_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_snd_1405_);
lean_inc(v_fst_1404_);
lean_dec(v_a_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1433_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7___closed__1));
v___x_1411_ = lean_st_mk_ref(v___x_1410_);
lean_inc(v_fst_1404_);
v___x_1412_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_checkDocStringPostponed(v_fst_1404_, v_snd_1405_, v___x_1411_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v_snd_1405_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; lean_object* v_a_1415_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
lean_dec_ref(v___x_1412_);
v___x_1413_ = lean_st_ref_get(v___x_1411_);
lean_dec(v___x_1411_);
v___x_1419_ = l___private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_Stats_total(v___x_1413_);
v___x_1420_ = lean_nat_dec_lt(v___x_1409_, v___x_1419_);
lean_dec(v___x_1419_);
if (v___x_1420_ == 0)
{
lean_dec(v___x_1413_);
lean_del_object(v___x_1407_);
lean_dec(v_fst_1404_);
v_a_1415_ = v_b_1393_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1422_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 1, v___x_1413_);
v___x_1422_ = v___x_1407_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_fst_1404_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1413_);
v___x_1422_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_array_push(v_b_1393_, v___x_1422_);
v_a_1415_ = v___x_1423_;
goto v___jp_1414_;
}
}
v___jp_1414_:
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1392_, v___x_1416_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0_spec__0(v_as_1390_, v_sz_1391_, v___x_1417_, v_a_1415_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1418_;
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v___x_1411_);
lean_del_object(v___x_1407_);
lean_dec(v_fst_1404_);
lean_dec_ref(v_b_1393_);
v_a_1425_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1412_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1412_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0___boxed(lean_object* v_as_1434_, lean_object* v_sz_1435_, lean_object* v_i_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
size_t v_sz_boxed_1445_; size_t v_i_boxed_1446_; lean_object* v_res_1447_; 
v_sz_boxed_1445_ = lean_unbox_usize(v_sz_1435_);
lean_dec(v_sz_1435_);
v_i_boxed_1446_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(v_as_1434_, v_sz_boxed_1445_, v_i_boxed_1446_, v_b_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_as_1434_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(lean_object* v_as_1448_, size_t v_sz_1449_, size_t v_i_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_b_1451_);
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; size_t v_sz_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v_a_1461_ = lean_array_uget_borrowed(v_as_1448_, v_i_1450_);
v_sz_1462_ = lean_array_size(v_a_1461_);
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__0(v_a_1461_, v_sz_1462_, v___x_1463_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; size_t v___x_1466_; size_t v___x_1467_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1450_, v___x_1466_);
v_i_1450_ = v___x_1467_;
v_b_1451_ = v_a_1465_;
goto _start;
}
else
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8___boxed(lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(v_as_1469_, v_sz_boxed_1480_, v_i_boxed_1481_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_bs_1485_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1486_ == 0)
{
return v_bs_1485_;
}
else
{
lean_object* v_v_1487_; lean_object* v___x_1488_; lean_object* v_bs_x27_1489_; lean_object* v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v_v_1487_ = lean_array_uget(v_bs_1485_, v_i_1484_);
v___x_1488_ = lean_unsigned_to_nat(0u);
v_bs_x27_1489_ = lean_array_uset(v_bs_1485_, v_i_1484_, v___x_1488_);
v___x_1490_ = l_Lean_Exception_toMessageData(v_v_1487_);
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = lean_usize_add(v_i_1484_, v___x_1491_);
v___x_1493_ = lean_array_uset(v_bs_x27_1489_, v_i_1484_, v___x_1490_);
v_i_1484_ = v___x_1492_;
v_bs_1485_ = v___x_1493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1___boxed(lean_object* v_sz_1495_, lean_object* v_i_1496_, lean_object* v_bs_1497_){
_start:
{
size_t v_sz_boxed_1498_; size_t v_i_boxed_1499_; lean_object* v_res_1500_; 
v_sz_boxed_1498_ = lean_unbox_usize(v_sz_1495_);
lean_dec(v_sz_1495_);
v_i_boxed_1499_ = lean_unbox_usize(v_i_1496_);
lean_dec(v_i_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(v_sz_boxed_1498_, v_i_boxed_1499_, v_bs_1497_);
return v_res_1500_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1501_; double v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_float_of_nat(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__4));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__6));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__8));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__10));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(size_t v_sz_1519_, size_t v_i_1520_, lean_object* v_bs_1521_){
_start:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_usize_dec_lt(v_i_1520_, v_sz_1519_);
if (v___x_1522_ == 0)
{
return v_bs_1521_;
}
else
{
lean_object* v_v_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1573_; 
v_v_1523_ = lean_array_uget(v_bs_1521_, v_i_1520_);
v_fst_1524_ = lean_ctor_get(v_v_1523_, 0);
v_snd_1525_ = lean_ctor_get(v_v_1523_, 1);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_v_1523_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1527_ = v_v_1523_;
v_isShared_1528_ = v_isSharedCheck_1573_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_snd_1525_);
lean_inc(v_fst_1524_);
lean_dec(v_v_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1573_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; double v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_passed_1535_; lean_object* v_failed_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1572_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0);
v___x_1532_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1));
v___x_1533_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__3));
v___x_1534_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1529_);
lean_ctor_set(v___x_1534_, 2, v___x_1532_);
lean_ctor_set_float(v___x_1534_, sizeof(void*)*3, v___x_1531_);
lean_ctor_set_float(v___x_1534_, sizeof(void*)*3 + 8, v___x_1531_);
lean_ctor_set_uint8(v___x_1534_, sizeof(void*)*3 + 16, v___x_1522_);
v_passed_1535_ = lean_ctor_get(v_snd_1525_, 0);
v_failed_1536_ = lean_ctor_get(v_snd_1525_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_snd_1525_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1538_ = v_snd_1525_;
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_failed_1536_);
lean_inc(v_passed_1535_);
lean_dec(v_snd_1525_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v_bs_x27_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5);
v___x_1541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7);
v_bs_x27_1542_ = lean_array_uset(v_bs_1521_, v_i_1520_, v___x_1530_);
v___x_1543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__9);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_MessageData_ofConstName(v_fst_1524_, v___x_1544_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 7);
lean_ctor_set(v___x_1538_, 1, v___x_1545_);
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1547_ = v___x_1538_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__11);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 7);
lean_ctor_set(v___x_1527_, 1, v___x_1548_);
lean_ctor_set(v___x_1527_, 0, v___x_1547_);
v___x_1550_ = v___x_1527_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1551_ = l_Nat_reprFast(v_passed_1535_);
v___x_1552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
v___x_1553_ = l_Lean_MessageData_ofFormat(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1550_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1540_);
v___x_1556_ = lean_array_get_size(v_failed_1536_);
v___x_1557_ = l_Nat_reprFast(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
v___x_1559_ = l_Lean_MessageData_ofFormat(v___x_1558_);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1555_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___x_1541_);
v_sz_1562_ = lean_array_size(v_failed_1536_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__1(v_sz_1562_, v___x_1563_, v_failed_1536_);
v___x_1565_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1534_);
lean_ctor_set(v___x_1565_, 1, v___x_1561_);
lean_ctor_set(v___x_1565_, 2, v___x_1564_);
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1520_, v___x_1566_);
v___x_1568_ = lean_array_uset(v_bs_x27_1542_, v_i_1520_, v___x_1565_);
v_i_1520_ = v___x_1567_;
v_bs_1521_ = v___x_1568_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___boxed(lean_object* v_sz_1574_, lean_object* v_i_1575_, lean_object* v_bs_1576_){
_start:
{
size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1574_);
lean_dec(v_sz_1574_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1575_);
lean_dec(v_i_1575_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(v_sz_boxed_1577_, v_i_boxed_1578_, v_bs_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(size_t v_sz_1580_, size_t v_i_1581_, lean_object* v_bs_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1581_, v_sz_1580_);
if (v___x_1583_ == 0)
{
return v_bs_1582_;
}
else
{
lean_object* v_v_1584_; lean_object* v_snd_1585_; lean_object* v_passed_1586_; lean_object* v___x_1587_; lean_object* v_bs_x27_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v_v_1584_ = lean_array_uget_borrowed(v_bs_1582_, v_i_1581_);
v_snd_1585_ = lean_ctor_get(v_v_1584_, 1);
v_passed_1586_ = lean_ctor_get(v_snd_1585_, 0);
lean_inc(v_passed_1586_);
v___x_1587_ = lean_unsigned_to_nat(0u);
v_bs_x27_1588_ = lean_array_uset(v_bs_1582_, v_i_1581_, v___x_1587_);
v___x_1589_ = ((size_t)1ULL);
v___x_1590_ = lean_usize_add(v_i_1581_, v___x_1589_);
v___x_1591_ = lean_array_uset(v_bs_x27_1588_, v_i_1581_, v_passed_1586_);
v_i_1581_ = v___x_1590_;
v_bs_1582_ = v___x_1591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6___boxed(lean_object* v_sz_1593_, lean_object* v_i_1594_, lean_object* v_bs_1595_){
_start:
{
size_t v_sz_boxed_1596_; size_t v_i_boxed_1597_; lean_object* v_res_1598_; 
v_sz_boxed_1596_ = lean_unbox_usize(v_sz_1593_);
lean_dec(v_sz_1593_);
v_i_boxed_1597_ = lean_unbox_usize(v_i_1594_);
lean_dec(v_i_1594_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(v_sz_boxed_1596_, v_i_boxed_1597_, v_bs_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(lean_object* v_as_1599_, size_t v_i_1600_, size_t v_stop_1601_, lean_object* v_b_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_eq(v_i_1600_, v_stop_1601_);
if (v___x_1603_ == 0)
{
size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_sub(v_i_1600_, v___x_1604_);
v___x_1606_ = lean_array_uget_borrowed(v_as_1599_, v___x_1605_);
v___x_1607_ = lean_nat_add(v___x_1606_, v_b_1602_);
lean_dec(v_b_1602_);
v_i_1600_ = v___x_1605_;
v_b_1602_ = v___x_1607_;
goto _start;
}
else
{
return v_b_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5___boxed(lean_object* v_as_1609_, lean_object* v_i_1610_, lean_object* v_stop_1611_, lean_object* v_b_1612_){
_start:
{
size_t v_i_boxed_1613_; size_t v_stop_boxed_1614_; lean_object* v_res_1615_; 
v_i_boxed_1613_ = lean_unbox_usize(v_i_1610_);
lean_dec(v_i_1610_);
v_stop_boxed_1614_ = lean_unbox_usize(v_stop_1611_);
lean_dec(v_stop_1611_);
v_res_1615_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v_as_1609_, v_i_boxed_1613_, v_stop_boxed_1614_, v_b_1612_);
lean_dec_ref(v_as_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(size_t v_sz_1616_, size_t v_i_1617_, lean_object* v_bs_1618_){
_start:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_usize_dec_lt(v_i_1617_, v_sz_1616_);
if (v___x_1619_ == 0)
{
return v_bs_1618_;
}
else
{
lean_object* v_v_1620_; lean_object* v_snd_1621_; lean_object* v_failed_1622_; lean_object* v___x_1623_; lean_object* v_bs_x27_1624_; lean_object* v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v_v_1620_ = lean_array_uget_borrowed(v_bs_1618_, v_i_1617_);
v_snd_1621_ = lean_ctor_get(v_v_1620_, 1);
v_failed_1622_ = lean_ctor_get(v_snd_1621_, 1);
lean_inc_ref(v_failed_1622_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v_bs_x27_1624_ = lean_array_uset(v_bs_1618_, v_i_1617_, v___x_1623_);
v___x_1625_ = lean_array_get_size(v_failed_1622_);
lean_dec_ref(v_failed_1622_);
v___x_1626_ = ((size_t)1ULL);
v___x_1627_ = lean_usize_add(v_i_1617_, v___x_1626_);
v___x_1628_ = lean_array_uset(v_bs_x27_1624_, v_i_1617_, v___x_1625_);
v_i_1617_ = v___x_1627_;
v_bs_1618_ = v___x_1628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4___boxed(lean_object* v_sz_1630_, lean_object* v_i_1631_, lean_object* v_bs_1632_){
_start:
{
size_t v_sz_boxed_1633_; size_t v_i_boxed_1634_; lean_object* v_res_1635_; 
v_sz_boxed_1633_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1634_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(v_sz_boxed_1633_, v_i_boxed_1634_, v_bs_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0(uint8_t v___y_1644_, uint8_t v_suppressElabErrors_1645_, lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 1)
{
lean_object* v_pre_1647_; 
v_pre_1647_ = lean_ctor_get(v_x_1646_, 0);
switch(lean_obj_tag(v_pre_1647_))
{
case 1:
{
lean_object* v_pre_1648_; 
v_pre_1648_ = lean_ctor_get(v_pre_1647_, 0);
switch(lean_obj_tag(v_pre_1648_))
{
case 0:
{
lean_object* v_str_1649_; lean_object* v_str_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_str_1649_ = lean_ctor_get(v_x_1646_, 1);
v_str_1650_ = lean_ctor_get(v_pre_1647_, 1);
v___x_1651_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__0));
v___x_1652_ = lean_string_dec_eq(v_str_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__1));
v___x_1654_ = lean_string_dec_eq(v_str_1650_, v___x_1653_);
if (v___x_1654_ == 0)
{
return v___y_1644_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__2));
v___x_1656_ = lean_string_dec_eq(v_str_1649_, v___x_1655_);
if (v___x_1656_ == 0)
{
return v___y_1644_;
}
else
{
return v_suppressElabErrors_1645_;
}
}
}
else
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__3));
v___x_1658_ = lean_string_dec_eq(v_str_1649_, v___x_1657_);
if (v___x_1658_ == 0)
{
return v___y_1644_;
}
else
{
return v_suppressElabErrors_1645_;
}
}
}
case 1:
{
lean_object* v_pre_1659_; 
v_pre_1659_ = lean_ctor_get(v_pre_1648_, 0);
if (lean_obj_tag(v_pre_1659_) == 0)
{
lean_object* v_str_1660_; lean_object* v_str_1661_; lean_object* v_str_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_str_1660_ = lean_ctor_get(v_x_1646_, 1);
v_str_1661_ = lean_ctor_get(v_pre_1647_, 1);
v_str_1662_ = lean_ctor_get(v_pre_1648_, 1);
v___x_1663_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__4));
v___x_1664_ = lean_string_dec_eq(v_str_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
return v___y_1644_;
}
else
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__5));
v___x_1666_ = lean_string_dec_eq(v_str_1661_, v___x_1665_);
if (v___x_1666_ == 0)
{
return v___y_1644_;
}
else
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__6));
v___x_1668_ = lean_string_dec_eq(v_str_1660_, v___x_1667_);
if (v___x_1668_ == 0)
{
return v___y_1644_;
}
else
{
return v_suppressElabErrors_1645_;
}
}
}
}
else
{
return v___y_1644_;
}
}
default: 
{
return v___y_1644_;
}
}
}
case 0:
{
lean_object* v_str_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_str_1669_ = lean_ctor_get(v_x_1646_, 1);
v___x_1670_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___closed__7));
v___x_1671_ = lean_string_dec_eq(v_str_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
return v___y_1644_;
}
else
{
return v_suppressElabErrors_1645_;
}
}
default: 
{
return v___y_1644_;
}
}
}
else
{
return v___y_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___boxed(lean_object* v___y_1672_, lean_object* v_suppressElabErrors_1673_, lean_object* v_x_1674_){
_start:
{
uint8_t v___y_12662__boxed_1675_; uint8_t v_suppressElabErrors_boxed_1676_; uint8_t v_res_1677_; lean_object* v_r_1678_; 
v___y_12662__boxed_1675_ = lean_unbox(v___y_1672_);
v_suppressElabErrors_boxed_1676_ = lean_unbox(v_suppressElabErrors_1673_);
v_res_1677_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0(v___y_12662__boxed_1675_, v_suppressElabErrors_boxed_1676_, v_x_1674_);
lean_dec(v_x_1674_);
v_r_1678_ = lean_box(v_res_1677_);
return v_r_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(lean_object* v_ref_1679_, lean_object* v_msgData_1680_, uint8_t v_severity_1681_, uint8_t v_isSilent_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
uint8_t v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; uint8_t v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1725_; uint8_t v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; uint8_t v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1750_; uint8_t v___y_1751_; uint8_t v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1761_; uint8_t v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; uint8_t v___y_1765_; lean_object* v___y_1766_; uint8_t v___y_1767_; uint8_t v___x_1772_; lean_object* v___y_1774_; uint8_t v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; uint8_t v___y_1779_; uint8_t v___y_1780_; uint8_t v___y_1782_; uint8_t v___x_1797_; 
v___x_1772_ = 2;
v___x_1797_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1681_, v___x_1772_);
if (v___x_1797_ == 0)
{
v___y_1782_ = v___x_1797_;
goto v___jp_1781_;
}
else
{
uint8_t v___x_1798_; 
lean_inc_ref(v_msgData_1680_);
v___x_1798_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1680_);
v___y_1782_ = v___x_1798_;
goto v___jp_1781_;
}
v___jp_1688_:
{
lean_object* v___x_1698_; lean_object* v_currNamespace_1699_; lean_object* v_openDecls_1700_; lean_object* v_env_1701_; lean_object* v_nextMacroScope_1702_; lean_object* v_ngen_1703_; lean_object* v_auxDeclNGen_1704_; lean_object* v_traceState_1705_; lean_object* v_cache_1706_; lean_object* v_messages_1707_; lean_object* v_infoState_1708_; lean_object* v_snapshotTasks_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1723_; 
v___x_1698_ = lean_st_ref_take(v___y_1697_);
v_currNamespace_1699_ = lean_ctor_get(v___y_1696_, 6);
v_openDecls_1700_ = lean_ctor_get(v___y_1696_, 7);
v_env_1701_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1702_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1703_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1704_ = lean_ctor_get(v___x_1698_, 3);
v_traceState_1705_ = lean_ctor_get(v___x_1698_, 4);
v_cache_1706_ = lean_ctor_get(v___x_1698_, 5);
v_messages_1707_ = lean_ctor_get(v___x_1698_, 6);
v_infoState_1708_ = lean_ctor_get(v___x_1698_, 7);
v_snapshotTasks_1709_ = lean_ctor_get(v___x_1698_, 8);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1711_ = v___x_1698_;
v_isShared_1712_ = v_isSharedCheck_1723_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_snapshotTasks_1709_);
lean_inc(v_infoState_1708_);
lean_inc(v_messages_1707_);
lean_inc(v_cache_1706_);
lean_inc(v_traceState_1705_);
lean_inc(v_auxDeclNGen_1704_);
lean_inc(v_ngen_1703_);
lean_inc(v_nextMacroScope_1702_);
lean_inc(v_env_1701_);
lean_dec(v___x_1698_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1723_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_inc(v_openDecls_1700_);
lean_inc(v_currNamespace_1699_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_currNamespace_1699_);
lean_ctor_set(v___x_1713_, 1, v_openDecls_1700_);
v___x_1714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___y_1690_);
lean_inc_ref(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1715_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1715_, 0, v___y_1694_);
lean_ctor_set(v___x_1715_, 1, v___y_1692_);
lean_ctor_set(v___x_1715_, 2, v___y_1691_);
lean_ctor_set(v___x_1715_, 3, v___y_1695_);
lean_ctor_set(v___x_1715_, 4, v___x_1714_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*5, v___y_1693_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*5 + 1, v___y_1689_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*5 + 2, v_isSilent_1682_);
v___x_1716_ = l_Lean_MessageLog_add(v___x_1715_, v_messages_1707_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 6, v___x_1716_);
v___x_1718_ = v___x_1711_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_env_1701_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_nextMacroScope_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_ngen_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_auxDeclNGen_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_traceState_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_cache_1706_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_infoState_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_snapshotTasks_1709_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_st_ref_set(v___y_1697_, v___x_1718_);
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
return v___x_1721_;
}
}
}
v___jp_1724_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1748_; 
v___x_1733_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1680_);
v___x_1734_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__3(v___x_1733_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1737_ = v___x_1734_;
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
lean_inc_ref_n(v___y_1731_, 2);
v___x_1739_ = l_Lean_FileMap_toPosition(v___y_1731_, v___y_1728_);
lean_dec(v___y_1728_);
v___x_1740_ = l_Lean_FileMap_toPosition(v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1));
if (v___y_1727_ == 0)
{
lean_del_object(v___x_1737_);
lean_dec_ref(v___y_1725_);
v___y_1689_ = v___y_1726_;
v___y_1690_ = v_a_1735_;
v___y_1691_ = v___x_1741_;
v___y_1692_ = v___x_1739_;
v___y_1693_ = v___y_1730_;
v___y_1694_ = v___y_1729_;
v___y_1695_ = v___x_1742_;
v___y_1696_ = v___y_1685_;
v___y_1697_ = v___y_1686_;
goto v___jp_1688_;
}
else
{
uint8_t v___x_1743_; 
lean_inc(v_a_1735_);
v___x_1743_ = l_Lean_MessageData_hasTag(v___y_1725_, v_a_1735_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec_ref(v___x_1741_);
lean_dec_ref(v___x_1739_);
lean_dec(v_a_1735_);
v___x_1744_ = lean_box(0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1744_);
v___x_1746_ = v___x_1737_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
else
{
lean_del_object(v___x_1737_);
v___y_1689_ = v___y_1726_;
v___y_1690_ = v_a_1735_;
v___y_1691_ = v___x_1741_;
v___y_1692_ = v___x_1739_;
v___y_1693_ = v___y_1730_;
v___y_1694_ = v___y_1729_;
v___y_1695_ = v___x_1742_;
v___y_1696_ = v___y_1685_;
v___y_1697_ = v___y_1686_;
goto v___jp_1688_;
}
}
}
}
v___jp_1749_:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Syntax_getTailPos_x3f(v___y_1753_, v___y_1754_);
lean_dec(v___y_1753_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_inc(v___y_1757_);
v___y_1725_ = v___y_1750_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___y_1757_;
v___y_1729_ = v___y_1755_;
v___y_1730_ = v___y_1754_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1757_;
goto v___jp_1724_;
}
else
{
lean_object* v_val_1759_; 
v_val_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_val_1759_);
lean_dec_ref(v___x_1758_);
v___y_1725_ = v___y_1750_;
v___y_1726_ = v___y_1751_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___y_1757_;
v___y_1729_ = v___y_1755_;
v___y_1730_ = v___y_1754_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v_val_1759_;
goto v___jp_1724_;
}
}
v___jp_1760_:
{
lean_object* v_ref_1768_; lean_object* v___x_1769_; 
v_ref_1768_ = l_Lean_replaceRef(v_ref_1679_, v___y_1763_);
v___x_1769_ = l_Lean_Syntax_getPos_x3f(v_ref_1768_, v___y_1765_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___y_1750_ = v___y_1761_;
v___y_1751_ = v___y_1767_;
v___y_1752_ = v___y_1762_;
v___y_1753_ = v_ref_1768_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1764_;
v___y_1756_ = v___y_1766_;
v___y_1757_ = v___x_1770_;
goto v___jp_1749_;
}
else
{
lean_object* v_val_1771_; 
v_val_1771_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_val_1771_);
lean_dec_ref(v___x_1769_);
v___y_1750_ = v___y_1761_;
v___y_1751_ = v___y_1767_;
v___y_1752_ = v___y_1762_;
v___y_1753_ = v_ref_1768_;
v___y_1754_ = v___y_1765_;
v___y_1755_ = v___y_1764_;
v___y_1756_ = v___y_1766_;
v___y_1757_ = v_val_1771_;
goto v___jp_1749_;
}
}
v___jp_1773_:
{
if (v___y_1780_ == 0)
{
v___y_1761_ = v___y_1774_;
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1779_;
v___y_1766_ = v___y_1778_;
v___y_1767_ = v_severity_1681_;
goto v___jp_1760_;
}
else
{
v___y_1761_ = v___y_1774_;
v___y_1762_ = v___y_1775_;
v___y_1763_ = v___y_1776_;
v___y_1764_ = v___y_1777_;
v___y_1765_ = v___y_1779_;
v___y_1766_ = v___y_1778_;
v___y_1767_ = v___x_1772_;
goto v___jp_1760_;
}
}
v___jp_1781_:
{
if (v___y_1782_ == 0)
{
lean_object* v_fileName_1783_; lean_object* v_fileMap_1784_; lean_object* v_options_1785_; lean_object* v_ref_1786_; uint8_t v_suppressElabErrors_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; 
v_fileName_1783_ = lean_ctor_get(v___y_1685_, 0);
v_fileMap_1784_ = lean_ctor_get(v___y_1685_, 1);
v_options_1785_ = lean_ctor_get(v___y_1685_, 2);
v_ref_1786_ = lean_ctor_get(v___y_1685_, 5);
v_suppressElabErrors_1787_ = lean_ctor_get_uint8(v___y_1685_, sizeof(void*)*14 + 1);
v___x_1788_ = lean_box(v___y_1782_);
v___x_1789_ = lean_box(v_suppressElabErrors_1787_);
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1790_, 0, v___x_1788_);
lean_closure_set(v___f_1790_, 1, v___x_1789_);
v___x_1791_ = 1;
v___x_1792_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1681_, v___x_1791_);
if (v___x_1792_ == 0)
{
v___y_1774_ = v___f_1790_;
v___y_1775_ = v_suppressElabErrors_1787_;
v___y_1776_ = v_ref_1786_;
v___y_1777_ = v_fileName_1783_;
v___y_1778_ = v_fileMap_1784_;
v___y_1779_ = v___y_1782_;
v___y_1780_ = v___x_1792_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = l_Lean_warningAsError;
v___x_1794_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DocString_Builtin_Postponed_0__Lean_Doc_getHandlerUnsafe_spec__0_spec__0_spec__1_spec__4_spec__5(v_options_1785_, v___x_1793_);
v___y_1774_ = v___f_1790_;
v___y_1775_ = v_suppressElabErrors_1787_;
v___y_1776_ = v_ref_1786_;
v___y_1777_ = v_fileName_1783_;
v___y_1778_ = v_fileMap_1784_;
v___y_1779_ = v___y_1782_;
v___y_1780_ = v___x_1794_;
goto v___jp_1773_;
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec_ref(v_msgData_1680_);
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_ref_1799_, lean_object* v_msgData_1800_, lean_object* v_severity_1801_, lean_object* v_isSilent_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
uint8_t v_severity_boxed_1808_; uint8_t v_isSilent_boxed_1809_; lean_object* v_res_1810_; 
v_severity_boxed_1808_ = lean_unbox(v_severity_1801_);
v_isSilent_boxed_1809_ = lean_unbox(v_isSilent_1802_);
v_res_1810_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_1799_, v_msgData_1800_, v_severity_boxed_1808_, v_isSilent_boxed_1809_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v_ref_1799_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(lean_object* v_msgData_1811_, uint8_t v_severity_1812_, uint8_t v_isSilent_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_ref_1821_; lean_object* v___x_1822_; 
v_ref_1821_ = lean_ctor_get(v___y_1818_, 5);
v___x_1822_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_1821_, v_msgData_1811_, v_severity_1812_, v_isSilent_1813_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4___boxed(lean_object* v_msgData_1823_, lean_object* v_severity_1824_, lean_object* v_isSilent_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v_severity_boxed_1833_; uint8_t v_isSilent_boxed_1834_; lean_object* v_res_1835_; 
v_severity_boxed_1833_ = lean_unbox(v_severity_1824_);
v_isSilent_boxed_1834_ = lean_unbox(v_isSilent_1825_);
v_res_1835_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(v_msgData_1823_, v_severity_boxed_1833_, v_isSilent_boxed_1834_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(lean_object* v_msgData_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = 0;
v___x_1845_ = 0;
v___x_1846_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4(v_msgData_1836_, v___x_1844_, v___x_1845_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3___boxed(lean_object* v_msgData_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(v_msgData_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
return v_res_1855_;
}
}
static lean_object* _init_l_Lean_Doc_checkPostponed___closed__2(void){
_start:
{
lean_object* v___x_1859_; uint8_t v___x_1860_; double v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__1));
v___x_1860_ = 1;
v___x_1861_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__0);
v___x_1862_ = lean_box(0);
v___x_1863_ = ((lean_object*)(l_Lean_Doc_checkPostponed___closed__1));
v___x_1864_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
lean_ctor_set(v___x_1864_, 2, v___x_1859_);
lean_ctor_set_float(v___x_1864_, sizeof(void*)*3, v___x_1861_);
lean_ctor_set_float(v___x_1864_, sizeof(void*)*3 + 8, v___x_1861_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*3 + 16, v___x_1860_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_Doc_checkPostponed___closed__4(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_Lean_Doc_checkPostponed___closed__3));
v___x_1867_ = l_Lean_stringToMessageData(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_Doc_checkPostponed___closed__6(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_Doc_checkPostponed___closed__5));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lean_Doc_checkPostponed___closed__8(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_box(1);
v___x_1874_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_checkPostponed(lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v_a_1918_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_toEnvExtension_1938_; lean_object* v_asyncMode_1939_; lean_object* v___x_1940_; 
v___x_1936_ = lean_st_ref_get(v_a_1880_);
v___x_1937_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1938_ = lean_ctor_get(v___x_1937_, 0);
v_asyncMode_1939_ = lean_ctor_get(v_toEnvExtension_1938_, 2);
v___x_1940_ = l_Lean_getBuiltinVersoDocStrings();
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_checked_1942_; lean_object* v___x_1943_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref(v___x_1940_);
v_checked_1942_ = ((lean_object*)(l_Lean_Doc_checkPostponed___closed__7));
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__7(v_checked_1942_, v_a_1941_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_env_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v_a_1950_; lean_object* v_a_1976_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v_env_1945_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1945_);
lean_dec(v___x_1936_);
v___x_1946_ = lean_obj_once(&l_Lean_Doc_checkPostponed___closed__8, &l_Lean_Doc_checkPostponed___closed__8_once, _init_l_Lean_Doc_checkPostponed___closed__8);
v___x_1947_ = lean_box(0);
v___x_1948_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1946_, v_toEnvExtension_1938_, v_env_1945_, v_asyncMode_1939_, v___x_1947_);
v_a_1976_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_a_1976_);
lean_dec(v_a_1944_);
v_a_1950_ = v_a_1976_;
goto v___jp_1949_;
v___jp_1949_:
{
lean_object* v_importedEntries_1951_; lean_object* v_state_1952_; size_t v_sz_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v_importedEntries_1951_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_ref(v_importedEntries_1951_);
v_state_1952_ = lean_ctor_get(v___x_1948_, 1);
lean_inc(v_state_1952_);
lean_dec(v___x_1948_);
v_sz_1953_ = lean_array_size(v_importedEntries_1951_);
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Doc_checkPostponed_spec__8(v_importedEntries_1951_, v_sz_1953_, v___x_1954_, v_a_1950_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec_ref(v_importedEntries_1951_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___x_1955_);
v___x_1957_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Doc_checkPostponed_spec__9(v_a_1956_, v_state_1952_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v_a_1959_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
v_a_1959_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_a_1959_);
lean_dec(v_a_1958_);
v_a_1918_ = v_a_1959_;
goto v___jp_1917_;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1957_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1957_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v_state_1952_);
v_a_1968_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1955_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1955_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v___x_1936_);
v_a_1977_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1943_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1943_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v___x_1936_);
v_a_1985_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1987_ = v___x_1940_;
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1940_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1997_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_ref_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v_ref_1989_ = lean_ctor_get(v_a_1879_, 5);
v___x_1990_ = lean_io_error_to_string(v_a_1985_);
v___x_1991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
v___x_1992_ = l_Lean_MessageData_ofFormat(v___x_1991_);
lean_inc(v_ref_1989_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v_ref_1989_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1993_);
v___x_1995_ = v___x_1987_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
v___jp_1882_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; size_t v_sz_1893_; size_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1887_ = l_Nat_reprFast(v___y_1886_);
v___x_1888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
v___x_1889_ = l_Lean_MessageData_ofFormat(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1885_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__7);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v_sz_1893_ = lean_array_size(v___y_1883_);
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2(v_sz_1893_, v___x_1894_, v___y_1883_);
lean_inc_ref(v___y_1884_);
v___x_1896_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1896_, 0, v___y_1884_);
lean_ctor_set(v___x_1896_, 1, v___x_1892_);
lean_ctor_set(v___x_1896_, 2, v___x_1895_);
v___x_1897_ = l_Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3(v___x_1896_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; size_t v_sz_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1904_ = l_Nat_reprFast(v___y_1903_);
v___x_1905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_ofFormat(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___y_1901_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__2___closed__5);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v_sz_1910_ = lean_array_size(v___y_1899_);
v___x_1911_ = ((size_t)0ULL);
lean_inc_ref(v___y_1899_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__4(v_sz_1910_, v___x_1911_, v___y_1899_);
v___x_1913_ = lean_array_get_size(v___x_1912_);
v___x_1914_ = lean_nat_dec_lt(v___y_1902_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_dec_ref(v___x_1912_);
v___y_1883_ = v___y_1899_;
v___y_1884_ = v___y_1900_;
v___y_1885_ = v___x_1909_;
v___y_1886_ = v___y_1902_;
goto v___jp_1882_;
}
else
{
size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_usize_of_nat(v___x_1913_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v___x_1912_, v___x_1915_, v___x_1911_, v___y_1902_);
lean_dec_ref(v___x_1912_);
v___y_1883_ = v___y_1899_;
v___y_1884_ = v___y_1900_;
v___y_1885_ = v___x_1909_;
v___y_1886_ = v___x_1916_;
goto v___jp_1882_;
}
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; size_t v_sz_1929_; size_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_obj_once(&l_Lean_Doc_checkPostponed___closed__2, &l_Lean_Doc_checkPostponed___closed__2_once, _init_l_Lean_Doc_checkPostponed___closed__2);
v___x_1921_ = lean_obj_once(&l_Lean_Doc_checkPostponed___closed__4, &l_Lean_Doc_checkPostponed___closed__4_once, _init_l_Lean_Doc_checkPostponed___closed__4);
v___x_1922_ = lean_array_get_size(v_a_1918_);
v___x_1923_ = l_Nat_reprFast(v___x_1922_);
v___x_1924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
v___x_1925_ = l_Lean_MessageData_ofFormat(v___x_1924_);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1921_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_obj_once(&l_Lean_Doc_checkPostponed___closed__6, &l_Lean_Doc_checkPostponed___closed__6_once, _init_l_Lean_Doc_checkPostponed___closed__6);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v_sz_1929_ = lean_array_size(v_a_1918_);
v___x_1930_ = ((size_t)0ULL);
lean_inc_ref(v_a_1918_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_checkPostponed_spec__6(v_sz_1929_, v___x_1930_, v_a_1918_);
v___x_1932_ = lean_array_get_size(v___x_1931_);
v___x_1933_ = lean_nat_dec_lt(v___x_1919_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec_ref(v___x_1931_);
v___y_1899_ = v_a_1918_;
v___y_1900_ = v___x_1920_;
v___y_1901_ = v___x_1928_;
v___y_1902_ = v___x_1919_;
v___y_1903_ = v___x_1919_;
goto v___jp_1898_;
}
else
{
size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_usize_of_nat(v___x_1932_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Doc_checkPostponed_spec__5(v___x_1931_, v___x_1934_, v___x_1930_, v___x_1919_);
lean_dec_ref(v___x_1931_);
v___y_1899_ = v_a_1918_;
v___y_1900_ = v___x_1920_;
v___y_1901_ = v___x_1928_;
v___y_1902_ = v___x_1919_;
v___y_1903_ = v___x_1935_;
goto v___jp_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_checkPostponed___boxed(lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Doc_checkPostponed(v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5(lean_object* v_ref_2006_, lean_object* v_msgData_2007_, uint8_t v_severity_2008_, uint8_t v_isSilent_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___redArg(v_ref_2006_, v_msgData_2007_, v_severity_2008_, v_isSilent_2009_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5___boxed(lean_object* v_ref_2018_, lean_object* v_msgData_2019_, lean_object* v_severity_2020_, lean_object* v_isSilent_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_severity_boxed_2029_; uint8_t v_isSilent_boxed_2030_; lean_object* v_res_2031_; 
v_severity_boxed_2029_ = lean_unbox(v_severity_2020_);
v_isSilent_boxed_2030_ = lean_unbox(v_isSilent_2021_);
v_res_2031_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Doc_checkPostponed_spec__3_spec__4_spec__5(v_ref_2018_, v_msgData_2019_, v_severity_boxed_2029_, v_isSilent_boxed_2030_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v_ref_2018_);
return v_res_2031_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_instToExprPostponedImport = _init_l_Lean_Doc_instToExprPostponedImport();
lean_mark_persistent(l_Lean_Doc_instToExprPostponedImport);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Postponed(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Postponed(builtin);
}
#ifdef __cplusplus
}
#endif
