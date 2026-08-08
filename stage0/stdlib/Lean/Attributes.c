// Lean compiler output
// Module: Lean.Attributes
// Imports: public import Lean.CoreM public import Lean.Compiler.MetaAttr
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeApplicationTime;
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeApplicationTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeApplicationTime_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeApplicationTime___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeApplicationTime = (const lean_object*)&l_Lean_instBEqAttributeApplicationTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMonadLiftImportMAttrM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMonadLiftImportMAttrM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instMonadLiftImportMAttrM___closed__0 = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMonadLiftImportMAttrM = (const lean_object*)&l_Lean_instMonadLiftImportMAttrM___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__0 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__1 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__2 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__3 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__4 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__4_value;
static const lean_array_object l_Lean_AttributeImplCore_ref___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__5 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__5_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__6 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__7 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__7_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__8 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__9 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__9_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__10 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__11 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__12;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__13;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__14 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__15 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_1),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_AttributeImplCore_ref___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value_aux_2),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__16 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__16_value;
static const lean_string_object l_Lean_AttributeImplCore_ref___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__17 = (const lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__17_value;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__18;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__19;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__20;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__21;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__22;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__23;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__24;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__25;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__26;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__27;
static lean_once_cell_t l_Lean_AttributeImplCore_ref___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_AttributeImplCore_ref___autoParam___closed__28;
LEAN_EXPORT lean_object* l_Lean_AttributeImplCore_ref___autoParam;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "instInhabitedAttributeImplCore"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_0),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 168, 67, 30, 9, 195, 195, 250)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value_aux_1),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 28, 76, 169, 127, 73, 161, 93)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value;
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore_default = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAttributeKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAttributeKind___closed__0 = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAttributeKind = (const lean_object*)&l_Lean_instBEqAttributeKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedAttributeKind;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringAttributeKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_instToStringAttributeKind___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringAttributeKind___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToStringAttributeKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToStringAttributeKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToStringAttributeKind___closed__0 = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instToStringAttributeKind = (const lean_object*)&l_Lean_instToStringAttributeKind___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1;
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value)} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__4_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "Failed to register attribute: Attributes can only be registered during initialization"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__0 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__0_value;
static lean_once_cell_t l_Lean_registerBuiltinAttribute___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerBuiltinAttribute___closed__1;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Invalid builtin attribute declaration: `"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__2 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__2_value;
static const lean_string_object l_Lean_registerBuiltinAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` has already been used"};
static const lean_object* l_Lean_registerBuiltinAttribute___closed__3 = (const lean_object*)&l_Lean_registerBuiltinAttribute___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 14, 146, 125, 144, 1, 65, 64)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__2_value;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Unexpected attribute argument: This attribute takes no arguments"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__3_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__4;
static const lean_string_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__5 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___closed__6 = (const lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 202, 70, 6, 8, 133, 137, 74)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__1 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__1_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "export"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__2 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_1),((lean_object*)&l_Lean_Attribute_Builtin_ensureNoArgs___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value_aux_2),((lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(43, 70, 85, 26, 88, 142, 178, 115)}};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__3 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__3_value;
static const lean_string_object l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected attribute argument"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__4 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getIdent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected identifier, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getIdent___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getIdent___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getIdent___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getIdent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getAttrParamOptPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Unexpected attribute argument: Expected a priority, but found"};
static const lean_object* l_Lean_getAttrParamOptPrio___closed__0 = (const lean_object*)&l_Lean_getAttrParamOptPrio___closed__0_value;
static lean_once_cell_t l_Lean_getAttrParamOptPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAttrParamOptPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Attribute_Builtin_getPrio___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Unexpected attribute argument: Expected an optional priority, but found"};
static const lean_object* l_Lean_Attribute_Builtin_getPrio___closed__0 = (const lean_object*)&l_Lean_Attribute_Builtin_getPrio___closed__0_value;
static lean_once_cell_t l_Lean_Attribute_Builtin_getPrio___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Attribute_Builtin_getPrio___closed__1;
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "` must be public"};
static const lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureAttrDeclIsMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` must be marked as `meta`"};
static const lean_object* l_Lean_ensureAttrDeclIsMeta___closed__0 = (const lean_object*)&l_Lean_ensureAttrDeclIsMeta___closed__0_value;
static lean_once_cell_t l_Lean_ensureAttrDeclIsMeta___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureAttrDeclIsMeta___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedTagAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTagAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tag attribute"};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value;
static const lean_string_object l_Lean_registerTagAttribute___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__3_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_registerTagAttribute___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerTagAttribute___lam__2___closed__5 = (const lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerTagAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___closed__0_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__1 = (const lean_object*)&l_Lean_registerTagAttribute___closed__1_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___closed__2_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__3, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__3 = (const lean_object*)&l_Lean_registerTagAttribute___closed__3_value;
static const lean_closure_object l_Lean_registerTagAttribute___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerTagAttribute___closed__4 = (const lean_object*)&l_Lean_registerTagAttribute___closed__4_value;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__5;
static lean_once_cell_t l_Lean_registerTagAttribute___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___closed__6;
static const lean_ctor_object l_Lean_registerTagAttribute___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerTagAttribute___closed__1_value)}};
static const lean_object* l_Lean_registerTagAttribute___closed__7 = (const lean_object*)&l_Lean_registerTagAttribute___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__5;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parametric attribute"};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__0 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__1 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__2 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttributeExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__3 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttributeExt___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttributeExt___redArg___closed__5 = (const lean_object*)&l_Lean_registerParametricAttributeExt___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__3_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__11_value),((lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__9_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to add parametric attribute `["};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "]` to `"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`: Attribute has already been set"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2_value;
static const lean_string_object l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: Declaration is in an imported module"};
static const lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__4;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___auto__1;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "enumeration attribute extension"};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__0 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__1 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__2 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__2_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__3 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__4, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__4 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__5 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__6___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__6 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__6_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__7 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__7_value;
static const lean_ctor_object l_Lean_registerEnumAttributes___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__1_value)}};
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__8 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Internal error calling `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__0 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__0_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ".setValue` for `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__1 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__1_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = ": Declaration is not from this async context `"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__2 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__2_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__3 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__3_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__4 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__4_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__5 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__5_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ": Attribute has already been set"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__6 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__6_value;
static const lean_string_object l_Lean_EnumAttributes_setValue___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = ": Declaration is in an imported module"};
static const lean_object* l_Lean_EnumAttributes_setValue___redArg___closed__7 = (const lean_object*)&l_Lean_EnumAttributes_setValue___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeImplBuilderTableRef;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Attribute implementation builder `"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__0 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__0_value;
static const lean_string_object l_Lean_registerAttributeImplBuilder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_registerAttributeImplBuilder___closed__1 = (const lean_object*)&l_Lean_registerAttributeImplBuilder___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Unknown attribute implementation builder `"};
static const lean_object* l_Lean_mkAttributeImplOfEntry___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAttributeExtensionState_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeExtensionState;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object*);
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Unexpected attribute implementation type: `{.ofConstName declName}` is not of type `Lean.AttributeImpl`"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__0 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value;
static const lean_ctor_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__0_value)}};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__1 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__1_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__2 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__2_value;
static const lean_string_object l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "AttributeImpl"};
static const lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___closed__3 = (const lean_object*)&l_Lean_mkAttributeImplOfConstantUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "attributeExtension"};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 25, 250, 145, 208, 184, 170, 105)}};
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_addAttrEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeExtension;
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames();
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object*);
static const lean_string_object l_Lean_getBuiltinAttributeImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unknown attribute `"};
static const lean_object* l_Lean_getBuiltinAttributeImpl___closed__0 = (const lean_object*)&l_Lean_getBuiltinAttributeImpl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_num_attributes();
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_inc(v_afterTypeChecking_23_);
return v_afterTypeChecking_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_24_);
lean_dec(v_afterTypeChecking_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_afterTypeChecking_29_){
_start:
{
lean_inc(v_afterTypeChecking_29_);
return v_afterTypeChecking_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_afterTypeChecking_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_afterTypeChecking_33_);
lean_dec(v_afterTypeChecking_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_36_){
_start:
{
lean_inc(v_afterCompilation_36_);
return v_afterCompilation_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_37_);
lean_dec(v_afterCompilation_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_afterCompilation_42_){
_start:
{
lean_inc(v_afterCompilation_42_);
return v_afterCompilation_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_afterCompilation_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_afterCompilation_46_);
lean_dec(v_afterCompilation_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_49_){
_start:
{
lean_inc(v_beforeElaboration_49_);
return v_beforeElaboration_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_50_);
lean_dec(v_beforeElaboration_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_beforeElaboration_55_){
_start:
{
lean_inc(v_beforeElaboration_55_);
return v_beforeElaboration_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_beforeElaboration_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_beforeElaboration_59_);
lean_dec(v_beforeElaboration_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_17__boxed_71_; uint8_t v_y_18__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_17__boxed_71_ = lean_unbox(v_x_69_);
v_y_18__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_17__boxed_71_, v_y_18__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_options_84_; lean_object* v_ref_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v_options_84_ = lean_ctor_get(v___y_79_, 2);
v_ref_85_ = lean_ctor_get(v___y_79_, 5);
lean_inc_ref(v_options_84_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_env_83_);
lean_ctor_set(v___x_86_, 1, v_options_84_);
v___x_87_ = lean_apply_2(v_x_78_, v___x_86_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_107_; 
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_100_ = lean_io_error_to_string(v_a_96_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
lean_inc(v_ref_85_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_85_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_103_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_108_, v_x_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_145_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_158_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_161_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_168_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_172_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_175_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_176_ = lean_box(2);
v___x_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_179_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_182_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_186_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_189_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_207_){
_start:
{
switch(v_x_207_)
{
case 0:
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
case 1:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(1u);
return v___x_209_;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(2u);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_boxed_212_; lean_object* v_res_213_; 
v_x_boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_214_){
_start:
{
lean_inc(v_k_214_);
return v_k_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_215_);
lean_dec(v_k_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_inc(v_k_221_);
return v_k_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_222_, lean_object* v_ctorIdx_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_k_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_AttributeKind_ctorElim(v_motive_222_, v_ctorIdx_223_, v_t_boxed_227_, v_h_225_, v_k_226_);
lean_dec(v_k_226_);
lean_dec(v_ctorIdx_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_229_){
_start:
{
lean_inc(v_global_229_);
return v_global_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_AttributeKind_global_elim___redArg(v_global_230_);
lean_dec(v_global_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_global_235_){
_start:
{
lean_inc(v_global_235_);
return v_global_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_global_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_AttributeKind_global_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_global_239_);
lean_dec(v_global_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_242_){
_start:
{
lean_inc(v_local_242_);
return v_local_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_AttributeKind_local_elim___redArg(v_local_243_);
lean_dec(v_local_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_local_248_){
_start:
{
lean_inc(v_local_248_);
return v_local_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_local_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_AttributeKind_local_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_local_252_);
lean_dec(v_local_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_255_){
_start:
{
lean_inc(v_scoped_255_);
return v_scoped_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_256_);
lean_dec(v_scoped_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_scoped_261_){
_start:
{
lean_inc(v_scoped_261_);
return v_scoped_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_scoped_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_AttributeKind_scoped_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_scoped_265_);
lean_dec(v_scoped_265_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_268_, uint8_t v_y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_AttributeKind_ctorIdx(v_x_268_);
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_y_269_);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
uint8_t v_x_17__boxed_275_; uint8_t v_y_18__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_17__boxed_275_ = lean_unbox(v_x_273_);
v_y_18__boxed_276_ = lean_unbox(v_y_274_);
v_res_277_ = l_Lean_instBEqAttributeKind_beq(v_x_17__boxed_275_, v_y_18__boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_286_){
_start:
{
switch(v_x_286_)
{
case 0:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_288_;
}
default: 
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_x_36__boxed_291_; lean_object* v_res_292_; 
v_x_36__boxed_291_ = lean_unbox(v_x_290_);
v_res_292_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_291_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_instInhabitedMessageData_default;
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_298_, lean_object* v___y_299_, uint8_t v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_994__boxed_312_; lean_object* v_res_313_; 
v___y_994__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_994__boxed_312_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_307_);
lean_dec(v_x_306_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_317_);
lean_ctor_set(v___x_319_, 5, v___x_317_);
lean_ctor_set(v___x_319_, 6, v___x_317_);
lean_ctor_set(v___x_319_, 7, v___x_317_);
lean_ctor_set(v___x_319_, 8, v___x_317_);
lean_ctor_set(v___x_319_, 9, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(32u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unsigned_to_nat(32u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_324_);
lean_ctor_set(v___x_328_, 3, v___x_324_);
lean_ctor_set_usize(v___x_328_, 4, v___x_323_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_box(1);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_options_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_337_ = lean_st_ref_get(v___y_335_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_337_);
v_options_339_ = lean_ctor_get(v___y_334_, 2);
v___x_340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_339_);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v_env_338_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_341_);
lean_ctor_set(v___x_342_, 3, v_options_339_);
v___x_343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_msgData_333_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_ref_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_364_; 
v_ref_354_ = lean_ctor_get(v___y_351_, 5);
v___x_355_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_350_, v___y_351_, v___y_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_364_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_364_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_inc(v_ref_354_);
v___x_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_360_, 0, v_ref_354_);
lean_ctor_set(v___x_360_, 1, v_a_356_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 1);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_362_ = v___x_358_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_375_ = l_Lean_stringToMessageData(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_376_, lean_object* v_decl_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_name_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_name_381_ = lean_ctor_get(v___x_376_, 1);
lean_inc(v_name_381_);
lean_dec_ref(v___x_376_);
v___x_382_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_383_ = l_Lean_MessageData_ofName(v_name_381_);
v___x_384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_386_, v___y_378_, v___y_379_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_388_, lean_object* v_decl_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_388_, v_decl_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v_decl_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_408_, v_msg_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_unsigned_to_nat(16u);
v___x_417_ = lean_mk_array(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_423_ = lean_st_mk_ref(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
lean_object* v_key_430_; lean_object* v_tail_431_; uint8_t v___x_432_; 
v_key_430_ = lean_ctor_get(v_x_428_, 0);
v_tail_431_ = lean_ctor_get(v_x_428_, 2);
v___x_432_ = lean_name_eq(v_key_430_, v_a_427_);
if (v___x_432_ == 0)
{
v_x_428_ = v_tail_431_;
goto _start;
}
else
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec(v_a_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_438_; uint64_t v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(1723u);
v___x_439_ = lean_uint64_of_nat(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_buckets_442_; lean_object* v___x_443_; uint64_t v___y_445_; 
v_buckets_442_ = lean_ctor_get(v_m_440_, 1);
v___x_443_ = lean_array_get_size(v_buckets_442_);
if (lean_obj_tag(v_a_441_) == 0)
{
uint64_t v___x_459_; 
v___x_459_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_445_ = v___x_459_;
goto v___jp_444_;
}
else
{
uint64_t v_hash_460_; 
v_hash_460_ = lean_ctor_get_uint64(v_a_441_, sizeof(void*)*2);
v___y_445_ = v_hash_460_;
goto v___jp_444_;
}
v___jp_444_:
{
uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___y_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___y_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_443_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v___x_457_ = lean_array_uget_borrowed(v_buckets_442_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_441_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_m_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v_x_467_;
}
else
{
lean_object* v_key_468_; lean_object* v_value_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_key_468_ = lean_ctor_get(v_x_467_, 0);
v_value_469_ = lean_ctor_get(v_x_467_, 1);
v_tail_470_ = lean_ctor_get(v_x_467_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v_x_467_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_value_469_);
lean_inc(v_key_468_);
lean_dec(v_x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_name_eq(v_key_468_, v_a_465_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_465_, v_b_466_, v_tail_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_key_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_value_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_value_469_);
lean_dec(v_key_468_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_b_466_);
lean_ctor_set(v___x_472_, 0, v_a_465_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_b_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_tail_470_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
return v_x_483_;
}
else
{
lean_object* v_key_485_; lean_object* v_value_486_; lean_object* v_tail_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_513_; 
v_key_485_ = lean_ctor_get(v_x_484_, 0);
v_value_486_ = lean_ctor_get(v_x_484_, 1);
v_tail_487_ = lean_ctor_get(v_x_484_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_489_ = v_x_484_;
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_tail_487_);
lean_inc(v_value_486_);
lean_inc(v_key_485_);
lean_dec(v_x_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; uint64_t v___y_493_; 
v___x_491_ = lean_array_get_size(v_x_483_);
if (lean_obj_tag(v_key_485_) == 0)
{
uint64_t v___x_511_; 
v___x_511_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_493_ = v___x_511_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_512_; 
v_hash_512_ = lean_ctor_get_uint64(v_key_485_, sizeof(void*)*2);
v___y_493_ = v_hash_512_;
goto v___jp_492_;
}
v___jp_492_:
{
uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___y_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___y_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_491_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v___x_505_ = lean_array_uget_borrowed(v_x_483_, v___x_504_);
lean_inc(v___x_505_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 2, v___x_505_);
v___x_507_ = v___x_489_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_505_);
v___x_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_array_uset(v_x_483_, v___x_504_, v___x_507_);
v_x_483_ = v___x_508_;
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_514_, lean_object* v_source_515_, lean_object* v_target_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_source_515_);
v___x_518_ = lean_nat_dec_lt(v_i_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_source_515_);
lean_dec(v_i_514_);
return v_target_516_;
}
else
{
lean_object* v_es_519_; lean_object* v___x_520_; lean_object* v_source_521_; lean_object* v_target_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_es_519_ = lean_array_fget(v_source_515_, v_i_514_);
v___x_520_ = lean_box(0);
v_source_521_ = lean_array_fset(v_source_515_, v_i_514_, v___x_520_);
v_target_522_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_516_, v_es_519_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_514_, v___x_523_);
lean_dec(v_i_514_);
v_i_514_ = v___x_524_;
v_source_515_ = v_source_521_;
v_target_516_ = v_target_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_nbuckets_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_527_ = lean_array_get_size(v_data_526_);
v___x_528_ = lean_unsigned_to_nat(2u);
v_nbuckets_529_ = lean_nat_mul(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_box(0);
v___x_532_ = lean_mk_array(v_nbuckets_529_, v___x_531_);
v___x_533_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_530_, v_data_526_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_size_537_; lean_object* v_buckets_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_584_; 
v_size_537_ = lean_ctor_get(v_m_534_, 0);
v_buckets_538_ = lean_ctor_get(v_m_534_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_534_);
if (v_isSharedCheck_584_ == 0)
{
v___x_540_ = v_m_534_;
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_buckets_538_);
lean_inc(v_size_537_);
lean_dec(v_m_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint64_t v___y_544_; 
v___x_542_ = lean_array_get_size(v_buckets_538_);
if (lean_obj_tag(v_a_535_) == 0)
{
uint64_t v___x_582_; 
v___x_582_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_544_ = v___x_582_;
goto v___jp_543_;
}
else
{
uint64_t v_hash_583_; 
v_hash_583_ = lean_ctor_get_uint64(v_a_535_, sizeof(void*)*2);
v___y_544_ = v_hash_583_;
goto v___jp_543_;
}
v___jp_543_:
{
uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v_fold_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_bkt_556_; uint8_t v___x_557_; 
v___x_545_ = 32ULL;
v___x_546_ = lean_uint64_shift_right(v___y_544_, v___x_545_);
v_fold_547_ = lean_uint64_xor(v___y_544_, v___x_546_);
v___x_548_ = 16ULL;
v___x_549_ = lean_uint64_shift_right(v_fold_547_, v___x_548_);
v___x_550_ = lean_uint64_xor(v_fold_547_, v___x_549_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
v___x_552_ = lean_usize_of_nat(v___x_542_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_sub(v___x_552_, v___x_553_);
v___x_555_ = lean_usize_land(v___x_551_, v___x_554_);
v_bkt_556_ = lean_array_uget_borrowed(v_buckets_538_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_535_, v_bkt_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v_size_x27_559_; lean_object* v___x_560_; lean_object* v_buckets_x27_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v_size_x27_559_ = lean_nat_add(v_size_537_, v___x_558_);
lean_dec(v_size_537_);
lean_inc(v_bkt_556_);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v_a_535_);
lean_ctor_set(v___x_560_, 1, v_b_536_);
lean_ctor_set(v___x_560_, 2, v_bkt_556_);
v_buckets_x27_561_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(4u);
v___x_563_ = lean_nat_mul(v_size_x27_559_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_div(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_array_get_size(v_buckets_x27_561_);
v___x_567_ = lean_nat_dec_le(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v_val_568_; lean_object* v___x_570_; 
v_val_568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_561_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_val_568_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_570_ = v___x_540_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_val_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_buckets_x27_561_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_573_ = v___x_540_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_buckets_x27_561_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v___x_575_; lean_object* v_buckets_x27_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_inc(v_bkt_556_);
v___x_575_ = lean_box(0);
v_buckets_x27_576_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_575_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_535_, v_b_536_, v_bkt_556_);
v___x_578_ = lean_array_uset(v_buckets_x27_576_, v___x_555_, v___x_577_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_578_);
v___x_580_ = v___x_540_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_size_537_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_587_ = lean_mk_io_user_error(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_toAttributeImplCore_594_; lean_object* v_name_595_; uint8_t v___x_596_; 
v___x_592_ = l_Lean_attributeMapRef;
v___x_593_ = lean_st_ref_get(v___x_592_);
v_toAttributeImplCore_594_ = lean_ctor_get(v_attr_590_, 0);
v_name_595_ = lean_ctor_get(v_toAttributeImplCore_594_, 1);
lean_inc(v_name_595_);
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_593_, v_name_595_);
lean_dec(v___x_593_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
v___x_597_ = l_Lean_initializing();
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_name_595_);
lean_dec_ref(v_attr_590_);
v___x_598_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_st_ref_take(v___x_592_);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_600_, v_name_595_, v_attr_590_);
v___x_602_ = lean_st_ref_set(v___x_592_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_attr_590_);
v___x_604_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_595_, v___x_596_);
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_mk_io_user_error(v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_registerBuiltinAttribute(v_attr_611_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_618_, v_m_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_m_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_a_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_624_, v_a_625_, v_b_626_);
return v___x_627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_a_629_, lean_object* v_x_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_632_, v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_637_, lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_641_, v_b_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_645_, lean_object* v_i_646_, lean_object* v_source_647_, lean_object* v_target_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_646_, v_source_647_, v_target_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_fileName_659_; lean_object* v_fileMap_660_; lean_object* v_options_661_; lean_object* v_currRecDepth_662_; lean_object* v_maxRecDepth_663_; lean_object* v_ref_664_; lean_object* v_currNamespace_665_; lean_object* v_openDecls_666_; lean_object* v_initHeartbeats_667_; lean_object* v_maxHeartbeats_668_; lean_object* v_quotContext_669_; lean_object* v_currMacroScope_670_; uint8_t v_diag_671_; lean_object* v_cancelTk_x3f_672_; uint8_t v_suppressElabErrors_673_; lean_object* v_inheritedTraceOptions_674_; lean_object* v_ref_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_fileName_659_ = lean_ctor_get(v___y_656_, 0);
v_fileMap_660_ = lean_ctor_get(v___y_656_, 1);
v_options_661_ = lean_ctor_get(v___y_656_, 2);
v_currRecDepth_662_ = lean_ctor_get(v___y_656_, 3);
v_maxRecDepth_663_ = lean_ctor_get(v___y_656_, 4);
v_ref_664_ = lean_ctor_get(v___y_656_, 5);
v_currNamespace_665_ = lean_ctor_get(v___y_656_, 6);
v_openDecls_666_ = lean_ctor_get(v___y_656_, 7);
v_initHeartbeats_667_ = lean_ctor_get(v___y_656_, 8);
v_maxHeartbeats_668_ = lean_ctor_get(v___y_656_, 9);
v_quotContext_669_ = lean_ctor_get(v___y_656_, 10);
v_currMacroScope_670_ = lean_ctor_get(v___y_656_, 11);
v_diag_671_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*14);
v_cancelTk_x3f_672_ = lean_ctor_get(v___y_656_, 12);
v_suppressElabErrors_673_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_674_ = lean_ctor_get(v___y_656_, 13);
v_ref_675_ = l_Lean_replaceRef(v_ref_654_, v_ref_664_);
lean_inc_ref(v_inheritedTraceOptions_674_);
lean_inc(v_cancelTk_x3f_672_);
lean_inc(v_currMacroScope_670_);
lean_inc(v_quotContext_669_);
lean_inc(v_maxHeartbeats_668_);
lean_inc(v_initHeartbeats_667_);
lean_inc(v_openDecls_666_);
lean_inc(v_currNamespace_665_);
lean_inc(v_maxRecDepth_663_);
lean_inc(v_currRecDepth_662_);
lean_inc_ref(v_options_661_);
lean_inc_ref(v_fileMap_660_);
lean_inc_ref(v_fileName_659_);
v___x_676_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_676_, 0, v_fileName_659_);
lean_ctor_set(v___x_676_, 1, v_fileMap_660_);
lean_ctor_set(v___x_676_, 2, v_options_661_);
lean_ctor_set(v___x_676_, 3, v_currRecDepth_662_);
lean_ctor_set(v___x_676_, 4, v_maxRecDepth_663_);
lean_ctor_set(v___x_676_, 5, v_ref_675_);
lean_ctor_set(v___x_676_, 6, v_currNamespace_665_);
lean_ctor_set(v___x_676_, 7, v_openDecls_666_);
lean_ctor_set(v___x_676_, 8, v_initHeartbeats_667_);
lean_ctor_set(v___x_676_, 9, v_maxHeartbeats_668_);
lean_ctor_set(v___x_676_, 10, v_quotContext_669_);
lean_ctor_set(v___x_676_, 11, v_currMacroScope_670_);
lean_ctor_set(v___x_676_, 12, v_cancelTk_x3f_672_);
lean_ctor_set(v___x_676_, 13, v_inheritedTraceOptions_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14, v_diag_671_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14 + 1, v_suppressElabErrors_673_);
v___x_677_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_655_, v___x_676_, v___y_657_);
lean_dec_ref_known(v___x_676_, 14);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_678_, v_msg_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_ref_678_);
return v_res_683_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; uint8_t v___y_715_; lean_object* v___x_721_; uint8_t v___x_722_; 
lean_inc(v_stx_700_);
v___x_704_ = l_Lean_Syntax_getKind(v_stx_700_);
v___x_721_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_722_ = lean_name_eq(v___x_704_, v___x_721_);
if (v___x_722_ == 0)
{
v___y_715_ = v___x_722_;
goto v___jp_714_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = l_Lean_Syntax_getArg(v_stx_700_, v___x_723_);
v___x_725_ = l_Lean_Syntax_isNone(v___x_724_);
lean_dec(v___x_724_);
v___y_715_ = v___x_725_;
goto v___jp_714_;
}
v___jp_705_:
{
lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_707_ = lean_name_eq(v___x_704_, v___x_706_);
lean_dec(v___x_704_);
if (v___x_707_ == 0)
{
if (lean_obj_tag(v_stx_700_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_711_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_700_, v___x_710_, v_a_701_, v_a_702_);
lean_dec(v_stx_700_);
return v___x_711_;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_stx_700_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
goto v___jp_705_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(2u);
v___x_717_ = l_Lean_Syntax_getArg(v_stx_700_, v___x_716_);
v___x_718_ = l_Lean_Syntax_isNone(v___x_717_);
lean_dec(v___x_717_);
if (v___x_718_ == 0)
{
goto v___jp_705_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v___x_704_);
lean_dec(v_stx_700_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_731_, lean_object* v_ref_732_, lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_732_, v_msg_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_738_, lean_object* v_ref_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_738_, v_ref_739_, v_msg_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v_ref_739_);
return v_res_744_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
lean_inc(v_stx_760_);
v___x_772_ = l_Lean_Syntax_getKind(v_stx_760_);
v___x_773_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_774_ = lean_name_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_776_ = lean_name_eq(v___x_772_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_778_ = lean_name_eq(v___x_772_, v___x_777_);
lean_dec(v___x_772_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_780_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_760_, v___x_779_, v_a_761_, v_a_762_);
lean_dec(v_stx_760_);
return v___x_780_;
}
else
{
goto v___jp_764_;
}
}
else
{
lean_dec(v___x_772_);
goto v___jp_764_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
lean_dec(v___x_772_);
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = l_Lean_Syntax_getArg(v_stx_760_, v___x_781_);
lean_dec(v_stx_760_);
v___x_783_ = l_Lean_Syntax_isNone(v___x_782_);
if (v___x_783_ == 0)
{
if (v___x_774_ == 0)
{
lean_dec(v___x_782_);
goto v___jp_769_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lean_Syntax_getArg(v___x_782_, v___x_784_);
lean_dec(v___x_782_);
v___x_786_ = l_Lean_Syntax_isIdent(v___x_785_);
if (v___x_786_ == 0)
{
lean_dec(v___x_785_);
goto v___jp_769_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
else
{
lean_dec(v___x_782_);
goto v___jp_769_;
}
}
v___jp_764_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = l_Lean_Syntax_getArg(v_stx_760_, v___x_765_);
lean_dec(v_stx_760_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
v___jp_769_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_793_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_796_ = l_Lean_stringToMessageData(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_801_; 
lean_inc(v_stx_797_);
v___x_801_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_797_, v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_815_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_815_ == 0)
{
v___x_804_ = v___x_801_;
v_isShared_805_ = v_isSharedCheck_815_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_815_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
if (lean_obj_tag(v_a_802_) == 0)
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_del_object(v___x_804_);
v___x_806_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_797_);
v___x_807_ = l_Lean_MessageData_ofSyntax(v_stx_797_);
v___x_808_ = l_Lean_indentD(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_797_, v___x_809_, v_a_798_, v_a_799_);
lean_dec(v_stx_797_);
return v___x_810_;
}
else
{
lean_object* v_val_811_; lean_object* v___x_813_; 
lean_dec(v_stx_797_);
v_val_811_ = lean_ctor_get(v_a_802_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v_a_802_, 1);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_val_811_);
v___x_813_ = v___x_804_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_val_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_stx_797_);
v_a_816_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_801_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_801_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Attribute_Builtin_getIdent(v_stx_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_854_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_854_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_854_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_854_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_box(0);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_853_; 
v_val_842_ = lean_ctor_get(v_a_834_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_853_ == 0)
{
v___x_844_ = v_a_834_;
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v_a_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_Syntax_getId(v_val_842_);
lean_dec(v_val_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_852_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_848_);
v___x_850_ = v___x_836_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_833_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_833_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Attribute_Builtin_getIdent(v_stx_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = l_Lean_Syntax_getId(v_a_873_);
lean_dec(v_a_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_a_882_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_872_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_872_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Attribute_Builtin_getId(v_stx_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_894_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_Syntax_isNone(v_optPrioStx_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = l_Lean_Syntax_getArg(v_optPrioStx_898_, v___x_903_);
v___x_905_ = l_Lean_Syntax_isNatLit_x3f(v___x_904_);
lean_dec(v___x_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_906_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_898_);
v___x_907_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_898_);
v___x_908_ = l_Lean_indentD(v___x_907_);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_906_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_898_, v___x_909_, v_a_899_, v_a_900_);
lean_dec(v_optPrioStx_898_);
return v___x_910_;
}
else
{
lean_object* v_val_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_optPrioStx_898_);
v_val_911_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_905_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_val_911_);
lean_dec(v___x_905_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 0);
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_val_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_optPrioStx_898_);
v___x_919_ = lean_unsigned_to_nat(1000u);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
lean_inc(v_stx_929_);
v___x_933_ = l_Lean_Syntax_getKind(v_stx_929_);
v___x_934_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_935_ = lean_name_eq(v___x_933_, v___x_934_);
lean_dec(v___x_933_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_936_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_929_);
v___x_937_ = l_Lean_MessageData_ofSyntax(v_stx_929_);
v___x_938_ = l_Lean_indentD(v___x_937_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_936_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_929_, v___x_939_, v_a_930_, v_a_931_);
lean_dec(v_stx_929_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = l_Lean_Syntax_getArg(v_stx_929_, v___x_941_);
lean_dec(v_stx_929_);
v___x_943_ = l_Lean_getAttrParamOptPrio(v___x_942_, v_a_930_, v_a_931_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Attribute_Builtin_getPrio(v_stx_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_name_960_, uint8_t v_kind_961_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___y_968_; 
v___x_962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_963_ = l_Lean_MessageData_ofName(v_name_960_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
switch(v_kind_961_)
{
case 0:
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_968_ = v___x_975_;
goto v___jp_967_;
}
case 1:
{
lean_object* v___x_976_; 
v___x_976_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_968_ = v___x_976_;
goto v___jp_967_;
}
default: 
{
lean_object* v___x_977_; 
v___x_977_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_968_ = v___x_977_;
goto v___jp_967_;
}
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_inc_ref(v___y_968_);
v___x_969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_969_, 0, v___y_968_);
v___x_970_ = l_Lean_MessageData_ofFormat(v___x_969_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_966_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_throwError___redArg(v_inst_958_, v_inst_959_, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_name_980_, lean_object* v_kind_981_){
_start:
{
uint8_t v_kind_boxed_982_; lean_object* v_res_983_; 
v_kind_boxed_982_ = lean_unbox(v_kind_981_);
v_res_983_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_978_, v_inst_979_, v_name_980_, v_kind_boxed_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_00_u03b1_987_, lean_object* v_name_988_, uint8_t v_kind_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_985_, v_inst_986_, v_name_988_, v_kind_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_00_u03b1_994_, lean_object* v_name_995_, lean_object* v_kind_996_){
_start:
{
uint8_t v_kind_boxed_997_; lean_object* v_res_998_; 
v_kind_boxed_997_ = lean_unbox(v_kind_996_);
v_res_998_ = l_Lean_throwAttrMustBeGlobal(v_m_991_, v_inst_992_, v_inst_993_, v_00_u03b1_994_, v_name_995_, v_kind_boxed_997_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_attrName_1010_, lean_object* v_declName_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1012_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1013_ = l_Lean_MessageData_ofName(v_attrName_1010_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = 0;
v___x_1018_ = l_Lean_MessageData_ofConstName(v_declName_1011_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1016_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___redArg(v_inst_1008_, v_inst_1009_, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_00_u03b1_1026_, lean_object* v_attrName_1027_, lean_object* v_declName_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1024_, v_inst_1025_, v_attrName_1027_, v_declName_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_attrName_1038_, lean_object* v_declName_1039_, lean_object* v_asyncPrefix_x3f_1040_){
_start:
{
lean_object* v___y_1042_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1040_) == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_MessageData_nil;
v___y_1042_ = v___x_1055_;
goto v___jp_1041_;
}
else
{
lean_object* v_val_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_val_1056_ = lean_ctor_get(v_asyncPrefix_x3f_1040_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v_asyncPrefix_x3f_1040_, 1);
v___x_1057_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1058_ = l_Lean_MessageData_ofName(v_val_1056_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___y_1042_ = v___x_1061_;
goto v___jp_1041_;
}
v___jp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1043_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1044_ = l_Lean_MessageData_ofName(v_attrName_1038_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = 0;
v___x_1049_ = l_Lean_MessageData_ofConstName(v_declName_1039_, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___y_1042_);
v___x_1054_ = l_Lean_throwError___redArg(v_inst_1036_, v_inst_1037_, v___x_1053_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_00_u03b1_1065_, lean_object* v_attrName_1066_, lean_object* v_declName_1067_, lean_object* v_asyncPrefix_x3f_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1063_, v_inst_1064_, v_attrName_1066_, v_declName_1067_, v_asyncPrefix_x3f_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_attrName_1084_, lean_object* v_declName_1085_, lean_object* v_givenType_1086_, lean_object* v_expectedType_1087_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1088_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1089_ = l_Lean_MessageData_ofName(v_attrName_1084_);
lean_inc_ref(v___x_1089_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_MessageData_ofConstName(v_declName_1085_, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_indentExpr(v_givenType_1086_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1089_);
v___x_1103_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_indentExpr(v_expectedType_1087_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_throwError___redArg(v_inst_1082_, v_inst_1083_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_00_u03b1_1111_, lean_object* v_attrName_1112_, lean_object* v_declName_1113_, lean_object* v_givenType_1114_, lean_object* v_expectedType_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1109_, v_inst_1110_, v_attrName_1112_, v_declName_1113_, v_givenType_1114_, v_expectedType_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1117_, uint8_t v_skipRealize_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1121_ = lean_st_ref_get(v___y_1119_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Environment_contains(v_env_1122_, v_constName_1117_, v_skipRealize_1118_);
v___x_1124_ = lean_box(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1126_, lean_object* v_skipRealize_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v_skipRealize_boxed_1130_; lean_object* v_res_1131_; 
v_skipRealize_boxed_1130_ = lean_unbox(v_skipRealize_1127_);
v_res_1131_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1126_, v_skipRealize_boxed_1130_, v___y_1128_);
lean_dec(v___y_1128_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1132_, uint8_t v_skipRealize_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1132_, v_skipRealize_1133_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1138_, lean_object* v_skipRealize_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_skipRealize_boxed_1143_; lean_object* v_res_1144_; 
v_skipRealize_boxed_1143_ = lean_unbox(v_skipRealize_1139_);
v_res_1144_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1138_, v_skipRealize_boxed_1143_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1145_, uint8_t v_isExporting_1146_, lean_object* v___x_1147_, lean_object* v_a_x3f_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_env_1151_; lean_object* v_nextMacroScope_1152_; lean_object* v_ngen_1153_; lean_object* v_auxDeclNGen_1154_; lean_object* v_traceState_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1169_; 
v___x_1150_ = lean_st_ref_take(v___y_1145_);
v_env_1151_ = lean_ctor_get(v___x_1150_, 0);
v_nextMacroScope_1152_ = lean_ctor_get(v___x_1150_, 1);
v_ngen_1153_ = lean_ctor_get(v___x_1150_, 2);
v_auxDeclNGen_1154_ = lean_ctor_get(v___x_1150_, 3);
v_traceState_1155_ = lean_ctor_get(v___x_1150_, 4);
v_messages_1156_ = lean_ctor_get(v___x_1150_, 6);
v_infoState_1157_ = lean_ctor_get(v___x_1150_, 7);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1150_, 8);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1150_, 5);
lean_dec(v_unused_1170_);
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_traceState_1155_);
lean_inc(v_auxDeclNGen_1154_);
lean_inc(v_ngen_1153_);
lean_inc(v_nextMacroScope_1152_);
lean_inc(v_env_1151_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_Environment_setExporting(v_env_1151_, v_isExporting_1146_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 5, v___x_1147_);
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_nextMacroScope_1152_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_ngen_1153_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_auxDeclNGen_1154_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_traceState_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 5, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1168_, 6, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1168_, 7, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1168_, 8, v_snapshotTasks_1158_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_st_ref_set(v___y_1145_, v___x_1164_);
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1171_, lean_object* v_isExporting_1172_, lean_object* v___x_1173_, lean_object* v_a_x3f_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v_isExporting_boxed_1176_; lean_object* v_res_1177_; 
v_isExporting_boxed_1176_ = lean_unbox(v_isExporting_1172_);
v_res_1177_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1171_, v_isExporting_boxed_1176_, v___x_1173_, v_a_x3f_1174_);
lean_dec(v_a_x3f_1174_);
lean_dec(v___y_1171_);
return v_res_1177_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1183_, uint8_t v_isExporting_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; uint8_t v_isExporting_1190_; lean_object* v___x_1241_; uint8_t v_isModule_1242_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_env_1189_);
lean_dec(v___x_1188_);
v_isExporting_1190_ = lean_ctor_get_uint8(v_env_1189_, sizeof(void*)*8);
v___x_1241_ = l_Lean_Environment_header(v_env_1189_);
lean_dec_ref(v_env_1189_);
v_isModule_1242_ = lean_ctor_get_uint8(v___x_1241_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1241_);
if (v_isModule_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v___x_1243_ = lean_apply_3(v_x_1183_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1243_;
}
else
{
if (v_isExporting_1190_ == 0)
{
if (v_isExporting_1184_ == 0)
{
lean_object* v___x_1244_; 
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v___x_1244_ = lean_apply_3(v_x_1183_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1244_;
}
else
{
goto v___jp_1191_;
}
}
else
{
if (v_isExporting_1184_ == 0)
{
goto v___jp_1191_;
}
else
{
lean_object* v___x_1245_; 
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v___x_1245_ = lean_apply_3(v_x_1183_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1245_;
}
}
}
v___jp_1191_:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v_ngen_1195_; lean_object* v_auxDeclNGen_1196_; lean_object* v_traceState_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1239_; 
v___x_1192_ = lean_st_ref_take(v___y_1186_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1195_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1196_ = lean_ctor_get(v___x_1192_, 3);
v_traceState_1197_ = lean_ctor_get(v___x_1192_, 4);
v_messages_1198_ = lean_ctor_get(v___x_1192_, 6);
v_infoState_1199_ = lean_ctor_get(v___x_1192_, 7);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1192_, 8);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v___x_1192_, 5);
lean_dec(v_unused_1240_);
v___x_1202_ = v___x_1192_;
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_traceState_1197_);
lean_inc(v_auxDeclNGen_1196_);
lean_inc(v_ngen_1195_);
lean_inc(v_nextMacroScope_1194_);
lean_inc(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1204_ = l_Lean_Environment_setExporting(v_env_1193_, v_isExporting_1184_);
v___x_1205_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1205_);
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_nextMacroScope_1194_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_ngen_1195_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_auxDeclNGen_1196_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v_traceState_1197_);
lean_ctor_set(v_reuseFailAlloc_1238_, 5, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1238_, 6, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1238_, 7, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1238_, 8, v_snapshotTasks_1200_);
v___x_1207_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v_r_1209_; 
v___x_1208_ = lean_st_ref_set(v___y_1186_, v___x_1207_);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v_r_1209_ = lean_apply_3(v_x_1183_, v___y_1185_, v___y_1186_, lean_box(0));
if (lean_obj_tag(v_r_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1226_; 
v_a_1210_ = lean_ctor_get(v_r_1209_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_r_1209_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1212_ = v_r_1209_;
v_isShared_1213_ = v_isSharedCheck_1226_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v_r_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1226_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
lean_inc(v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set_tag(v___x_1212_, 1);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
v___x_1216_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1186_, v_isExporting_1190_, v___x_1205_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1224_);
v___x_1218_ = v___x_1216_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1216_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v_a_1210_);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1210_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1227_ = lean_ctor_get(v_r_1209_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v_r_1209_, 1);
v___x_1228_ = lean_box(0);
v___x_1229_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1186_, v_isExporting_1190_, v___x_1205_, v___x_1228_);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1229_, 0);
lean_dec(v_unused_1237_);
v___x_1231_ = v___x_1229_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_dec(v___x_1229_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 1);
lean_ctor_set(v___x_1231_, 0, v_a_1227_);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1227_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1246_, lean_object* v_isExporting_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v_isExporting_boxed_1251_; lean_object* v_res_1252_; 
v_isExporting_boxed_1251_ = lean_unbox(v_isExporting_1247_);
v_res_1252_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1246_, v_isExporting_boxed_1251_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1253_, lean_object* v_x_1254_, uint8_t v_isExporting_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1254_, v_isExporting_1255_, v___y_1256_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_x_1261_, lean_object* v_isExporting_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_isExporting_boxed_1266_; lean_object* v_res_1267_; 
v_isExporting_boxed_1266_ = lean_unbox(v_isExporting_1262_);
v_res_1267_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1260_, v_x_1261_, v_isExporting_boxed_1266_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1268_, lean_object* v_opt_1269_){
_start:
{
lean_object* v_name_1270_; lean_object* v_defValue_1271_; lean_object* v_map_1272_; lean_object* v___x_1273_; 
v_name_1270_ = lean_ctor_get(v_opt_1269_, 0);
v_defValue_1271_ = lean_ctor_get(v_opt_1269_, 1);
v_map_1272_ = lean_ctor_get(v_opts_1268_, 0);
v___x_1273_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1272_, v_name_1270_);
if (lean_obj_tag(v___x_1273_) == 0)
{
uint8_t v___x_1274_; 
v___x_1274_ = lean_unbox(v_defValue_1271_);
return v___x_1274_;
}
else
{
lean_object* v_val_1275_; 
v_val_1275_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_val_1275_);
lean_dec_ref_known(v___x_1273_, 1);
if (lean_obj_tag(v_val_1275_) == 1)
{
uint8_t v_v_1276_; 
v_v_1276_ = lean_ctor_get_uint8(v_val_1275_, 0);
lean_dec_ref_known(v_val_1275_, 0);
return v_v_1276_;
}
else
{
uint8_t v___x_1277_; 
lean_dec(v_val_1275_);
v___x_1277_ = lean_unbox(v_defValue_1271_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1278_, lean_object* v_opt_1279_){
_start:
{
uint8_t v_res_1280_; lean_object* v_r_1281_; 
v_res_1280_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1278_, v_opt_1279_);
lean_dec_ref(v_opt_1279_);
lean_dec_ref(v_opts_1278_);
v_r_1281_ = lean_box(v_res_1280_);
return v_r_1281_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1289_, uint8_t v_suppressElabErrors_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 1)
{
lean_object* v_pre_1292_; 
v_pre_1292_ = lean_ctor_get(v_x_1291_, 0);
switch(lean_obj_tag(v_pre_1292_))
{
case 1:
{
lean_object* v_pre_1293_; 
v_pre_1293_ = lean_ctor_get(v_pre_1292_, 0);
switch(lean_obj_tag(v_pre_1293_))
{
case 0:
{
lean_object* v_str_1294_; lean_object* v_str_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_str_1294_ = lean_ctor_get(v_x_1291_, 1);
v_str_1295_ = lean_ctor_get(v_pre_1292_, 1);
v___x_1296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1297_ = lean_string_dec_eq(v_str_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1299_ = lean_string_dec_eq(v_str_1295_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___y_1289_;
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1301_ = lean_string_dec_eq(v_str_1294_, v___x_1300_);
if (v___x_1301_ == 0)
{
return v___y_1289_;
}
else
{
return v_suppressElabErrors_1290_;
}
}
}
else
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1303_ = lean_string_dec_eq(v_str_1294_, v___x_1302_);
if (v___x_1303_ == 0)
{
return v___y_1289_;
}
else
{
return v_suppressElabErrors_1290_;
}
}
}
case 1:
{
lean_object* v_pre_1304_; 
v_pre_1304_ = lean_ctor_get(v_pre_1293_, 0);
if (lean_obj_tag(v_pre_1304_) == 0)
{
lean_object* v_str_1305_; lean_object* v_str_1306_; lean_object* v_str_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_str_1305_ = lean_ctor_get(v_x_1291_, 1);
v_str_1306_ = lean_ctor_get(v_pre_1292_, 1);
v_str_1307_ = lean_ctor_get(v_pre_1293_, 1);
v___x_1308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1309_ = lean_string_dec_eq(v_str_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___y_1289_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1311_ = lean_string_dec_eq(v_str_1306_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___y_1289_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1313_ = lean_string_dec_eq(v_str_1305_, v___x_1312_);
if (v___x_1313_ == 0)
{
return v___y_1289_;
}
else
{
return v_suppressElabErrors_1290_;
}
}
}
}
else
{
return v___y_1289_;
}
}
default: 
{
return v___y_1289_;
}
}
}
case 0:
{
lean_object* v_str_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_str_1314_ = lean_ctor_get(v_x_1291_, 1);
v___x_1315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1316_ = lean_string_dec_eq(v_str_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
return v___y_1289_;
}
else
{
return v_suppressElabErrors_1290_;
}
}
default: 
{
return v___y_1289_;
}
}
}
else
{
return v___y_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1317_, lean_object* v_suppressElabErrors_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v___y_4996__boxed_1320_; uint8_t v_suppressElabErrors_boxed_1321_; uint8_t v_res_1322_; lean_object* v_r_1323_; 
v___y_4996__boxed_1320_ = lean_unbox(v___y_1317_);
v_suppressElabErrors_boxed_1321_ = lean_unbox(v_suppressElabErrors_1318_);
v_res_1322_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4996__boxed_1320_, v_suppressElabErrors_boxed_1321_, v_x_1319_);
lean_dec(v_x_1319_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1324_, lean_object* v_msgData_1325_, uint8_t v_severity_1326_, uint8_t v_isSilent_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; uint8_t v___x_1415_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1425_; uint8_t v___x_1440_; 
v___x_1415_ = 2;
v___x_1440_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1326_, v___x_1415_);
if (v___x_1440_ == 0)
{
v___y_1425_ = v___x_1440_;
goto v___jp_1424_;
}
else
{
uint8_t v___x_1441_; 
lean_inc_ref(v_msgData_1325_);
v___x_1441_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1325_);
v___y_1425_ = v___x_1441_;
goto v___jp_1424_;
}
v___jp_1331_:
{
lean_object* v___x_1341_; lean_object* v_currNamespace_1342_; lean_object* v_openDecls_1343_; lean_object* v_env_1344_; lean_object* v_nextMacroScope_1345_; lean_object* v_ngen_1346_; lean_object* v_auxDeclNGen_1347_; lean_object* v_traceState_1348_; lean_object* v_cache_1349_; lean_object* v_messages_1350_; lean_object* v_infoState_1351_; lean_object* v_snapshotTasks_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1366_; 
v___x_1341_ = lean_st_ref_take(v___y_1340_);
v_currNamespace_1342_ = lean_ctor_get(v___y_1339_, 6);
v_openDecls_1343_ = lean_ctor_get(v___y_1339_, 7);
v_env_1344_ = lean_ctor_get(v___x_1341_, 0);
v_nextMacroScope_1345_ = lean_ctor_get(v___x_1341_, 1);
v_ngen_1346_ = lean_ctor_get(v___x_1341_, 2);
v_auxDeclNGen_1347_ = lean_ctor_get(v___x_1341_, 3);
v_traceState_1348_ = lean_ctor_get(v___x_1341_, 4);
v_cache_1349_ = lean_ctor_get(v___x_1341_, 5);
v_messages_1350_ = lean_ctor_get(v___x_1341_, 6);
v_infoState_1351_ = lean_ctor_get(v___x_1341_, 7);
v_snapshotTasks_1352_ = lean_ctor_get(v___x_1341_, 8);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1354_ = v___x_1341_;
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snapshotTasks_1352_);
lean_inc(v_infoState_1351_);
lean_inc(v_messages_1350_);
lean_inc(v_cache_1349_);
lean_inc(v_traceState_1348_);
lean_inc(v_auxDeclNGen_1347_);
lean_inc(v_ngen_1346_);
lean_inc(v_nextMacroScope_1345_);
lean_inc(v_env_1344_);
lean_dec(v___x_1341_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1366_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
lean_inc(v_openDecls_1343_);
lean_inc(v_currNamespace_1342_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_currNamespace_1342_);
lean_ctor_set(v___x_1356_, 1, v_openDecls_1343_);
v___x_1357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc_ref(v___y_1333_);
v___x_1358_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1358_, 0, v___y_1333_);
lean_ctor_set(v___x_1358_, 1, v___y_1334_);
lean_ctor_set(v___x_1358_, 2, v___y_1335_);
lean_ctor_set(v___x_1358_, 3, v___y_1336_);
lean_ctor_set(v___x_1358_, 4, v___x_1357_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*5, v___y_1338_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*5 + 1, v___y_1332_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*5 + 2, v_isSilent_1327_);
v___x_1359_ = l_Lean_MessageLog_add(v___x_1358_, v_messages_1350_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 6, v___x_1359_);
v___x_1361_ = v___x_1354_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_env_1344_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_nextMacroScope_1345_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_ngen_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_auxDeclNGen_1347_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_traceState_1348_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_cache_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 6, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 7, v_infoState_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 8, v_snapshotTasks_1352_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = lean_st_ref_set(v___y_1340_, v___x_1361_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
return v___x_1364_;
}
}
}
v___jp_1367_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1391_; 
v___x_1376_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1325_);
v___x_1377_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1376_, v___y_1328_, v___y_1329_);
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1391_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_inc_ref_n(v___y_1374_, 2);
v___x_1382_ = l_Lean_FileMap_toPosition(v___y_1374_, v___y_1373_);
lean_dec(v___y_1373_);
v___x_1383_ = l_Lean_FileMap_toPosition(v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1372_ == 0)
{
lean_del_object(v___x_1380_);
lean_dec_ref(v___y_1368_);
v___y_1332_ = v___y_1370_;
v___y_1333_ = v___y_1369_;
v___y_1334_ = v___x_1382_;
v___y_1335_ = v___x_1384_;
v___y_1336_ = v___x_1385_;
v___y_1337_ = v_a_1378_;
v___y_1338_ = v___y_1371_;
v___y_1339_ = v___y_1328_;
v___y_1340_ = v___y_1329_;
goto v___jp_1331_;
}
else
{
uint8_t v___x_1386_; 
lean_inc(v_a_1378_);
v___x_1386_ = l_Lean_MessageData_hasTag(v___y_1368_, v_a_1378_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec_ref_known(v___x_1384_, 1);
lean_dec_ref(v___x_1382_);
lean_dec(v_a_1378_);
v___x_1387_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1387_);
v___x_1389_ = v___x_1380_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_del_object(v___x_1380_);
v___y_1332_ = v___y_1370_;
v___y_1333_ = v___y_1369_;
v___y_1334_ = v___x_1382_;
v___y_1335_ = v___x_1384_;
v___y_1336_ = v___x_1385_;
v___y_1337_ = v_a_1378_;
v___y_1338_ = v___y_1371_;
v___y_1339_ = v___y_1328_;
v___y_1340_ = v___y_1329_;
goto v___jp_1331_;
}
}
}
}
v___jp_1392_:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Syntax_getTailPos_x3f(v___y_1396_, v___y_1397_);
lean_dec(v___y_1396_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_inc(v___y_1400_);
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1394_;
v___y_1371_ = v___y_1397_;
v___y_1372_ = v___y_1398_;
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___y_1399_;
v___y_1375_ = v___y_1400_;
goto v___jp_1367_;
}
else
{
lean_object* v_val_1402_; 
v_val_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1394_;
v___y_1371_ = v___y_1397_;
v___y_1372_ = v___y_1398_;
v___y_1373_ = v___y_1400_;
v___y_1374_ = v___y_1399_;
v___y_1375_ = v_val_1402_;
goto v___jp_1367_;
}
}
v___jp_1403_:
{
lean_object* v_ref_1411_; lean_object* v___x_1412_; 
v_ref_1411_ = l_Lean_replaceRef(v_ref_1324_, v___y_1406_);
v___x_1412_ = l_Lean_Syntax_getPos_x3f(v_ref_1411_, v___y_1407_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___y_1393_ = v___y_1404_;
v___y_1394_ = v___y_1410_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v_ref_1411_;
v___y_1397_ = v___y_1407_;
v___y_1398_ = v___y_1408_;
v___y_1399_ = v___y_1409_;
v___y_1400_ = v___x_1413_;
goto v___jp_1392_;
}
else
{
lean_object* v_val_1414_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v___x_1412_, 1);
v___y_1393_ = v___y_1404_;
v___y_1394_ = v___y_1410_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v_ref_1411_;
v___y_1397_ = v___y_1407_;
v___y_1398_ = v___y_1408_;
v___y_1399_ = v___y_1409_;
v___y_1400_ = v_val_1414_;
goto v___jp_1392_;
}
}
v___jp_1416_:
{
if (v___y_1423_ == 0)
{
v___y_1404_ = v___y_1420_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1422_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1421_;
v___y_1410_ = v_severity_1326_;
goto v___jp_1403_;
}
else
{
v___y_1404_ = v___y_1420_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1422_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1421_;
v___y_1410_ = v___x_1415_;
goto v___jp_1403_;
}
}
v___jp_1424_:
{
if (v___y_1425_ == 0)
{
lean_object* v_fileName_1426_; lean_object* v_fileMap_1427_; lean_object* v_options_1428_; lean_object* v_ref_1429_; uint8_t v_suppressElabErrors_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; uint8_t v___x_1434_; uint8_t v___x_1435_; 
v_fileName_1426_ = lean_ctor_get(v___y_1328_, 0);
v_fileMap_1427_ = lean_ctor_get(v___y_1328_, 1);
v_options_1428_ = lean_ctor_get(v___y_1328_, 2);
v_ref_1429_ = lean_ctor_get(v___y_1328_, 5);
v_suppressElabErrors_1430_ = lean_ctor_get_uint8(v___y_1328_, sizeof(void*)*14 + 1);
v___x_1431_ = lean_box(v___y_1425_);
v___x_1432_ = lean_box(v_suppressElabErrors_1430_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1433_, 0, v___x_1431_);
lean_closure_set(v___f_1433_, 1, v___x_1432_);
v___x_1434_ = 1;
v___x_1435_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1326_, v___x_1434_);
if (v___x_1435_ == 0)
{
v___y_1417_ = v_ref_1429_;
v___y_1418_ = v_fileName_1426_;
v___y_1419_ = v_suppressElabErrors_1430_;
v___y_1420_ = v___f_1433_;
v___y_1421_ = v_fileMap_1427_;
v___y_1422_ = v___y_1425_;
v___y_1423_ = v___x_1435_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = l_Lean_warningAsError;
v___x_1437_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1428_, v___x_1436_);
v___y_1417_ = v_ref_1429_;
v___y_1418_ = v_fileName_1426_;
v___y_1419_ = v_suppressElabErrors_1430_;
v___y_1420_ = v___f_1433_;
v___y_1421_ = v_fileMap_1427_;
v___y_1422_ = v___y_1425_;
v___y_1423_ = v___x_1437_;
goto v___jp_1416_;
}
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_msgData_1325_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1442_, lean_object* v_msgData_1443_, lean_object* v_severity_1444_, lean_object* v_isSilent_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_severity_boxed_1449_; uint8_t v_isSilent_boxed_1450_; lean_object* v_res_1451_; 
v_severity_boxed_1449_ = lean_unbox(v_severity_1444_);
v_isSilent_boxed_1450_ = lean_unbox(v_isSilent_1445_);
v_res_1451_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1442_, v_msgData_1443_, v_severity_boxed_1449_, v_isSilent_boxed_1450_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v_ref_1442_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1452_, uint8_t v_severity_1453_, uint8_t v_isSilent_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_ref_1458_; lean_object* v___x_1459_; 
v_ref_1458_ = lean_ctor_get(v___y_1455_, 5);
v___x_1459_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1458_, v_msgData_1452_, v_severity_1453_, v_isSilent_1454_, v___y_1455_, v___y_1456_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1460_, lean_object* v_severity_1461_, lean_object* v_isSilent_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_severity_boxed_1466_; uint8_t v_isSilent_boxed_1467_; lean_object* v_res_1468_; 
v_severity_boxed_1466_ = lean_unbox(v_severity_1461_);
v_isSilent_boxed_1467_ = lean_unbox(v_isSilent_1462_);
v_res_1468_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1460_, v_severity_boxed_1466_, v_isSilent_boxed_1467_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = 1;
v___x_1474_ = 0;
v___x_1475_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1469_, v___x_1473_, v___x_1474_, v___y_1470_, v___y_1471_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_options_1484_; uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_options_1484_ = lean_ctor_get(v___y_1482_, 2);
v___x_1485_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1484_, v_opt_1481_);
v___x_1486_ = lean_box(v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1488_, v___y_1489_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v_opt_1488_);
return v_res_1491_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v_env_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1525_; 
v___x_1502_ = lean_st_ref_get(v___y_1500_);
v_env_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1502_);
v___x_1504_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1505_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1504_, v___y_1499_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1525_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1525_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
uint8_t v_isExporting_1515_; 
v_isExporting_1515_ = lean_ctor_get_uint8(v_env_1503_, sizeof(void*)*8);
lean_dec_ref(v_env_1503_);
if (v_isExporting_1515_ == 0)
{
lean_dec(v_a_1506_);
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Lean_isPrivateName(v_id_1498_);
if (v___x_1516_ == 0)
{
lean_dec(v_a_1506_);
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = lean_unbox(v_a_1506_);
lean_dec(v_a_1506_);
if (v___x_1517_ == 0)
{
lean_dec(v_id_1498_);
goto v___jp_1510_;
}
else
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1508_);
v___x_1518_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1519_ = 0;
v___x_1520_ = l_Lean_MessageData_ofConstName(v_id_1498_, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1518_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1523_, v___y_1499_, v___y_1500_);
return v___x_1524_;
}
}
}
v___jp_1510_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1534_, uint8_t v_isModule_1535_, lean_object* v_attrName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; 
lean_inc(v_declName_1534_);
v___x_1540_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1534_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref_known(v___x_1540_, 1);
lean_inc(v_declName_1534_);
v___x_1541_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1534_, v_isModule_1535_, v___y_1538_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1562_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1562_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_unbox(v_a_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_del_object(v___x_1544_);
v___x_1547_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1548_ = l_Lean_MessageData_ofName(v_attrName_1536_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___x_1553_ = l_Lean_MessageData_ofConstName(v_declName_1534_, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1556_, v___y_1537_, v___y_1538_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
lean_dec(v_a_1542_);
lean_dec(v_attrName_1536_);
lean_dec(v_declName_1534_);
v___x_1558_ = lean_box(0);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1558_);
v___x_1560_ = v___x_1544_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_dec(v_attrName_1536_);
lean_dec(v_declName_1534_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1563_, lean_object* v_isModule_1564_, lean_object* v_attrName_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_isModule_boxed_1569_; lean_object* v_res_1570_; 
v_isModule_boxed_1569_ = lean_unbox(v_isModule_1564_);
v_res_1570_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1563_, v_isModule_boxed_1569_, v_attrName_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1571_, lean_object* v_declName_1572_, uint8_t v_attrKind_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v_env_1581_; lean_object* v___x_1582_; uint8_t v_isModule_1583_; 
v___x_1577_ = lean_st_ref_get(v_a_1575_);
v_env_1581_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_ref(v_env_1581_);
lean_dec(v___x_1577_);
v___x_1582_ = l_Lean_Environment_header(v_env_1581_);
lean_dec_ref(v_env_1581_);
v_isModule_1583_ = lean_ctor_get_uint8(v___x_1582_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1582_);
if (v_isModule_1583_ == 0)
{
lean_dec(v_declName_1572_);
lean_dec(v_attrName_1571_);
goto v___jp_1578_;
}
else
{
uint8_t v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = 1;
v___x_1585_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1573_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(v_isModule_1583_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1587_, 0, v_declName_1572_);
lean_closure_set(v___f_1587_, 1, v___x_1586_);
lean_closure_set(v___f_1587_, 2, v_attrName_1571_);
v___x_1588_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1587_, v_isModule_1583_, v_a_1574_, v_a_1575_);
return v___x_1588_;
}
else
{
lean_dec(v_declName_1572_);
lean_dec(v_attrName_1571_);
goto v___jp_1578_;
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
return v___x_1580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1589_, lean_object* v_declName_1590_, lean_object* v_attrKind_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
uint8_t v_attrKind_boxed_1595_; lean_object* v_res_1596_; 
v_attrKind_boxed_1595_ = lean_unbox(v_attrKind_1591_);
v_res_1596_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1589_, v_declName_1590_, v_attrKind_boxed_1595_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1597_, v___y_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_opt_1602_);
return v_res_1606_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1610_, lean_object* v_declName_1611_, uint8_t v_attrKind_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_env_1618_; lean_object* v___x_1619_; uint8_t v_isModule_1620_; 
v___x_1616_ = lean_st_ref_get(v_a_1614_);
v___x_1617_ = lean_st_ref_get(v_a_1614_);
v_env_1618_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_ref(v_env_1618_);
lean_dec(v___x_1616_);
v___x_1619_ = l_Lean_Environment_header(v_env_1618_);
lean_dec_ref(v_env_1618_);
v_isModule_1620_ = lean_ctor_get_uint8(v___x_1619_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1619_);
if (v_isModule_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v___x_1617_);
v___x_1621_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1610_, v_declName_1611_, v_attrKind_1612_, v_a_1613_, v_a_1614_);
return v___x_1621_;
}
else
{
lean_object* v_env_1622_; uint8_t v___x_1623_; 
v_env_1622_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_env_1622_);
lean_dec(v___x_1617_);
lean_inc(v_declName_1611_);
v___x_1623_ = l_Lean_isMarkedMeta(v_env_1622_, v_declName_1611_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1624_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1625_ = l_Lean_MessageData_ofName(v_attrName_1610_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = l_Lean_MessageData_ofConstName(v_declName_1611_, v___x_1623_);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1632_, v_a_1613_, v_a_1614_);
return v___x_1633_;
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1610_, v_declName_1611_, v_attrKind_1612_, v_a_1613_, v_a_1614_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1635_, lean_object* v_declName_1636_, lean_object* v_attrKind_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
uint8_t v_attrKind_boxed_1641_; lean_object* v_res_1642_; 
v_attrKind_boxed_1641_ = lean_unbox(v_attrKind_1637_);
v_res_1642_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1635_, v_declName_1636_, v_attrKind_boxed_1641_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1651_, v___y_1652_);
lean_dec_ref(v___y_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1655_, lean_object* v_x_1656_){
_start:
{
lean_inc(v_s_1655_);
return v_s_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec(v_s_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1667_, v_x_1668_);
lean_dec(v_x_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = lean_box(0);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1672_);
lean_dec(v_x_1672_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___f_1679_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1680_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1681_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1685_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1683_);
lean_ctor_set(v___x_1685_, 2, v___f_1682_);
lean_ctor_set(v___x_1685_, 3, v___f_1681_);
lean_ctor_set(v___x_1685_, 4, v___f_1680_);
lean_ctor_set(v___x_1685_, 5, v___f_1679_);
return v___x_1685_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1687_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1686_);
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_registerTagAttribute___lam__0(v_x_1694_);
lean_dec(v_x_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
return v_x_1697_;
}
else
{
lean_object* v_head_1699_; lean_object* v_tail_1700_; uint8_t v___x_1701_; 
v_head_1699_ = lean_ctor_get(v_x_1698_, 0);
lean_inc(v_head_1699_);
v_tail_1700_ = lean_ctor_get(v_x_1698_, 1);
lean_inc(v_tail_1700_);
lean_dec_ref_known(v_x_1698_, 2);
v___x_1701_ = l_Lean_NameSet_contains(v_newState_1696_, v_head_1699_);
if (v___x_1701_ == 0)
{
lean_dec(v_head_1699_);
v_x_1698_ = v_tail_1700_;
goto _start;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_NameSet_insert(v_x_1697_, v_head_1699_);
v_x_1697_ = v___x_1703_;
v_x_1698_ = v_tail_1700_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1705_, v_x_1706_, v_x_1707_);
lean_dec(v_newState_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1709_, lean_object* v_newState_1710_, lean_object* v_newConsts_1711_, lean_object* v_s_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1710_, v_s_1712_, v_newConsts_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1714_, lean_object* v_newState_1715_, lean_object* v_newConsts_1716_, lean_object* v_s_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_registerTagAttribute___lam__1(v_x_1714_, v_newState_1715_, v_newConsts_1716_, v_s_1717_);
lean_dec(v_newState_1715_);
lean_dec(v_x_1714_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1731_){
_start:
{
lean_object* v___x_1732_; lean_object* v___y_1734_; 
v___x_1732_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1731_) == 0)
{
lean_object* v_size_1738_; 
v_size_1738_ = lean_ctor_get(v_s_1731_, 0);
lean_inc(v_size_1738_);
lean_dec_ref_known(v_s_1731_, 5);
v___y_1734_ = v_size_1738_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___y_1734_ = v___x_1739_;
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = l_Nat_reprFast(v___y_1734_);
v___x_1736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1732_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
return v___x_1737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1740_, lean_object* v_pivot_1741_, lean_object* v_as_1742_, lean_object* v_i_1743_, lean_object* v_k_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_lt(v_k_1744_, v_hi_1740_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec(v_k_1744_);
v___x_1746_ = lean_array_fswap(v_as_1742_, v_i_1743_, v_hi_1740_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_i_1743_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1748_ = lean_array_fget_borrowed(v_as_1742_, v_k_1744_);
v___x_1749_ = l_Lean_Name_quickLt(v___x_1748_, v_pivot_1741_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_k_1744_, v___x_1750_);
lean_dec(v_k_1744_);
v_k_1744_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_array_fswap(v_as_1742_, v_i_1743_, v_k_1744_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_nat_add(v_i_1743_, v___x_1754_);
lean_dec(v_i_1743_);
v___x_1756_ = lean_nat_add(v_k_1744_, v___x_1754_);
lean_dec(v_k_1744_);
v_as_1742_ = v___x_1753_;
v_i_1743_ = v___x_1755_;
v_k_1744_ = v___x_1756_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1758_, lean_object* v_pivot_1759_, lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_k_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1758_, v_pivot_1759_, v_as_1760_, v_i_1761_, v_k_1762_);
lean_dec(v_pivot_1759_);
lean_dec(v_hi_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1764_, lean_object* v_as_1765_, lean_object* v_lo_1766_, lean_object* v_hi_1767_){
_start:
{
lean_object* v___y_1769_; uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_lt(v_lo_1766_, v_hi_1767_);
if (v___x_1779_ == 0)
{
lean_dec(v_lo_1766_);
return v_as_1765_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_mid_1782_; lean_object* v___y_1784_; lean_object* v___y_1790_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1780_ = lean_nat_add(v_lo_1766_, v_hi_1767_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v_mid_1782_ = lean_nat_shiftr(v___x_1780_, v___x_1781_);
lean_dec(v___x_1780_);
v___x_1795_ = lean_array_fget_borrowed(v_as_1765_, v_mid_1782_);
v___x_1796_ = lean_array_fget_borrowed(v_as_1765_, v_lo_1766_);
v___x_1797_ = l_Lean_Name_quickLt(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
v___y_1790_ = v_as_1765_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_array_fswap(v_as_1765_, v_lo_1766_, v_mid_1782_);
v___y_1790_ = v___x_1798_;
goto v___jp_1789_;
}
v___jp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = lean_array_fget_borrowed(v___y_1784_, v_mid_1782_);
v___x_1786_ = lean_array_fget_borrowed(v___y_1784_, v_hi_1767_);
v___x_1787_ = l_Lean_Name_quickLt(v___x_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec(v_mid_1782_);
v___y_1769_ = v___y_1784_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_array_fswap(v___y_1784_, v_mid_1782_, v_hi_1767_);
lean_dec(v_mid_1782_);
v___y_1769_ = v___x_1788_;
goto v___jp_1768_;
}
}
v___jp_1789_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = lean_array_fget_borrowed(v___y_1790_, v_hi_1767_);
v___x_1792_ = lean_array_fget_borrowed(v___y_1790_, v_lo_1766_);
v___x_1793_ = l_Lean_Name_quickLt(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
v___y_1784_ = v___y_1790_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_array_fswap(v___y_1790_, v_lo_1766_, v_hi_1767_);
v___y_1784_ = v___x_1794_;
goto v___jp_1783_;
}
}
}
v___jp_1768_:
{
lean_object* v_pivot_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; uint8_t v___x_1774_; 
v_pivot_1770_ = lean_array_fget(v___y_1769_, v_hi_1767_);
lean_inc_n(v_lo_1766_, 2);
v___x_1771_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1767_, v_pivot_1770_, v___y_1769_, v_lo_1766_, v_lo_1766_);
lean_dec(v_pivot_1770_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = lean_nat_dec_le(v_hi_1767_, v_fst_1772_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1764_, v_snd_1773_, v_lo_1766_, v_fst_1772_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_fst_1772_, v___x_1776_);
lean_dec(v_fst_1772_);
v_as_1765_ = v___x_1775_;
v_lo_1766_ = v___x_1777_;
goto _start;
}
else
{
lean_dec(v_fst_1772_);
lean_dec(v_lo_1766_);
return v_snd_1773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1799_, lean_object* v_as_1800_, lean_object* v_lo_1801_, lean_object* v_hi_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1799_, v_as_1800_, v_lo_1801_, v_hi_1802_);
lean_dec(v_hi_1802_);
lean_dec(v_n_1799_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1804_, lean_object* v_as_1805_, size_t v_i_1806_, size_t v_stop_1807_, lean_object* v_b_1808_){
_start:
{
lean_object* v___y_1810_; uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
v___x_1816_ = 1;
lean_inc_ref(v_env_1804_);
v___x_1817_ = l_Lean_Environment_setExporting(v_env_1804_, v___x_1816_);
lean_inc(v___x_1815_);
v___x_1818_ = l_Lean_Environment_contains(v___x_1817_, v___x_1815_, v___x_1814_);
if (v___x_1818_ == 0)
{
v___y_1810_ = v_b_1808_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1819_; 
lean_inc(v___x_1815_);
v___x_1819_ = lean_array_push(v_b_1808_, v___x_1815_);
v___y_1810_ = v___x_1819_;
goto v___jp_1809_;
}
}
else
{
lean_dec_ref(v_env_1804_);
return v_b_1808_;
}
v___jp_1809_:
{
size_t v___x_1811_; size_t v___x_1812_; 
v___x_1811_ = ((size_t)1ULL);
v___x_1812_ = lean_usize_add(v_i_1806_, v___x_1811_);
v_i_1806_ = v___x_1812_;
v_b_1808_ = v___y_1810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1820_, lean_object* v_as_1821_, lean_object* v_i_1822_, lean_object* v_stop_1823_, lean_object* v_b_1824_){
_start:
{
size_t v_i_boxed_1825_; size_t v_stop_boxed_1826_; lean_object* v_res_1827_; 
v_i_boxed_1825_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_stop_boxed_1826_ = lean_unbox_usize(v_stop_1823_);
lean_dec(v_stop_1823_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v_as_1821_, v_i_boxed_1825_, v_stop_boxed_1826_, v_b_1824_);
lean_dec_ref(v_as_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_object* v_k_1830_; lean_object* v_l_1831_; lean_object* v_r_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_k_1830_ = lean_ctor_get(v_x_1829_, 1);
lean_inc(v_k_1830_);
v_l_1831_ = lean_ctor_get(v_x_1829_, 3);
lean_inc(v_l_1831_);
v_r_1832_ = lean_ctor_get(v_x_1829_, 4);
lean_inc(v_r_1832_);
lean_dec_ref_known(v_x_1829_, 5);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1828_, v_l_1831_);
v___x_1834_ = lean_array_push(v___x_1833_, v_k_1830_);
v_init_1828_ = v___x_1834_;
v_x_1829_ = v_r_1832_;
goto _start;
}
else
{
return v_init_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1836_, lean_object* v_es_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; uint8_t v___x_1861_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1839_, v_es_1837_);
v___x_1856_ = lean_array_get_size(v___x_1855_);
v___x_1861_ = lean_nat_dec_eq(v___x_1856_, v___x_1838_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___y_1865_; uint8_t v___x_1867_; 
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_sub(v___x_1856_, v___x_1862_);
v___x_1867_ = lean_nat_dec_le(v___x_1838_, v___x_1863_);
if (v___x_1867_ == 0)
{
lean_inc(v___x_1863_);
v___y_1865_ = v___x_1863_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v___x_1838_;
goto v___jp_1864_;
}
v___jp_1864_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_le(v___y_1865_, v___x_1863_);
if (v___x_1866_ == 0)
{
lean_dec(v___x_1863_);
lean_inc(v___y_1865_);
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___y_1865_;
goto v___jp_1857_;
}
else
{
v___y_1858_ = v___y_1865_;
v___y_1859_ = v___x_1863_;
goto v___jp_1857_;
}
}
}
else
{
v___y_1841_ = v___x_1855_;
goto v___jp_1840_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_array_get_size(v___y_1841_);
v___x_1843_ = lean_nat_dec_lt(v___x_1838_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v_env_1836_);
v___x_1844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1839_);
lean_ctor_set(v___x_1844_, 2, v___y_1841_);
return v___x_1844_;
}
else
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_le(v___x_1842_, v___x_1842_);
if (v___x_1845_ == 0)
{
if (v___x_1843_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v_env_1836_);
v___x_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1839_);
lean_ctor_set(v___x_1846_, 1, v___x_1839_);
lean_ctor_set(v___x_1846_, 2, v___y_1841_);
return v___x_1846_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1842_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1836_, v___y_1841_, v___x_1847_, v___x_1848_, v___x_1839_);
lean_inc_ref(v___x_1849_);
v___x_1850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
lean_ctor_set(v___x_1850_, 2, v___y_1841_);
return v___x_1850_;
}
}
else
{
size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = lean_usize_of_nat(v___x_1842_);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1836_, v___y_1841_, v___x_1851_, v___x_1852_, v___x_1839_);
lean_inc_ref(v___x_1853_);
v___x_1854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
lean_ctor_set(v___x_1854_, 2, v___y_1841_);
return v___x_1854_;
}
}
}
v___jp_1857_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1856_, v___x_1855_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
v___y_1841_ = v___x_1860_;
goto v___jp_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1868_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_registerTagAttribute___lam__4(v___x_1873_, v_x_1874_, v_x_1875_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_registerTagAttribute___lam__5(v___x_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1884_, lean_object* v_decl_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1889_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1890_ = l_Lean_MessageData_ofName(v_name_1884_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1893_, v___y_1886_, v___y_1887_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1895_, lean_object* v_decl_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_registerTagAttribute___lam__6(v_name_1895_, v_decl_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v_decl_1896_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1901_, lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1906_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1907_ = l_Lean_MessageData_ofName(v_attrName_1901_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = 0;
v___x_1912_ = l_Lean_MessageData_ofConstName(v_declName_1902_, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1910_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1915_, v___y_1903_, v___y_1904_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1917_, lean_object* v_declName_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1917_, v_declName_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1923_, lean_object* v_declName_1924_, lean_object* v_asyncPrefix_x3f_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___y_1930_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1925_) == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_MessageData_nil;
v___y_1930_ = v___x_1943_;
goto v___jp_1929_;
}
else
{
lean_object* v_val_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v_val_1944_ = lean_ctor_get(v_asyncPrefix_x3f_1925_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_asyncPrefix_x3f_1925_, 1);
v___x_1945_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1946_ = l_Lean_MessageData_ofName(v_val_1944_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___y_1930_ = v___x_1949_;
goto v___jp_1929_;
}
v___jp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1932_ = l_Lean_MessageData_ofName(v_attrName_1923_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = 0;
v___x_1937_ = l_Lean_MessageData_ofConstName(v_declName_1924_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___y_1930_);
v___x_1942_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1941_, v___y_1926_, v___y_1927_);
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1950_, lean_object* v_declName_1951_, lean_object* v_asyncPrefix_x3f_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1950_, v_declName_1951_, v_asyncPrefix_x3f_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1957_, uint8_t v_kind_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___y_1968_; 
v___x_1962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1963_ = l_Lean_MessageData_ofName(v_name_1957_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
switch(v_kind_1958_)
{
case 0:
{
lean_object* v___x_1975_; 
v___x_1975_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1968_ = v___x_1975_;
goto v___jp_1967_;
}
case 1:
{
lean_object* v___x_1976_; 
v___x_1976_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1968_ = v___x_1976_;
goto v___jp_1967_;
}
default: 
{
lean_object* v___x_1977_; 
v___x_1977_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1968_ = v___x_1977_;
goto v___jp_1967_;
}
}
v___jp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_inc_ref(v___y_1968_);
v___x_1969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___y_1968_);
v___x_1970_ = l_Lean_MessageData_ofFormat(v___x_1969_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1966_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1973_, v___y_1959_, v___y_1960_);
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1978_, lean_object* v_kind_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
uint8_t v_kind_boxed_1983_; lean_object* v_res_1984_; 
v_kind_boxed_1983_ = lean_unbox(v_kind_1979_);
v_res_1984_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1978_, v_kind_boxed_1983_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1985_, lean_object* v_a_1986_, lean_object* v_name_1987_, lean_object* v_decl_1988_, lean_object* v_stx_1989_, uint8_t v_kind_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1989_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2045_) == 0)
{
uint8_t v___x_2046_; uint8_t v___x_2047_; 
lean_dec_ref_known(v___x_2045_, 1);
v___x_2046_ = 0;
v___x_2047_ = l_Lean_instBEqAttributeKind_beq(v_kind_1990_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
lean_dec(v_decl_1988_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2048_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1987_, v_kind_1990_, v___y_1991_, v___y_1992_);
return v___x_2048_;
}
else
{
v___y_2039_ = v___y_1991_;
v___y_2040_ = v___y_1992_;
goto v___jp_2038_;
}
}
else
{
lean_dec(v_decl_1988_);
lean_dec(v_name_1987_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
return v___x_2045_;
}
v___jp_1994_:
{
lean_object* v___x_1997_; 
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v_decl_1988_);
v___x_1997_ = lean_apply_4(v_validate_1985_, v_decl_1988_, v___y_1995_, v___y_1996_, lean_box(0));
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2027_; 
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2028_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2027_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; lean_object* v_toEnvExtension_2002_; lean_object* v_env_2003_; lean_object* v_nextMacroScope_2004_; lean_object* v_ngen_2005_; lean_object* v_auxDeclNGen_2006_; lean_object* v_traceState_2007_; lean_object* v_messages_2008_; lean_object* v_infoState_2009_; lean_object* v_snapshotTasks_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2025_; 
v___x_2001_ = lean_st_ref_take(v___y_1996_);
v_toEnvExtension_2002_ = lean_ctor_get(v_a_1986_, 0);
v_env_2003_ = lean_ctor_get(v___x_2001_, 0);
v_nextMacroScope_2004_ = lean_ctor_get(v___x_2001_, 1);
v_ngen_2005_ = lean_ctor_get(v___x_2001_, 2);
v_auxDeclNGen_2006_ = lean_ctor_get(v___x_2001_, 3);
v_traceState_2007_ = lean_ctor_get(v___x_2001_, 4);
v_messages_2008_ = lean_ctor_get(v___x_2001_, 6);
v_infoState_2009_ = lean_ctor_get(v___x_2001_, 7);
v_snapshotTasks_2010_ = lean_ctor_get(v___x_2001_, 8);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2001_, 5);
lean_dec(v_unused_2026_);
v___x_2012_ = v___x_2001_;
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snapshotTasks_2010_);
lean_inc(v_infoState_2009_);
lean_inc(v_messages_2008_);
lean_inc(v_traceState_2007_);
lean_inc(v_auxDeclNGen_2006_);
lean_inc(v_ngen_2005_);
lean_inc(v_nextMacroScope_2004_);
lean_inc(v_env_2003_);
lean_dec(v___x_2001_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2025_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_asyncMode_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v_asyncMode_2014_ = lean_ctor_get(v_toEnvExtension_2002_, 2);
lean_inc(v_asyncMode_2014_);
lean_inc(v_decl_1988_);
v___x_2015_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1986_, v_env_2003_, v_decl_1988_, v_asyncMode_2014_, v_decl_1988_);
lean_dec(v_asyncMode_2014_);
v___x_2016_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 5, v___x_2016_);
lean_ctor_set(v___x_2012_, 0, v___x_2015_);
v___x_2018_ = v___x_2012_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_nextMacroScope_2004_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_ngen_2005_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v_auxDeclNGen_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 4, v_traceState_2007_);
lean_ctor_set(v_reuseFailAlloc_2024_, 5, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2024_, 6, v_messages_2008_);
lean_ctor_set(v_reuseFailAlloc_2024_, 7, v_infoState_2009_);
lean_ctor_set(v_reuseFailAlloc_2024_, 8, v_snapshotTasks_2010_);
v___x_2018_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = lean_st_ref_set(v___y_1996_, v___x_2018_);
v___x_2020_ = lean_box(0);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2020_);
v___x_2022_ = v___x_1999_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_dec(v_decl_1988_);
lean_dec_ref(v_a_1986_);
return v___x_1997_;
}
}
v___jp_2029_:
{
lean_object* v_toEnvExtension_2033_; lean_object* v_asyncMode_2034_; uint8_t v___x_2035_; 
v_toEnvExtension_2033_ = lean_ctor_get(v_a_1986_, 0);
v_asyncMode_2034_ = lean_ctor_get(v_toEnvExtension_2033_, 2);
lean_inc(v_decl_1988_);
lean_inc_ref(v___y_2030_);
v___x_2035_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2030_, v_decl_1988_, v_asyncMode_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2036_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2030_);
v___x_2037_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1987_, v_decl_1988_, v___x_2036_, v___y_2031_, v___y_2032_);
return v___x_2037_;
}
else
{
lean_dec_ref(v___y_2030_);
lean_dec(v_name_1987_);
v___y_1995_ = v___y_2031_;
v___y_1996_ = v___y_2032_;
goto v___jp_1994_;
}
}
v___jp_2038_:
{
lean_object* v___x_2041_; lean_object* v_env_2042_; lean_object* v___x_2043_; 
v___x_2041_ = lean_st_ref_get(v___y_2040_);
v_env_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2041_);
v___x_2043_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2042_, v_decl_1988_);
if (lean_obj_tag(v___x_2043_) == 0)
{
v___y_2030_ = v_env_2042_;
v___y_2031_ = v___y_2039_;
v___y_2032_ = v___y_2040_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2044_; 
lean_dec_ref_known(v___x_2043_, 1);
lean_dec_ref(v_env_2042_);
lean_dec_ref(v_a_1986_);
lean_dec_ref(v_validate_1985_);
v___x_2044_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1987_, v_decl_1988_, v___y_2039_, v___y_2040_);
return v___x_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2049_, lean_object* v_a_2050_, lean_object* v_name_2051_, lean_object* v_decl_2052_, lean_object* v_stx_2053_, lean_object* v_kind_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
uint8_t v_kind_boxed_2058_; lean_object* v_res_2059_; 
v_kind_boxed_2058_ = lean_unbox(v_kind_2054_);
v_res_2059_ = l_Lean_registerTagAttribute___lam__7(v_validate_2049_, v_a_2050_, v_name_2051_, v_decl_2052_, v_stx_2053_, v_kind_boxed_2058_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2059_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___f_2066_; 
v___x_2065_ = l_Lean_NameSet_empty;
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2066_, 0, v___x_2065_);
return v___f_2066_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___f_2068_; 
v___x_2067_ = l_Lean_NameSet_empty;
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2068_, 0, v___x_2067_);
return v___f_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2071_, lean_object* v_descr_2072_, lean_object* v_validate_2073_, lean_object* v_ref_2074_, uint8_t v_applicationTime_2075_, lean_object* v_asyncMode_2076_){
_start:
{
lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___f_2078_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2079_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2080_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2081_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2082_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2083_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2084_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2074_);
v___x_2085_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2085_, 0, v_ref_2074_);
lean_ctor_set(v___x_2085_, 1, v___f_2083_);
lean_ctor_set(v___x_2085_, 2, v___f_2082_);
lean_ctor_set(v___x_2085_, 3, v___f_2081_);
lean_ctor_set(v___x_2085_, 4, v___f_2080_);
lean_ctor_set(v___x_2085_, 5, v___f_2079_);
lean_ctor_set(v___x_2085_, 6, v_asyncMode_2076_);
lean_ctor_set(v___x_2085_, 7, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___f_2078_);
v___x_2087_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc_n(v_a_2088_, 2);
lean_dec_ref_known(v___x_2087_, 1);
lean_inc_n(v_name_2071_, 2);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2089_, 0, v_name_2071_);
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2090_, 0, v_validate_2073_);
lean_closure_set(v___f_2090_, 1, v_a_2088_);
lean_closure_set(v___f_2090_, 2, v_name_2071_);
v___x_2091_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2091_, 0, v_ref_2074_);
lean_ctor_set(v___x_2091_, 1, v_name_2071_);
lean_ctor_set(v___x_2091_, 2, v_descr_2072_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*3, v_applicationTime_2075_);
v___x_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___f_2090_);
lean_ctor_set(v___x_2092_, 2, v___f_2089_);
lean_inc_ref(v___x_2092_);
v___x_2093_ = l_Lean_registerBuiltinAttribute(v___x_2092_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2101_; 
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v___x_2093_, 0);
lean_dec(v_unused_2102_);
v___x_2095_ = v___x_2093_;
v_isShared_2096_ = v_isSharedCheck_2101_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v___x_2093_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2101_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2092_);
lean_ctor_set(v___x_2097_, 1, v_a_2088_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2097_);
v___x_2099_ = v___x_2095_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref_known(v___x_2092_, 3);
lean_dec(v_a_2088_);
v_a_2103_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2093_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2093_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_ref_2074_);
lean_dec_ref(v_validate_2073_);
lean_dec_ref(v_descr_2072_);
lean_dec(v_name_2071_);
v_a_2111_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2087_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2087_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2119_, lean_object* v_descr_2120_, lean_object* v_validate_2121_, lean_object* v_ref_2122_, lean_object* v_applicationTime_2123_, lean_object* v_asyncMode_2124_, lean_object* v_a_2125_){
_start:
{
uint8_t v_applicationTime_boxed_2126_; lean_object* v_res_2127_; 
v_applicationTime_boxed_2126_ = lean_unbox(v_applicationTime_2123_);
v_res_2127_ = l_Lean_registerTagAttribute(v_name_2119_, v_descr_2120_, v_validate_2121_, v_ref_2122_, v_applicationTime_boxed_2126_, v_asyncMode_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2128_, lean_object* v_t_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2128_, v_t_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2131_, lean_object* v_as_2132_, lean_object* v_lo_2133_, lean_object* v_hi_2134_, lean_object* v_w_2135_, lean_object* v_hlo_2136_, lean_object* v_hhi_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2131_, v_as_2132_, v_lo_2133_, v_hi_2134_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2139_, lean_object* v_as_2140_, lean_object* v_lo_2141_, lean_object* v_hi_2142_, lean_object* v_w_2143_, lean_object* v_hlo_2144_, lean_object* v_hhi_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2139_, v_as_2140_, v_lo_2141_, v_hi_2142_, v_w_2143_, v_hlo_2144_, v_hhi_2145_);
lean_dec(v_hi_2142_);
lean_dec(v_n_2139_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2147_, lean_object* v_attrName_2148_, lean_object* v_declName_2149_, lean_object* v_asyncPrefix_x3f_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2148_, v_declName_2149_, v_asyncPrefix_x3f_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_attrName_2156_, lean_object* v_declName_2157_, lean_object* v_asyncPrefix_x3f_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2155_, v_attrName_2156_, v_declName_2157_, v_asyncPrefix_x3f_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2163_, lean_object* v_attrName_2164_, lean_object* v_declName_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2164_, v_declName_2165_, v___y_2166_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_attrName_2171_, lean_object* v_declName_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2170_, v_attrName_2171_, v_declName_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2177_, lean_object* v_name_2178_, uint8_t v_kind_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2178_, v_kind_2179_, v___y_2180_, v___y_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2184_, lean_object* v_name_2185_, lean_object* v_kind_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v_kind_boxed_2190_; lean_object* v_res_2191_; 
v_kind_boxed_2190_ = lean_unbox(v_kind_2186_);
v_res_2191_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2184_, v_name_2185_, v_kind_boxed_2190_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2192_, lean_object* v_lo_2193_, lean_object* v_hi_2194_, lean_object* v_hhi_2195_, lean_object* v_pivot_2196_, lean_object* v_as_2197_, lean_object* v_i_2198_, lean_object* v_k_2199_, lean_object* v_ilo_2200_, lean_object* v_ik_2201_, lean_object* v_w_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2194_, v_pivot_2196_, v_as_2197_, v_i_2198_, v_k_2199_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2204_, lean_object* v_lo_2205_, lean_object* v_hi_2206_, lean_object* v_hhi_2207_, lean_object* v_pivot_2208_, lean_object* v_as_2209_, lean_object* v_i_2210_, lean_object* v_k_2211_, lean_object* v_ilo_2212_, lean_object* v_ik_2213_, lean_object* v_w_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2204_, v_lo_2205_, v_hi_2206_, v_hhi_2207_, v_pivot_2208_, v_as_2209_, v_i_2210_, v_k_2211_, v_ilo_2212_, v_ik_2213_, v_w_2214_);
lean_dec(v_pivot_2208_);
lean_dec(v_hi_2206_);
lean_dec(v_lo_2205_);
lean_dec(v_n_2204_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2216_, lean_object* v_decl_2217_, lean_object* v_env_2218_){
_start:
{
lean_object* v_ext_2219_; lean_object* v_toEnvExtension_2220_; lean_object* v_asyncMode_2221_; lean_object* v___x_2222_; 
v_ext_2219_ = lean_ctor_get(v_attr_2216_, 1);
lean_inc_ref(v_ext_2219_);
lean_dec_ref(v_attr_2216_);
v_toEnvExtension_2220_ = lean_ctor_get(v_ext_2219_, 0);
v_asyncMode_2221_ = lean_ctor_get(v_toEnvExtension_2220_, 2);
lean_inc(v_asyncMode_2221_);
lean_inc(v_decl_2217_);
v___x_2222_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2219_, v_env_2218_, v_decl_2217_, v_asyncMode_2221_, v_decl_2217_);
lean_dec(v_asyncMode_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2223_, lean_object* v___f_2224_, lean_object* v_____r_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_apply_1(v_modifyEnv_2223_, v___f_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2227_, lean_object* v_env_2228_, lean_object* v_decl_2229_, lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v_toBind_2232_, lean_object* v___f_2233_, lean_object* v_modifyEnv_2234_, lean_object* v___f_2235_, lean_object* v_____r_2236_){
_start:
{
lean_object* v_ext_2237_; lean_object* v_toEnvExtension_2238_; lean_object* v_attr_2239_; lean_object* v_asyncMode_2240_; uint8_t v___x_2241_; 
v_ext_2237_ = lean_ctor_get(v_attr_2227_, 1);
v_toEnvExtension_2238_ = lean_ctor_get(v_ext_2237_, 0);
lean_inc_ref(v_toEnvExtension_2238_);
v_attr_2239_ = lean_ctor_get(v_attr_2227_, 0);
lean_inc_ref(v_attr_2239_);
lean_dec_ref(v_attr_2227_);
v_asyncMode_2240_ = lean_ctor_get(v_toEnvExtension_2238_, 2);
lean_inc(v_asyncMode_2240_);
lean_dec_ref(v_toEnvExtension_2238_);
lean_inc(v_decl_2229_);
lean_inc_ref(v_env_2228_);
v___x_2241_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2228_, v_decl_2229_, v_asyncMode_2240_);
lean_dec(v_asyncMode_2240_);
if (v___x_2241_ == 0)
{
lean_object* v_toAttributeImplCore_2242_; lean_object* v_name_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v___f_2235_);
lean_dec(v_modifyEnv_2234_);
v_toAttributeImplCore_2242_ = lean_ctor_get(v_attr_2239_, 0);
lean_inc_ref(v_toAttributeImplCore_2242_);
lean_dec_ref(v_attr_2239_);
v_name_2243_ = lean_ctor_get(v_toAttributeImplCore_2242_, 1);
lean_inc(v_name_2243_);
lean_dec_ref(v_toAttributeImplCore_2242_);
v___x_2244_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2228_);
v___x_2245_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2230_, v_inst_2231_, v_name_2243_, v_decl_2229_, v___x_2244_);
v___x_2246_ = lean_apply_4(v_toBind_2232_, lean_box(0), lean_box(0), v___x_2245_, v___f_2233_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; 
lean_dec_ref(v_attr_2239_);
lean_dec(v___f_2233_);
lean_dec(v_toBind_2232_);
lean_dec_ref(v_inst_2231_);
lean_dec_ref(v_inst_2230_);
lean_dec(v_decl_2229_);
lean_dec_ref(v_env_2228_);
v___x_2247_ = lean_apply_1(v_modifyEnv_2234_, v___f_2235_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2248_, lean_object* v_____r_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_apply_1(v___f_2248_, v_____r_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2251_, lean_object* v_decl_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_toBind_2255_, lean_object* v___f_2256_, lean_object* v_modifyEnv_2257_, lean_object* v___f_2258_, lean_object* v_env_2259_){
_start:
{
lean_object* v___f_2260_; lean_object* v___x_2261_; 
lean_inc_ref(v___f_2258_);
lean_inc(v_modifyEnv_2257_);
lean_inc(v___f_2256_);
lean_inc(v_toBind_2255_);
lean_inc_ref(v_inst_2254_);
lean_inc_ref(v_inst_2253_);
lean_inc(v_decl_2252_);
lean_inc_ref(v_env_2259_);
lean_inc_ref(v_attr_2251_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2260_, 0, v_attr_2251_);
lean_closure_set(v___f_2260_, 1, v_env_2259_);
lean_closure_set(v___f_2260_, 2, v_decl_2252_);
lean_closure_set(v___f_2260_, 3, v_inst_2253_);
lean_closure_set(v___f_2260_, 4, v_inst_2254_);
lean_closure_set(v___f_2260_, 5, v_toBind_2255_);
lean_closure_set(v___f_2260_, 6, v___f_2256_);
lean_closure_set(v___f_2260_, 7, v_modifyEnv_2257_);
lean_closure_set(v___f_2260_, 8, v___f_2258_);
v___x_2261_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2259_, v_decl_2252_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v___f_2260_);
v___x_2262_ = lean_box(0);
v___x_2263_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2251_, v_env_2259_, v_decl_2252_, v_inst_2253_, v_inst_2254_, v_toBind_2255_, v___f_2256_, v_modifyEnv_2257_, v___f_2258_, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v_attr_2264_; lean_object* v_toAttributeImplCore_2265_; lean_object* v_name_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec_ref_known(v___x_2261_, 1);
lean_dec_ref(v_env_2259_);
lean_dec_ref(v___f_2258_);
lean_dec(v_modifyEnv_2257_);
lean_dec(v___f_2256_);
v_attr_2264_ = lean_ctor_get(v_attr_2251_, 0);
lean_inc_ref(v_attr_2264_);
lean_dec_ref(v_attr_2251_);
v_toAttributeImplCore_2265_ = lean_ctor_get(v_attr_2264_, 0);
lean_inc_ref(v_toAttributeImplCore_2265_);
lean_dec_ref(v_attr_2264_);
v_name_2266_ = lean_ctor_get(v_toAttributeImplCore_2265_, 1);
lean_inc(v_name_2266_);
lean_dec_ref(v_toAttributeImplCore_2265_);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2267_, 0, v___f_2260_);
v___x_2268_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2253_, v_inst_2254_, v_name_2266_, v_decl_2252_);
v___x_2269_ = lean_apply_4(v_toBind_2255_, lean_box(0), lean_box(0), v___x_2268_, v___f_2267_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_inst_2272_, lean_object* v_attr_2273_, lean_object* v_decl_2274_){
_start:
{
lean_object* v_toBind_2275_; lean_object* v_getEnv_2276_; lean_object* v_modifyEnv_2277_; lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; 
v_toBind_2275_ = lean_ctor_get(v_inst_2270_, 1);
lean_inc_n(v_toBind_2275_, 2);
v_getEnv_2276_ = lean_ctor_get(v_inst_2272_, 0);
lean_inc(v_getEnv_2276_);
v_modifyEnv_2277_ = lean_ctor_get(v_inst_2272_, 1);
lean_inc_n(v_modifyEnv_2277_, 2);
lean_dec_ref(v_inst_2272_);
lean_inc(v_decl_2274_);
lean_inc_ref(v_attr_2273_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2278_, 0, v_attr_2273_);
lean_closure_set(v___f_2278_, 1, v_decl_2274_);
lean_inc_ref(v___f_2278_);
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2279_, 0, v_modifyEnv_2277_);
lean_closure_set(v___f_2279_, 1, v___f_2278_);
v___f_2280_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2280_, 0, v_attr_2273_);
lean_closure_set(v___f_2280_, 1, v_decl_2274_);
lean_closure_set(v___f_2280_, 2, v_inst_2270_);
lean_closure_set(v___f_2280_, 3, v_inst_2271_);
lean_closure_set(v___f_2280_, 4, v_toBind_2275_);
lean_closure_set(v___f_2280_, 5, v___f_2279_);
lean_closure_set(v___f_2280_, 6, v_modifyEnv_2277_);
lean_closure_set(v___f_2280_, 7, v___f_2278_);
v___x_2281_ = lean_apply_4(v_toBind_2275_, lean_box(0), lean_box(0), v_getEnv_2276_, v___f_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_attr_2286_, lean_object* v_decl_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2283_, v_inst_2284_, v_inst_2285_, v_attr_2286_, v_decl_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2289_, lean_object* v_k_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_m_2295_; lean_object* v_a_2296_; uint8_t v___x_2297_; 
v___x_2293_ = lean_nat_add(v_x_2291_, v_x_2292_);
v___x_2294_ = lean_unsigned_to_nat(1u);
v_m_2295_ = lean_nat_shiftr(v___x_2293_, v___x_2294_);
lean_dec(v___x_2293_);
v_a_2296_ = lean_array_fget_borrowed(v_as_2289_, v_m_2295_);
v___x_2297_ = l_Lean_Name_quickLt(v_a_2296_, v_k_2290_);
if (v___x_2297_ == 0)
{
uint8_t v___x_2298_; 
lean_dec(v_x_2292_);
v___x_2298_ = l_Lean_Name_quickLt(v_k_2290_, v_a_2296_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; 
lean_dec(v_m_2295_);
lean_dec(v_x_2291_);
v___x_2299_ = 1;
return v___x_2299_;
}
else
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_nat_dec_eq(v_m_2295_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_nat_sub(v_m_2295_, v___x_2294_);
lean_dec(v_m_2295_);
v___x_2303_ = lean_nat_dec_lt(v___x_2302_, v_x_2291_);
if (v___x_2303_ == 0)
{
v_x_2292_ = v___x_2302_;
goto _start;
}
else
{
lean_dec(v___x_2302_);
lean_dec(v_x_2291_);
return v___x_2297_;
}
}
else
{
lean_dec(v_m_2295_);
lean_dec(v_x_2291_);
return v___x_2297_;
}
}
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
lean_dec(v_x_2291_);
v___x_2305_ = lean_nat_add(v_m_2295_, v___x_2294_);
lean_dec(v_m_2295_);
v___x_2306_ = lean_nat_dec_le(v___x_2305_, v_x_2292_);
if (v___x_2306_ == 0)
{
lean_dec(v___x_2305_);
lean_dec(v_x_2292_);
return v___x_2306_;
}
else
{
v_x_2291_ = v___x_2305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2308_, lean_object* v_k_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
uint8_t v_res_2312_; lean_object* v_r_2313_; 
v_res_2312_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2308_, v_k_2309_, v_x_2310_, v_x_2311_);
lean_dec(v_k_2309_);
lean_dec_ref(v_as_2308_);
v_r_2313_ = lean_box(v_res_2312_);
return v_r_2313_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2314_, lean_object* v_env_2315_, lean_object* v_decl_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_box(1);
v___x_2318_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2315_, v_decl_2316_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_ext_2319_; lean_object* v_toEnvExtension_2320_; lean_object* v_asyncMode_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_ext_2319_ = lean_ctor_get(v_attr_2314_, 1);
v_toEnvExtension_2320_ = lean_ctor_get(v_ext_2319_, 0);
v_asyncMode_2321_ = lean_ctor_get(v_toEnvExtension_2320_, 2);
lean_inc(v_decl_2316_);
v___x_2322_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2317_, v_ext_2319_, v_env_2315_, v_asyncMode_2321_, v_decl_2316_);
v___x_2323_ = l_Lean_NameSet_contains(v___x_2322_, v_decl_2316_);
lean_dec(v_decl_2316_);
lean_dec(v___x_2322_);
return v___x_2323_;
}
else
{
lean_object* v_val_2324_; lean_object* v_ext_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v_val_2324_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_val_2324_);
lean_dec_ref_known(v___x_2318_, 1);
v_ext_2325_ = lean_ctor_get(v_attr_2314_, 1);
v___x_2326_ = 0;
v___x_2327_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2317_, v_ext_2325_, v_env_2315_, v_val_2324_, v___x_2326_);
lean_dec(v_val_2324_);
lean_dec_ref(v_env_2315_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_array_get_size(v___x_2327_);
v___x_2330_ = lean_nat_dec_lt(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v___x_2327_);
lean_dec(v_decl_2316_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_sub(v___x_2329_, v___x_2331_);
v___x_2333_ = lean_nat_dec_le(v___x_2328_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec(v___x_2332_);
lean_dec_ref(v___x_2327_);
lean_dec(v_decl_2316_);
return v___x_2333_;
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2327_, v_decl_2316_, v___x_2328_, v___x_2332_);
lean_dec(v_decl_2316_);
lean_dec_ref(v___x_2327_);
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2335_, lean_object* v_env_2336_, lean_object* v_decl_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Lean_TagAttribute_hasTag(v_attr_2335_, v_env_2336_, v_decl_2337_);
lean_dec_ref(v_attr_2335_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2340_, lean_object* v_k_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2340_, v_k_2341_, v_x_2342_, v_x_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2346_, lean_object* v_k_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
uint8_t v_res_2351_; lean_object* v_r_2352_; 
v_res_2351_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2346_, v_k_2347_, v_x_2348_, v_x_2349_, v_x_2350_);
lean_dec(v_k_2347_);
lean_dec_ref(v_as_2346_);
v_r_2352_ = lean_box(v_res_2351_);
return v_r_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2358_, v___y_2359_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_x_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2362_, lean_object* v_x_2363_){
_start:
{
lean_inc_ref(v_s_2362_);
return v_s_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2364_, lean_object* v_x_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2364_, v_x_2365_);
lean_dec_ref(v_x_2365_);
lean_dec_ref(v_s_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2374_, v_x_2375_);
lean_dec_ref(v_x_2375_);
lean_dec_ref(v_x_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_box(0);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2379_);
lean_dec_ref(v_x_2379_);
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2386_; lean_object* v___f_2387_; lean_object* v___f_2388_; lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2387_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2388_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2389_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2392_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v___x_2390_);
lean_ctor_set(v___x_2392_, 2, v___f_2389_);
lean_ctor_set(v___x_2392_, 3, v___f_2388_);
lean_ctor_set(v___x_2392_, 4, v___f_2387_);
lean_ctor_set(v___x_2392_, 5, v___f_2386_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2393_ = 0;
v___x_2394_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2395_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2396_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2394_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*2, v___x_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2402_, lean_object* v_p_2403_){
_start:
{
lean_object* v_fst_2404_; lean_object* v_snd_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2422_; 
v_fst_2404_ = lean_ctor_get(v_x_2402_, 0);
v_snd_2405_ = lean_ctor_get(v_x_2402_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_x_2402_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2407_ = v_x_2402_;
v_isShared_2408_ = v_isSharedCheck_2422_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_snd_2405_);
lean_inc(v_fst_2404_);
lean_dec(v_x_2402_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2422_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2421_; 
v_fst_2409_ = lean_ctor_get(v_p_2403_, 0);
v_snd_2410_ = lean_ctor_get(v_p_2403_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_p_2403_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2412_ = v_p_2403_;
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snd_2410_);
lean_inc(v_fst_2409_);
lean_dec(v_p_2403_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2421_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
lean_inc(v_fst_2409_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set_tag(v___x_2407_, 1);
lean_ctor_set(v___x_2407_, 1, v_fst_2404_);
lean_ctor_set(v___x_2407_, 0, v_fst_2409_);
v___x_2415_ = v___x_2407_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fst_2409_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_fst_2404_);
v___x_2415_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2409_, v_snd_2410_, v_snd_2405_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2416_);
lean_ctor_set(v___x_2412_, 0, v___x_2415_);
v___x_2418_ = v___x_2412_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2423_, lean_object* v_x_2424_){
_start:
{
if (lean_obj_tag(v_x_2424_) == 0)
{
lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v_l_2427_; lean_object* v_r_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_k_2425_ = lean_ctor_get(v_x_2424_, 1);
v_v_2426_ = lean_ctor_get(v_x_2424_, 2);
v_l_2427_ = lean_ctor_get(v_x_2424_, 3);
v_r_2428_ = lean_ctor_get(v_x_2424_, 4);
v___x_2429_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2423_, v_l_2427_);
lean_inc(v_v_2426_);
lean_inc(v_k_2425_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_k_2425_);
lean_ctor_set(v___x_2430_, 1, v_v_2426_);
v___x_2431_ = lean_array_push(v___x_2429_, v___x_2430_);
v_init_2423_ = v___x_2431_;
v_x_2424_ = v_r_2428_;
goto _start;
}
else
{
return v_init_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2433_, v_x_2434_);
lean_dec(v_x_2434_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2436_, lean_object* v_as_2437_, size_t v_i_2438_, size_t v_stop_2439_, lean_object* v_b_2440_){
_start:
{
lean_object* v___y_2442_; uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_eq(v_i_2438_, v_stop_2439_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_array_uget_borrowed(v_as_2437_, v_i_2438_);
v___x_2448_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2436_, v___x_2447_);
if (lean_obj_tag(v___x_2448_) == 0)
{
v___y_2442_ = v_b_2440_;
goto v___jp_2441_;
}
else
{
lean_object* v_val_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_val_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_val_2449_);
lean_dec_ref_known(v___x_2448_, 1);
lean_inc(v___x_2447_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2447_);
lean_ctor_set(v___x_2450_, 1, v_val_2449_);
v___x_2451_ = lean_array_push(v_b_2440_, v___x_2450_);
v___y_2442_ = v___x_2451_;
goto v___jp_2441_;
}
}
else
{
return v_b_2440_;
}
v___jp_2441_:
{
size_t v___x_2443_; size_t v___x_2444_; 
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_add(v_i_2438_, v___x_2443_);
v_i_2438_ = v___x_2444_;
v_b_2440_ = v___y_2442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2452_, lean_object* v_as_2453_, lean_object* v_i_2454_, lean_object* v_stop_2455_, lean_object* v_b_2456_){
_start:
{
size_t v_i_boxed_2457_; size_t v_stop_boxed_2458_; lean_object* v_res_2459_; 
v_i_boxed_2457_ = lean_unbox_usize(v_i_2454_);
lean_dec(v_i_2454_);
v_stop_boxed_2458_ = lean_unbox_usize(v_stop_2455_);
lean_dec(v_stop_2455_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2452_, v_as_2453_, v_i_boxed_2457_, v_stop_boxed_2458_, v_b_2456_);
lean_dec_ref(v_as_2453_);
lean_dec(v_snd_2452_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2460_, lean_object* v_as_2461_, lean_object* v_start_2462_, lean_object* v_stop_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2465_ = lean_nat_dec_lt(v_start_2462_, v_stop_2463_);
if (v___x_2465_ == 0)
{
return v___x_2464_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_array_get_size(v_as_2461_);
v___x_2467_ = lean_nat_dec_le(v_stop_2463_, v___x_2466_);
if (v___x_2467_ == 0)
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_lt(v_start_2462_, v___x_2466_);
if (v___x_2468_ == 0)
{
return v___x_2464_;
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_usize_of_nat(v_start_2462_);
v___x_2470_ = lean_usize_of_nat(v___x_2466_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2460_, v_as_2461_, v___x_2469_, v___x_2470_, v___x_2464_);
return v___x_2471_;
}
}
else
{
size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_usize_of_nat(v_start_2462_);
v___x_2473_ = lean_usize_of_nat(v_stop_2463_);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2460_, v_as_2461_, v___x_2472_, v___x_2473_, v___x_2464_);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2475_, lean_object* v_as_2476_, lean_object* v_start_2477_, lean_object* v_stop_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2475_, v_as_2476_, v_start_2477_, v_stop_2478_);
lean_dec(v_stop_2478_);
lean_dec(v_start_2477_);
lean_dec_ref(v_as_2476_);
lean_dec(v_snd_2475_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2480_, lean_object* v_pivot_2481_, lean_object* v_as_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_nat_dec_lt(v_k_2484_, v_hi_2480_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v_k_2484_);
v___x_2486_ = lean_array_fswap(v_as_2482_, v_i_2483_, v_hi_2480_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v_i_2483_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v_fst_2489_; lean_object* v_fst_2490_; uint8_t v___x_2491_; 
v___x_2488_ = lean_array_fget_borrowed(v_as_2482_, v_k_2484_);
v_fst_2489_ = lean_ctor_get(v___x_2488_, 0);
v_fst_2490_ = lean_ctor_get(v_pivot_2481_, 0);
v___x_2491_ = l_Lean_Name_quickLt(v_fst_2489_, v_fst_2490_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_add(v_k_2484_, v___x_2492_);
lean_dec(v_k_2484_);
v_k_2484_ = v___x_2493_;
goto _start;
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2495_ = lean_array_fswap(v_as_2482_, v_i_2483_, v_k_2484_);
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = lean_nat_add(v_i_2483_, v___x_2496_);
lean_dec(v_i_2483_);
v___x_2498_ = lean_nat_add(v_k_2484_, v___x_2496_);
lean_dec(v_k_2484_);
v_as_2482_ = v___x_2495_;
v_i_2483_ = v___x_2497_;
v_k_2484_ = v___x_2498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2500_, lean_object* v_pivot_2501_, lean_object* v_as_2502_, lean_object* v_i_2503_, lean_object* v_k_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2500_, v_pivot_2501_, v_as_2502_, v_i_2503_, v_k_2504_);
lean_dec_ref(v_pivot_2501_);
lean_dec(v_hi_2500_);
return v_res_2505_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2506_, lean_object* v_b_2507_){
_start:
{
lean_object* v_fst_2508_; lean_object* v_fst_2509_; uint8_t v___x_2510_; 
v_fst_2508_ = lean_ctor_get(v_a_2506_, 0);
v_fst_2509_ = lean_ctor_get(v_b_2507_, 0);
v___x_2510_ = l_Lean_Name_quickLt(v_fst_2508_, v_fst_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2511_, lean_object* v_b_2512_){
_start:
{
uint8_t v_res_2513_; lean_object* v_r_2514_; 
v_res_2513_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2511_, v_b_2512_);
lean_dec_ref(v_b_2512_);
lean_dec_ref(v_a_2511_);
v_r_2514_ = lean_box(v_res_2513_);
return v_r_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2515_, lean_object* v_as_2516_, lean_object* v_lo_2517_, lean_object* v_hi_2518_){
_start:
{
lean_object* v___y_2520_; uint8_t v___x_2530_; 
v___x_2530_ = lean_nat_dec_lt(v_lo_2517_, v_hi_2518_);
if (v___x_2530_ == 0)
{
lean_dec(v_lo_2517_);
return v_as_2516_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_mid_2533_; lean_object* v___y_2535_; lean_object* v___y_2541_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2531_ = lean_nat_add(v_lo_2517_, v_hi_2518_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v_mid_2533_ = lean_nat_shiftr(v___x_2531_, v___x_2532_);
lean_dec(v___x_2531_);
v___x_2546_ = lean_array_fget_borrowed(v_as_2516_, v_mid_2533_);
v___x_2547_ = lean_array_fget_borrowed(v_as_2516_, v_lo_2517_);
v___x_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
v___y_2541_ = v_as_2516_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_array_fswap(v_as_2516_, v_lo_2517_, v_mid_2533_);
v___y_2541_ = v___x_2549_;
goto v___jp_2540_;
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2536_ = lean_array_fget_borrowed(v___y_2535_, v_mid_2533_);
v___x_2537_ = lean_array_fget_borrowed(v___y_2535_, v_hi_2518_);
v___x_2538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_dec(v_mid_2533_);
v___y_2520_ = v___y_2535_;
goto v___jp_2519_;
}
else
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_array_fswap(v___y_2535_, v_mid_2533_, v_hi_2518_);
lean_dec(v_mid_2533_);
v___y_2520_ = v___x_2539_;
goto v___jp_2519_;
}
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_array_fget_borrowed(v___y_2541_, v_hi_2518_);
v___x_2543_ = lean_array_fget_borrowed(v___y_2541_, v_lo_2517_);
v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
v___y_2535_ = v___y_2541_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_array_fswap(v___y_2541_, v_lo_2517_, v_hi_2518_);
v___y_2535_ = v___x_2545_;
goto v___jp_2534_;
}
}
}
v___jp_2519_:
{
lean_object* v_pivot_2521_; lean_object* v___x_2522_; lean_object* v_fst_2523_; lean_object* v_snd_2524_; uint8_t v___x_2525_; 
v_pivot_2521_ = lean_array_fget(v___y_2520_, v_hi_2518_);
lean_inc_n(v_lo_2517_, 2);
v___x_2522_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2518_, v_pivot_2521_, v___y_2520_, v_lo_2517_, v_lo_2517_);
lean_dec(v_pivot_2521_);
v_fst_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_fst_2523_);
v_snd_2524_ = lean_ctor_get(v___x_2522_, 1);
lean_inc(v_snd_2524_);
lean_dec_ref(v___x_2522_);
v___x_2525_ = lean_nat_dec_le(v_hi_2518_, v_fst_2523_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2515_, v_snd_2524_, v_lo_2517_, v_fst_2523_);
v___x_2527_ = lean_unsigned_to_nat(1u);
v___x_2528_ = lean_nat_add(v_fst_2523_, v___x_2527_);
lean_dec(v_fst_2523_);
v_as_2516_ = v___x_2526_;
v_lo_2517_ = v___x_2528_;
goto _start;
}
else
{
lean_dec(v_fst_2523_);
lean_dec(v_lo_2517_);
return v_snd_2524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2550_, lean_object* v_as_2551_, lean_object* v_lo_2552_, lean_object* v_hi_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2550_, v_as_2551_, v_lo_2552_, v_hi_2553_);
lean_dec(v_hi_2553_);
lean_dec(v_n_2550_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2555_, lean_object* v_env_2556_, lean_object* v_as_2557_, size_t v_i_2558_, size_t v_stop_2559_, lean_object* v_b_2560_){
_start:
{
lean_object* v___y_2562_; uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_eq(v_i_2558_, v_stop_2559_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2567_ = lean_array_uget_borrowed(v_as_2557_, v_i_2558_);
v_fst_2568_ = lean_ctor_get(v___x_2567_, 0);
v_snd_2569_ = lean_ctor_get(v___x_2567_, 1);
lean_inc_ref(v_filterExport_2555_);
lean_inc(v_snd_2569_);
lean_inc(v_fst_2568_);
lean_inc_ref(v_env_2556_);
v___x_2570_ = lean_apply_3(v_filterExport_2555_, v_env_2556_, v_fst_2568_, v_snd_2569_);
v___x_2571_ = lean_unbox(v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_2562_ = v_b_2560_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2572_; 
lean_inc(v___x_2567_);
v___x_2572_ = lean_array_push(v_b_2560_, v___x_2567_);
v___y_2562_ = v___x_2572_;
goto v___jp_2561_;
}
}
else
{
lean_dec_ref(v_env_2556_);
lean_dec_ref(v_filterExport_2555_);
return v_b_2560_;
}
v___jp_2561_:
{
size_t v___x_2563_; size_t v___x_2564_; 
v___x_2563_ = ((size_t)1ULL);
v___x_2564_ = lean_usize_add(v_i_2558_, v___x_2563_);
v_i_2558_ = v___x_2564_;
v_b_2560_ = v___y_2562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2573_, lean_object* v_env_2574_, lean_object* v_as_2575_, lean_object* v_i_2576_, lean_object* v_stop_2577_, lean_object* v_b_2578_){
_start:
{
size_t v_i_boxed_2579_; size_t v_stop_boxed_2580_; lean_object* v_res_2581_; 
v_i_boxed_2579_ = lean_unbox_usize(v_i_2576_);
lean_dec(v_i_2576_);
v_stop_boxed_2580_ = lean_unbox_usize(v_stop_2577_);
lean_dec(v_stop_2577_);
v_res_2581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2573_, v_env_2574_, v_as_2575_, v_i_boxed_2579_, v_stop_boxed_2580_, v_b_2578_);
lean_dec_ref(v_as_2575_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2582_, uint8_t v_preserveOrder_2583_, lean_object* v_env_2584_, lean_object* v_x_2585_){
_start:
{
lean_object* v___y_2587_; 
if (v_preserveOrder_2583_ == 0)
{
lean_object* v_snd_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_r_2606_; lean_object* v___x_2607_; lean_object* v___y_2609_; lean_object* v___y_2610_; uint8_t v___x_2612_; 
v_snd_2603_ = lean_ctor_get(v_x_2585_, 1);
lean_inc(v_snd_2603_);
lean_dec_ref(v_x_2585_);
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2606_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2605_, v_snd_2603_);
lean_dec(v_snd_2603_);
v___x_2607_ = lean_array_get_size(v_r_2606_);
v___x_2612_ = lean_nat_dec_eq(v___x_2607_, v___x_2604_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___y_2616_; uint8_t v___x_2618_; 
v___x_2613_ = lean_unsigned_to_nat(1u);
v___x_2614_ = lean_nat_sub(v___x_2607_, v___x_2613_);
v___x_2618_ = lean_nat_dec_le(v___x_2604_, v___x_2614_);
if (v___x_2618_ == 0)
{
lean_inc(v___x_2614_);
v___y_2616_ = v___x_2614_;
goto v___jp_2615_;
}
else
{
v___y_2616_ = v___x_2604_;
goto v___jp_2615_;
}
v___jp_2615_:
{
uint8_t v___x_2617_; 
v___x_2617_ = lean_nat_dec_le(v___y_2616_, v___x_2614_);
if (v___x_2617_ == 0)
{
lean_dec(v___x_2614_);
lean_inc(v___y_2616_);
v___y_2609_ = v___y_2616_;
v___y_2610_ = v___y_2616_;
goto v___jp_2608_;
}
else
{
v___y_2609_ = v___y_2616_;
v___y_2610_ = v___x_2614_;
goto v___jp_2608_;
}
}
}
else
{
v___y_2587_ = v_r_2606_;
goto v___jp_2586_;
}
v___jp_2608_:
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2607_, v_r_2606_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
v___y_2587_ = v___x_2611_;
goto v___jp_2586_;
}
}
else
{
lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_fst_2619_ = lean_ctor_get(v_x_2585_, 0);
lean_inc(v_fst_2619_);
v_snd_2620_ = lean_ctor_get(v_x_2585_, 1);
lean_inc(v_snd_2620_);
lean_dec_ref(v_x_2585_);
v___x_2621_ = lean_array_mk(v_fst_2619_);
v___x_2622_ = l_Array_reverse___redArg(v___x_2621_);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_array_get_size(v___x_2622_);
v___x_2625_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2620_, v___x_2622_, v___x_2623_, v___x_2624_);
lean_dec_ref(v___x_2622_);
lean_dec(v_snd_2620_);
v___y_2587_ = v___x_2625_;
goto v___jp_2586_;
}
v___jp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_array_get_size(v___y_2587_);
v___x_2590_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2591_ = lean_nat_dec_lt(v___x_2588_, v___x_2589_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref(v_env_2584_);
lean_dec_ref(v_filterExport_2582_);
v___x_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2590_);
lean_ctor_set(v___x_2592_, 2, v___y_2587_);
return v___x_2592_;
}
else
{
uint8_t v___x_2593_; 
v___x_2593_ = lean_nat_dec_le(v___x_2589_, v___x_2589_);
if (v___x_2593_ == 0)
{
if (v___x_2591_ == 0)
{
lean_object* v___x_2594_; 
lean_dec_ref(v_env_2584_);
lean_dec_ref(v_filterExport_2582_);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2590_);
lean_ctor_set(v___x_2594_, 1, v___x_2590_);
lean_ctor_set(v___x_2594_, 2, v___y_2587_);
return v___x_2594_;
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2589_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2582_, v_env_2584_, v___y_2587_, v___x_2595_, v___x_2596_, v___x_2590_);
lean_inc_ref(v___x_2597_);
v___x_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_ctor_set(v___x_2598_, 2, v___y_2587_);
return v___x_2598_;
}
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_of_nat(v___x_2589_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2582_, v_env_2584_, v___y_2587_, v___x_2599_, v___x_2600_, v___x_2590_);
lean_inc_ref(v___x_2601_);
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_ctor_set(v___x_2602_, 2, v___y_2587_);
return v___x_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2626_, lean_object* v_preserveOrder_2627_, lean_object* v_env_2628_, lean_object* v_x_2629_){
_start:
{
uint8_t v_preserveOrder_boxed_2630_; lean_object* v_res_2631_; 
v_preserveOrder_boxed_2630_ = lean_unbox(v_preserveOrder_2627_);
v_res_2631_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2626_, v_preserveOrder_boxed_2630_, v_env_2628_, v_x_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2641_){
_start:
{
lean_object* v_snd_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2656_; 
v_snd_2642_ = lean_ctor_get(v_x_2641_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_x_2641_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v_x_2641_, 0);
lean_dec(v_unused_2657_);
v___x_2644_ = v_x_2641_;
v_isShared_2645_ = v_isSharedCheck_2656_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_snd_2642_);
lean_dec(v_x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2656_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___y_2648_; 
v___x_2646_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2642_) == 0)
{
lean_object* v_size_2654_; 
v_size_2654_ = lean_ctor_get(v_snd_2642_, 0);
lean_inc(v_size_2654_);
lean_dec_ref_known(v_snd_2642_, 5);
v___y_2648_ = v_size_2654_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___y_2648_ = v___x_2655_;
goto v___jp_2647_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = l_Nat_reprFast(v___y_2648_);
v___x_2650_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 5);
lean_ctor_set(v___x_2644_, 1, v___x_2650_);
lean_ctor_set(v___x_2644_, 0, v___x_2646_);
v___x_2652_ = v___x_2644_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2660_);
lean_dec_ref(v_x_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2662_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2665_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2668_, lean_object* v_x_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2668_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2673_, lean_object* v_x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2673_, v_x_2674_, v___y_2675_);
lean_dec_ref(v___y_2675_);
lean_dec_ref(v_x_2674_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2688_, uint8_t v_preserveOrder_2689_, lean_object* v_filterExport_2690_){
_start:
{
lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___f_2692_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2693_ = lean_box(v_preserveOrder_2689_);
v___f_2694_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2694_, 0, v_filterExport_2690_);
lean_closure_set(v___f_2694_, 1, v___x_2693_);
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2697_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2698_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2699_ = lean_box(2);
v___x_2700_ = lean_box(0);
v___x_2701_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2701_, 0, v_ref_2688_);
lean_ctor_set(v___x_2701_, 1, v___f_2697_);
lean_ctor_set(v___x_2701_, 2, v___f_2698_);
lean_ctor_set(v___x_2701_, 3, v___f_2692_);
lean_ctor_set(v___x_2701_, 4, v___f_2694_);
lean_ctor_set(v___x_2701_, 5, v___f_2695_);
lean_ctor_set(v___x_2701_, 6, v___x_2699_);
lean_ctor_set(v___x_2701_, 7, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___f_2696_);
v___x_2703_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2704_, lean_object* v_preserveOrder_2705_, lean_object* v_filterExport_2706_, lean_object* v_a_2707_){
_start:
{
uint8_t v_preserveOrder_boxed_2708_; lean_object* v_res_2709_; 
v_preserveOrder_boxed_2708_ = lean_unbox(v_preserveOrder_2705_);
v_res_2709_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2704_, v_preserveOrder_boxed_2708_, v_filterExport_2706_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2710_, lean_object* v_ref_2711_, uint8_t v_preserveOrder_2712_, lean_object* v_filterExport_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2711_, v_preserveOrder_2712_, v_filterExport_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_ref_2717_, lean_object* v_preserveOrder_2718_, lean_object* v_filterExport_2719_, lean_object* v_a_2720_){
_start:
{
uint8_t v_preserveOrder_boxed_2721_; lean_object* v_res_2722_; 
v_preserveOrder_boxed_2721_ = lean_unbox(v_preserveOrder_2718_);
v_res_2722_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2716_, v_ref_2717_, v_preserveOrder_boxed_2721_, v_filterExport_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2723_, lean_object* v_filterExport_2724_, lean_object* v_env_2725_, lean_object* v_as_2726_, size_t v_i_2727_, size_t v_stop_2728_, lean_object* v_b_2729_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2724_, v_env_2725_, v_as_2726_, v_i_2727_, v_stop_2728_, v_b_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2731_, lean_object* v_filterExport_2732_, lean_object* v_env_2733_, lean_object* v_as_2734_, lean_object* v_i_2735_, lean_object* v_stop_2736_, lean_object* v_b_2737_){
_start:
{
size_t v_i_boxed_2738_; size_t v_stop_boxed_2739_; lean_object* v_res_2740_; 
v_i_boxed_2738_ = lean_unbox_usize(v_i_2735_);
lean_dec(v_i_2735_);
v_stop_boxed_2739_ = lean_unbox_usize(v_stop_2736_);
lean_dec(v_stop_2736_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2731_, v_filterExport_2732_, v_env_2733_, v_as_2734_, v_i_boxed_2738_, v_stop_boxed_2739_, v_b_2737_);
lean_dec_ref(v_as_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2741_, lean_object* v_t_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2741_, v_t_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2744_, lean_object* v_t_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2744_, v_t_2745_);
lean_dec(v_t_2745_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2747_, lean_object* v_init_2748_, lean_object* v_t_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2748_, v_t_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_init_2752_, lean_object* v_t_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2751_, v_init_2752_, v_t_2753_);
lean_dec(v_t_2753_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2755_, lean_object* v_n_2756_, lean_object* v_as_2757_, lean_object* v_lo_2758_, lean_object* v_hi_2759_, lean_object* v_w_2760_, lean_object* v_hlo_2761_, lean_object* v_hhi_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2756_, v_as_2757_, v_lo_2758_, v_hi_2759_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2764_, lean_object* v_n_2765_, lean_object* v_as_2766_, lean_object* v_lo_2767_, lean_object* v_hi_2768_, lean_object* v_w_2769_, lean_object* v_hlo_2770_, lean_object* v_hhi_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2764_, v_n_2765_, v_as_2766_, v_lo_2767_, v_hi_2768_, v_w_2769_, v_hlo_2770_, v_hhi_2771_);
lean_dec(v_hi_2768_);
lean_dec(v_n_2765_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2773_, lean_object* v_snd_2774_, lean_object* v_as_2775_, lean_object* v_start_2776_, lean_object* v_stop_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2774_, v_as_2775_, v_start_2776_, v_stop_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_snd_2780_, lean_object* v_as_2781_, lean_object* v_start_2782_, lean_object* v_stop_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2779_, v_snd_2780_, v_as_2781_, v_start_2782_, v_stop_2783_);
lean_dec(v_stop_2783_);
lean_dec(v_start_2782_);
lean_dec_ref(v_as_2781_);
lean_dec(v_snd_2780_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2785_, lean_object* v_init_2786_, lean_object* v_x_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2786_, v_x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_init_2790_, lean_object* v_x_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2789_, v_init_2790_, v_x_2791_);
lean_dec(v_x_2791_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2793_, lean_object* v_n_2794_, lean_object* v_lo_2795_, lean_object* v_hi_2796_, lean_object* v_hhi_2797_, lean_object* v_pivot_2798_, lean_object* v_as_2799_, lean_object* v_i_2800_, lean_object* v_k_2801_, lean_object* v_ilo_2802_, lean_object* v_ik_2803_, lean_object* v_w_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2796_, v_pivot_2798_, v_as_2799_, v_i_2800_, v_k_2801_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_n_2807_, lean_object* v_lo_2808_, lean_object* v_hi_2809_, lean_object* v_hhi_2810_, lean_object* v_pivot_2811_, lean_object* v_as_2812_, lean_object* v_i_2813_, lean_object* v_k_2814_, lean_object* v_ilo_2815_, lean_object* v_ik_2816_, lean_object* v_w_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2806_, v_n_2807_, v_lo_2808_, v_hi_2809_, v_hhi_2810_, v_pivot_2811_, v_as_2812_, v_i_2813_, v_k_2814_, v_ilo_2815_, v_ik_2816_, v_w_2817_);
lean_dec_ref(v_pivot_2811_);
lean_dec(v_hi_2809_);
lean_dec(v_lo_2808_);
lean_dec(v_n_2807_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2819_, lean_object* v_snd_2820_, lean_object* v_as_2821_, size_t v_i_2822_, size_t v_stop_2823_, lean_object* v_b_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2820_, v_as_2821_, v_i_2822_, v_stop_2823_, v_b_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_snd_2827_, lean_object* v_as_2828_, lean_object* v_i_2829_, lean_object* v_stop_2830_, lean_object* v_b_2831_){
_start:
{
size_t v_i_boxed_2832_; size_t v_stop_boxed_2833_; lean_object* v_res_2834_; 
v_i_boxed_2832_ = lean_unbox_usize(v_i_2829_);
lean_dec(v_i_2829_);
v_stop_boxed_2833_ = lean_unbox_usize(v_stop_2830_);
lean_dec(v_stop_2830_);
v_res_2834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2826_, v_snd_2827_, v_as_2828_, v_i_boxed_2832_, v_stop_boxed_2833_, v_b_2831_);
lean_dec_ref(v_as_2828_);
lean_dec(v_snd_2827_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; lean_object* v_nextMacroScope_2839_; lean_object* v_ngen_2840_; lean_object* v_auxDeclNGen_2841_; lean_object* v_traceState_2842_; lean_object* v_messages_2843_; lean_object* v_infoState_2844_; lean_object* v_snapshotTasks_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2856_; 
v___x_2838_ = lean_st_ref_take(v___y_2836_);
v_nextMacroScope_2839_ = lean_ctor_get(v___x_2838_, 1);
v_ngen_2840_ = lean_ctor_get(v___x_2838_, 2);
v_auxDeclNGen_2841_ = lean_ctor_get(v___x_2838_, 3);
v_traceState_2842_ = lean_ctor_get(v___x_2838_, 4);
v_messages_2843_ = lean_ctor_get(v___x_2838_, 6);
v_infoState_2844_ = lean_ctor_get(v___x_2838_, 7);
v_snapshotTasks_2845_ = lean_ctor_get(v___x_2838_, 8);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; lean_object* v_unused_2858_; 
v_unused_2857_ = lean_ctor_get(v___x_2838_, 5);
lean_dec(v_unused_2857_);
v_unused_2858_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2858_);
v___x_2847_ = v___x_2838_;
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_snapshotTasks_2845_);
lean_inc(v_infoState_2844_);
lean_inc(v_messages_2843_);
lean_inc(v_traceState_2842_);
lean_inc(v_auxDeclNGen_2841_);
lean_inc(v_ngen_2840_);
lean_inc(v_nextMacroScope_2839_);
lean_dec(v___x_2838_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 5, v___x_2849_);
lean_ctor_set(v___x_2847_, 0, v_env_2835_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_env_2835_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_nextMacroScope_2839_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_ngen_2840_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_auxDeclNGen_2841_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_traceState_2842_);
lean_ctor_set(v_reuseFailAlloc_2855_, 5, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2855_, 6, v_messages_2843_);
lean_ctor_set(v_reuseFailAlloc_2855_, 7, v_infoState_2844_);
lean_ctor_set(v_reuseFailAlloc_2855_, 8, v_snapshotTasks_2845_);
v___x_2851_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = lean_st_ref_set(v___y_2836_, v___x_2851_);
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2859_, v___y_2860_);
lean_dec(v___y_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2863_, v___y_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2873_, lean_object* v_ext_2874_, lean_object* v_afterSet_2875_, lean_object* v_toAttributeImplCore_2876_, lean_object* v_decl_2877_, lean_object* v_stx_2878_, uint8_t v_kind_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; uint8_t v___x_2937_; uint8_t v___x_2938_; 
v___x_2937_ = 0;
v___x_2938_ = l_Lean_instBEqAttributeKind_beq(v_kind_2879_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v_name_2939_; lean_object* v___x_2940_; 
lean_dec(v_stx_2878_);
lean_dec(v_decl_2877_);
lean_dec_ref(v_afterSet_2875_);
lean_dec_ref(v_ext_2874_);
lean_dec_ref(v_getParam_2873_);
v_name_2939_ = lean_ctor_get(v_toAttributeImplCore_2876_, 1);
lean_inc(v_name_2939_);
lean_dec_ref(v_toAttributeImplCore_2876_);
v___x_2940_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2939_, v_kind_2879_, v___y_2880_, v___y_2881_);
return v___x_2940_;
}
else
{
goto v___jp_2931_;
}
v___jp_2883_:
{
if (v___y_2888_ == 0)
{
lean_object* v___x_2889_; 
lean_dec_ref(v___y_2885_);
v___x_2889_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2886_, v___y_2884_);
return v___x_2889_;
}
else
{
lean_dec_ref(v___y_2886_);
return v___y_2885_;
}
}
v___jp_2890_:
{
lean_object* v___x_2894_; 
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
lean_inc(v_decl_2877_);
v___x_2894_ = lean_apply_5(v_getParam_2873_, v_decl_2877_, v_stx_2878_, v___y_2892_, v___y_2893_, lean_box(0));
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v_toEnvExtension_2897_; lean_object* v_env_2898_; lean_object* v_nextMacroScope_2899_; lean_object* v_ngen_2900_; lean_object* v_auxDeclNGen_2901_; lean_object* v_traceState_2902_; lean_object* v_messages_2903_; lean_object* v_infoState_2904_; lean_object* v_snapshotTasks_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2921_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = lean_st_ref_take(v___y_2893_);
v_toEnvExtension_2897_ = lean_ctor_get(v_ext_2874_, 0);
v_env_2898_ = lean_ctor_get(v___x_2896_, 0);
v_nextMacroScope_2899_ = lean_ctor_get(v___x_2896_, 1);
v_ngen_2900_ = lean_ctor_get(v___x_2896_, 2);
v_auxDeclNGen_2901_ = lean_ctor_get(v___x_2896_, 3);
v_traceState_2902_ = lean_ctor_get(v___x_2896_, 4);
v_messages_2903_ = lean_ctor_get(v___x_2896_, 6);
v_infoState_2904_ = lean_ctor_get(v___x_2896_, 7);
v_snapshotTasks_2905_ = lean_ctor_get(v___x_2896_, 8);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v___x_2896_, 5);
lean_dec(v_unused_2922_);
v___x_2907_ = v___x_2896_;
v_isShared_2908_ = v_isSharedCheck_2921_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snapshotTasks_2905_);
lean_inc(v_infoState_2904_);
lean_inc(v_messages_2903_);
lean_inc(v_traceState_2902_);
lean_inc(v_auxDeclNGen_2901_);
lean_inc(v_ngen_2900_);
lean_inc(v_nextMacroScope_2899_);
lean_inc(v_env_2898_);
lean_dec(v___x_2896_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2921_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_asyncMode_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_asyncMode_2909_ = lean_ctor_get(v_toEnvExtension_2897_, 2);
lean_inc(v_asyncMode_2909_);
lean_inc(v_a_2895_);
lean_inc_n(v_decl_2877_, 2);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_decl_2877_);
lean_ctor_set(v___x_2910_, 1, v_a_2895_);
v___x_2911_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2874_, v_env_2898_, v___x_2910_, v_asyncMode_2909_, v_decl_2877_);
lean_dec(v_asyncMode_2909_);
v___x_2912_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 5, v___x_2912_);
lean_ctor_set(v___x_2907_, 0, v___x_2911_);
v___x_2914_ = v___x_2907_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_nextMacroScope_2899_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_ngen_2900_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v_auxDeclNGen_2901_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_traceState_2902_);
lean_ctor_set(v_reuseFailAlloc_2920_, 5, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2920_, 6, v_messages_2903_);
lean_ctor_set(v_reuseFailAlloc_2920_, 7, v_infoState_2904_);
lean_ctor_set(v_reuseFailAlloc_2920_, 8, v_snapshotTasks_2905_);
v___x_2914_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = lean_st_ref_set(v___y_2893_, v___x_2914_);
lean_inc(v___y_2893_);
lean_inc_ref(v___y_2892_);
v___x_2916_ = lean_apply_5(v_afterSet_2875_, v_decl_2877_, v_a_2895_, v___y_2892_, v___y_2893_, lean_box(0));
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_dec_ref(v___y_2891_);
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; uint8_t v___x_2918_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
v___x_2918_ = l_Lean_Exception_isInterrupt(v_a_2917_);
if (v___x_2918_ == 0)
{
uint8_t v___x_2919_; 
v___x_2919_ = l_Lean_Exception_isRuntime(v_a_2917_);
v___y_2884_ = v___y_2893_;
v___y_2885_ = v___x_2916_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___y_2892_;
v___y_2888_ = v___x_2919_;
goto v___jp_2883_;
}
else
{
lean_dec(v_a_2917_);
v___y_2884_ = v___y_2893_;
v___y_2885_ = v___x_2916_;
v___y_2886_ = v___y_2891_;
v___y_2887_ = v___y_2892_;
v___y_2888_ = v___x_2918_;
goto v___jp_2883_;
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref(v___y_2891_);
lean_dec(v_decl_2877_);
lean_dec_ref(v_afterSet_2875_);
lean_dec_ref(v_ext_2874_);
v_a_2923_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2894_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2894_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2931_:
{
lean_object* v___x_2932_; lean_object* v_env_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_st_ref_get(v___y_2881_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2934_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2933_, v_decl_2877_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2876_);
v___y_2891_ = v_env_2933_;
v___y_2892_ = v___y_2880_;
v___y_2893_ = v___y_2881_;
goto v___jp_2890_;
}
else
{
lean_object* v_name_2935_; lean_object* v___x_2936_; 
lean_dec_ref_known(v___x_2934_, 1);
lean_dec_ref(v_env_2933_);
lean_dec(v_stx_2878_);
lean_dec_ref(v_afterSet_2875_);
lean_dec_ref(v_ext_2874_);
lean_dec_ref(v_getParam_2873_);
v_name_2935_ = lean_ctor_get(v_toAttributeImplCore_2876_, 1);
lean_inc(v_name_2935_);
lean_dec_ref(v_toAttributeImplCore_2876_);
v___x_2936_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2935_, v_decl_2877_, v___y_2880_, v___y_2881_);
return v___x_2936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2941_, lean_object* v_ext_2942_, lean_object* v_afterSet_2943_, lean_object* v_toAttributeImplCore_2944_, lean_object* v_decl_2945_, lean_object* v_stx_2946_, lean_object* v_kind_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v_kind_boxed_2951_; lean_object* v_res_2952_; 
v_kind_boxed_2951_ = lean_unbox(v_kind_2947_);
v_res_2952_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2941_, v_ext_2942_, v_afterSet_2943_, v_toAttributeImplCore_2944_, v_decl_2945_, v_stx_2946_, v_kind_boxed_2951_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2953_, lean_object* v_decl_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_name_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_name_2958_ = lean_ctor_get(v_toAttributeImplCore_2953_, 1);
lean_inc(v_name_2958_);
lean_dec_ref(v_toAttributeImplCore_2953_);
v___x_2959_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2960_ = l_Lean_MessageData_ofName(v_name_2958_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2963_, v___y_2955_, v___y_2956_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2965_, lean_object* v_decl_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2965_, v_decl_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v_decl_2966_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2971_, lean_object* v_ext_2972_){
_start:
{
lean_object* v_toAttributeImplCore_2974_; lean_object* v_getParam_2975_; lean_object* v_afterSet_2976_; uint8_t v_preserveOrder_2977_; lean_object* v___f_2978_; lean_object* v___f_2979_; lean_object* v_attrImpl_2980_; lean_object* v___x_2981_; 
v_toAttributeImplCore_2974_ = lean_ctor_get(v_impl_2971_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2974_, 3);
v_getParam_2975_ = lean_ctor_get(v_impl_2971_, 1);
lean_inc_ref(v_getParam_2975_);
v_afterSet_2976_ = lean_ctor_get(v_impl_2971_, 2);
lean_inc_ref(v_afterSet_2976_);
v_preserveOrder_2977_ = lean_ctor_get_uint8(v_impl_2971_, sizeof(void*)*4);
lean_dec_ref(v_impl_2971_);
lean_inc_ref(v_ext_2972_);
v___f_2978_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2978_, 0, v_getParam_2975_);
lean_closure_set(v___f_2978_, 1, v_ext_2972_);
lean_closure_set(v___f_2978_, 2, v_afterSet_2976_);
lean_closure_set(v___f_2978_, 3, v_toAttributeImplCore_2974_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2979_, 0, v_toAttributeImplCore_2974_);
v_attrImpl_2980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2980_, 0, v_toAttributeImplCore_2974_);
lean_ctor_set(v_attrImpl_2980_, 1, v___f_2978_);
lean_ctor_set(v_attrImpl_2980_, 2, v___f_2979_);
lean_inc_ref(v_attrImpl_2980_);
v___x_2981_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2980_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2989_; 
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2990_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2989_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2985_, 0, v_attrImpl_2980_);
lean_ctor_set(v___x_2985_, 1, v_ext_2972_);
lean_ctor_set_uint8(v___x_2985_, sizeof(void*)*2, v_preserveOrder_2977_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref_known(v_attrImpl_2980_, 3);
lean_dec_ref(v_ext_2972_);
v_a_2991_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2981_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2981_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2999_, lean_object* v_ext_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2999_, v_ext_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3003_, lean_object* v_impl_3004_, lean_object* v_ext_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3004_, v_ext_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3008_, lean_object* v_impl_3009_, lean_object* v_ext_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3008_, v_impl_3009_, v_ext_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3013_){
_start:
{
lean_object* v_toAttributeImplCore_3015_; uint8_t v_preserveOrder_3016_; lean_object* v_filterExport_3017_; lean_object* v_ref_3018_; lean_object* v___x_3019_; 
v_toAttributeImplCore_3015_ = lean_ctor_get(v_impl_3013_, 0);
v_preserveOrder_3016_ = lean_ctor_get_uint8(v_impl_3013_, sizeof(void*)*4);
v_filterExport_3017_ = lean_ctor_get(v_impl_3013_, 3);
v_ref_3018_ = lean_ctor_get(v_toAttributeImplCore_3015_, 0);
lean_inc_ref(v_filterExport_3017_);
lean_inc(v_ref_3018_);
v___x_3019_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3018_, v_preserveOrder_3016_, v_filterExport_3017_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3013_, v_a_3020_);
return v___x_3021_;
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec_ref(v_impl_3013_);
v_a_3022_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3019_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3019_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_registerParametricAttribute___redArg(v_impl_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3033_, lean_object* v_impl_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_registerParametricAttribute___redArg(v_impl_3034_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3037_, lean_object* v_impl_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_registerParametricAttribute(v_00_u03b1_3037_, v_impl_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3041_, lean_object* v___x_3042_, lean_object* v___x_3043_, lean_object* v_a_3044_, lean_object* v_x_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_fst_3047_; uint8_t v___x_3048_; 
v_fst_3047_ = lean_ctor_get(v_a_3044_, 0);
v___x_3048_ = lean_name_eq(v_fst_3047_, v_decl_3041_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v_a_3044_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3042_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec_ref(v___x_3042_);
v___x_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_a_3044_);
v___x_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v___x_3043_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3054_, lean_object* v___x_3055_, lean_object* v___x_3056_, lean_object* v_a_3057_, lean_object* v_x_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3054_, v___x_3055_, v___x_3056_, v_a_3057_, v_x_3058_, v___y_3059_);
lean_dec_ref(v___y_3059_);
lean_dec(v_decl_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3088_, lean_object* v_ext_3089_, uint8_t v_preserveOrder_3090_, lean_object* v_env_3091_, lean_object* v_decl_3092_){
_start:
{
lean_object* v___y_3094_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3106_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3091_, v_decl_3092_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_toEnvExtension_3107_; lean_object* v_asyncMode_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v_snd_3111_; lean_object* v___x_3112_; 
lean_dec(v_inst_3088_);
v_toEnvExtension_3107_ = lean_ctor_get(v_ext_3089_, 0);
v_asyncMode_3108_ = lean_ctor_get(v_toEnvExtension_3107_, 2);
v___x_3109_ = lean_box(0);
v___x_3110_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_asyncMode_3108_, v___x_3109_);
v_snd_3111_ = lean_ctor_get(v___x_3110_, 1);
lean_inc(v_snd_3111_);
lean_dec(v___x_3110_);
v___x_3112_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3111_, v_decl_3092_);
lean_dec(v_decl_3092_);
lean_dec(v_snd_3111_);
return v___x_3112_;
}
else
{
if (v_preserveOrder_3090_ == 0)
{
lean_object* v_val_3113_; uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_val_3113_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3114_ = 0;
v___x_3115_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_val_3113_, v___x_3114_);
lean_dec(v_val_3113_);
lean_dec_ref(v_env_3091_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_array_get_size(v___x_3115_);
v___x_3118_ = lean_nat_dec_lt(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec_ref(v___x_3115_);
lean_dec(v_decl_3092_);
lean_dec(v_inst_3088_);
v___x_3119_ = lean_box(0);
return v___x_3119_;
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = lean_nat_sub(v___x_3117_, v___x_3120_);
v___x_3122_ = lean_nat_dec_le(v___x_3116_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec(v___x_3121_);
lean_dec_ref(v___x_3115_);
lean_dec(v_decl_3092_);
lean_dec(v_inst_3088_);
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
else
{
lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___f_3124_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_decl_3092_);
lean_ctor_set(v___x_3125_, 1, v_inst_3088_);
v___x_3126_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3127_ = l_Array_binSearchAux___redArg(v___f_3124_, v___x_3126_, v___x_3115_, v___x_3125_, v___x_3116_, v___x_3121_);
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3127_;
goto v___jp_3093_;
}
}
}
else
{
lean_object* v_val_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; size_t v_sz_3136_; size_t v___x_3137_; lean_object* v___x_3138_; lean_object* v_fst_3139_; 
lean_dec(v_inst_3088_);
v_val_3128_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3128_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3129_ = 0;
v___x_3130_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3105_, v_ext_3089_, v_env_3091_, v_val_3128_, v___x_3129_);
lean_dec(v_val_3128_);
lean_dec_ref(v_env_3091_);
v___x_3131_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_box(0);
v___x_3134_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3135_, 0, v_decl_3092_);
lean_closure_set(v___f_3135_, 1, v___x_3134_);
lean_closure_set(v___f_3135_, 2, v___x_3133_);
v_sz_3136_ = lean_array_size(v___x_3130_);
v___x_3137_ = ((size_t)0ULL);
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3131_, v___x_3130_, v___f_3135_, v_sz_3136_, v___x_3137_, v___x_3134_);
v_fst_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_fst_3139_);
lean_dec(v___x_3138_);
if (lean_obj_tag(v_fst_3139_) == 0)
{
return v___x_3132_;
}
else
{
lean_object* v_val_3140_; 
v_val_3140_ = lean_ctor_get(v_fst_3139_, 0);
lean_inc(v_val_3140_);
lean_dec_ref_known(v_fst_3139_, 1);
v___y_3094_ = v_val_3140_;
goto v___jp_3093_;
}
}
}
v___jp_3093_:
{
if (lean_obj_tag(v___y_3094_) == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
else
{
lean_object* v_val_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3104_; 
v_val_3096_ = lean_ctor_get(v___y_3094_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___y_3094_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3098_ = v___y_3094_;
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_val_3096_);
lean_dec(v___y_3094_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3104_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_snd_3100_; lean_object* v___x_3102_; 
v_snd_3100_ = lean_ctor_get(v_val_3096_, 1);
lean_inc(v_snd_3100_);
lean_dec(v_val_3096_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v_snd_3100_);
v___x_3102_ = v___x_3098_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_snd_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3141_, lean_object* v_ext_3142_, lean_object* v_preserveOrder_3143_, lean_object* v_env_3144_, lean_object* v_decl_3145_){
_start:
{
uint8_t v_preserveOrder_boxed_3146_; lean_object* v_res_3147_; 
v_preserveOrder_boxed_3146_ = lean_unbox(v_preserveOrder_3143_);
v_res_3147_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3141_, v_ext_3142_, v_preserveOrder_boxed_3146_, v_env_3144_, v_decl_3145_);
lean_dec_ref(v_ext_3142_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3148_, lean_object* v_inst_3149_, lean_object* v_ext_3150_, uint8_t v_preserveOrder_3151_, lean_object* v_env_3152_, lean_object* v_decl_3153_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3149_, v_ext_3150_, v_preserveOrder_3151_, v_env_3152_, v_decl_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3155_, lean_object* v_inst_3156_, lean_object* v_ext_3157_, lean_object* v_preserveOrder_3158_, lean_object* v_env_3159_, lean_object* v_decl_3160_){
_start:
{
uint8_t v_preserveOrder_boxed_3161_; lean_object* v_res_3162_; 
v_preserveOrder_boxed_3161_ = lean_unbox(v_preserveOrder_3158_);
v_res_3162_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3155_, v_inst_3156_, v_ext_3157_, v_preserveOrder_boxed_3161_, v_env_3159_, v_decl_3160_);
lean_dec_ref(v_ext_3157_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3163_, lean_object* v_attr_3164_, lean_object* v_env_3165_, lean_object* v_decl_3166_){
_start:
{
lean_object* v_ext_3167_; uint8_t v_preserveOrder_3168_; lean_object* v___x_3169_; 
v_ext_3167_ = lean_ctor_get(v_attr_3164_, 1);
v_preserveOrder_3168_ = lean_ctor_get_uint8(v_attr_3164_, sizeof(void*)*2);
v___x_3169_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3163_, v_ext_3167_, v_preserveOrder_3168_, v_env_3165_, v_decl_3166_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3170_, lean_object* v_attr_3171_, lean_object* v_env_3172_, lean_object* v_decl_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3170_, v_attr_3171_, v_env_3172_, v_decl_3173_);
lean_dec_ref(v_attr_3171_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3175_, lean_object* v_inst_3176_, lean_object* v_attr_3177_, lean_object* v_env_3178_, lean_object* v_decl_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3176_, v_attr_3177_, v_env_3178_, v_decl_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3181_, lean_object* v_inst_3182_, lean_object* v_attr_3183_, lean_object* v_env_3184_, lean_object* v_decl_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3181_, v_inst_3182_, v_attr_3183_, v_env_3184_, v_decl_3185_);
lean_dec_ref(v_attr_3183_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3191_, lean_object* v_attr_3192_, lean_object* v_env_3193_, lean_object* v_decl_3194_, lean_object* v_param_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3193_, v_decl_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_toEnvExtension_3197_; lean_object* v_asyncMode_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3232_; 
v_toEnvExtension_3197_ = lean_ctor_get(v_ext_3191_, 0);
v_asyncMode_3198_ = lean_ctor_get(v_toEnvExtension_3197_, 2);
lean_inc(v_asyncMode_3198_);
v___x_3199_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3200_ = lean_box(0);
lean_inc_ref(v_env_3193_);
v___x_3201_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3199_, v_ext_3191_, v_env_3193_, v_asyncMode_3198_, v___x_3200_);
v_snd_3202_ = lean_ctor_get(v___x_3201_, 1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v___x_3201_, 0);
lean_dec(v_unused_3233_);
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3232_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3202_, v_decl_3194_);
lean_dec(v_snd_3202_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v___x_3208_; 
lean_dec_ref(v_attr_3192_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v_param_3195_);
lean_ctor_set(v___x_3204_, 0, v_decl_3194_);
v___x_3208_ = v___x_3204_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_decl_3194_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_param_3195_);
v___x_3208_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3191_, v_env_3193_, v___x_3208_, v_asyncMode_3198_, v___x_3200_);
lean_dec(v_asyncMode_3198_);
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
}
else
{
lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3230_; 
lean_del_object(v___x_3204_);
lean_dec(v_asyncMode_3198_);
lean_dec(v_param_3195_);
lean_dec_ref(v_env_3193_);
lean_dec_ref(v_ext_3191_);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3206_, 0);
lean_dec(v_unused_3231_);
v___x_3213_ = v___x_3206_;
v_isShared_3214_ = v_isSharedCheck_3230_;
goto v_resetjp_3212_;
}
else
{
lean_dec(v___x_3206_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3230_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v_toAttributeImplCore_3215_; lean_object* v_name_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v_toAttributeImplCore_3215_ = lean_ctor_get(v_attr_3192_, 0);
lean_inc_ref(v_toAttributeImplCore_3215_);
lean_dec_ref(v_attr_3192_);
v_name_3216_ = lean_ctor_get(v_toAttributeImplCore_3215_, 1);
lean_inc(v_name_3216_);
lean_dec_ref(v_toAttributeImplCore_3215_);
v___x_3217_ = 1;
v___x_3218_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3216_, v___x_3217_);
v___x_3220_ = lean_string_append(v___x_3218_, v___x_3219_);
lean_dec_ref(v___x_3219_);
v___x_3221_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
v___x_3223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3194_, v___x_3217_);
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3226_ = lean_string_append(v___x_3224_, v___x_3225_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set_tag(v___x_3213_, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3226_);
v___x_3228_ = v___x_3213_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
else
{
lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_param_3195_);
lean_dec_ref(v_env_3193_);
lean_dec_ref(v_ext_3191_);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3196_, 0);
lean_dec(v_unused_3253_);
v___x_3235_ = v___x_3196_;
v_isShared_3236_ = v_isSharedCheck_3252_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v___x_3196_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3252_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_toAttributeImplCore_3237_; lean_object* v_name_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v_toAttributeImplCore_3237_ = lean_ctor_get(v_attr_3192_, 0);
lean_inc_ref(v_toAttributeImplCore_3237_);
lean_dec_ref(v_attr_3192_);
v_name_3238_ = lean_ctor_get(v_toAttributeImplCore_3237_, 1);
lean_inc(v_name_3238_);
lean_dec_ref(v_toAttributeImplCore_3237_);
v___x_3239_ = 1;
v___x_3240_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3238_, v___x_3239_);
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3244_ = lean_string_append(v___x_3242_, v___x_3243_);
v___x_3245_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3194_, v___x_3239_);
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3248_);
v___x_3250_ = v___x_3235_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3254_, lean_object* v_ext_3255_, lean_object* v_attr_3256_, lean_object* v_env_3257_, lean_object* v_decl_3258_, lean_object* v_param_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3255_, v_attr_3256_, v_env_3257_, v_decl_3258_, v_param_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3261_, lean_object* v_env_3262_, lean_object* v_decl_3263_, lean_object* v_param_3264_){
_start:
{
lean_object* v_attr_3265_; lean_object* v_ext_3266_; lean_object* v___x_3267_; 
v_attr_3265_ = lean_ctor_get(v_attr_3261_, 0);
lean_inc_ref(v_attr_3265_);
v_ext_3266_ = lean_ctor_get(v_attr_3261_, 1);
lean_inc_ref(v_ext_3266_);
lean_dec_ref(v_attr_3261_);
v___x_3267_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3266_, v_attr_3265_, v_env_3262_, v_decl_3263_, v_param_3264_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3268_, lean_object* v_attr_3269_, lean_object* v_env_3270_, lean_object* v_decl_3271_, lean_object* v_param_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3269_, v_env_3270_, v_decl_3271_, v_param_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3279_, v___y_3280_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v_x_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3283_, lean_object* v_x_3284_){
_start:
{
lean_inc(v_s_3283_);
return v_s_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3285_, v_x_3286_);
lean_dec_ref(v_x_3286_);
lean_dec(v_s_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3291_, v_x_3292_);
lean_dec(v_x_3292_);
lean_dec_ref(v_x_3291_);
return v_res_3293_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3297_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___f_3300_; lean_object* v___f_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3299_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3300_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3301_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3304_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v___f_3301_);
lean_ctor_set(v___x_3304_, 3, v___f_3300_);
lean_ctor_set(v___x_3304_, 4, v___f_3299_);
lean_ctor_set(v___x_3304_, 5, v___f_3298_);
return v___x_3304_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v___x_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3312_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3316_);
lean_dec(v_x_3316_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
if (lean_obj_tag(v_x_3320_) == 0)
{
return v_x_3319_;
}
else
{
lean_object* v_head_3321_; lean_object* v_tail_3322_; lean_object* v___x_3323_; 
v_head_3321_ = lean_ctor_get(v_x_3320_, 0);
lean_inc(v_head_3321_);
v_tail_3322_ = lean_ctor_get(v_x_3320_, 1);
lean_inc(v_tail_3322_);
lean_dec_ref_known(v_x_3320_, 2);
v___x_3323_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3318_, v_head_3321_);
if (lean_obj_tag(v___x_3323_) == 1)
{
lean_object* v_val_3324_; lean_object* v___x_3325_; 
v_val_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_val_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3321_, v_val_3324_, v_x_3319_);
v_x_3319_ = v___x_3325_;
v_x_3320_ = v_tail_3322_;
goto _start;
}
else
{
lean_dec(v___x_3323_);
lean_dec(v_head_3321_);
v_x_3320_ = v_tail_3322_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3328_, v_x_3329_, v_x_3330_);
lean_dec(v_newState_3328_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3332_, lean_object* v_newState_3333_, lean_object* v_consts_3334_, lean_object* v_st_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3333_, v_st_3335_, v_consts_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3337_, lean_object* v_newState_3338_, lean_object* v_consts_3339_, lean_object* v_st_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3337_, v_newState_3338_, v_consts_3339_, v_st_3340_);
lean_dec(v_newState_3338_);
lean_dec(v_x_3337_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3351_){
_start:
{
lean_object* v___x_3352_; lean_object* v___y_3354_; 
v___x_3352_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3351_) == 0)
{
lean_object* v_size_3358_; 
v_size_3358_ = lean_ctor_get(v_s_3351_, 0);
lean_inc(v_size_3358_);
lean_dec_ref_known(v_s_3351_, 5);
v___y_3354_ = v_size_3358_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_unsigned_to_nat(0u);
v___y_3354_ = v___x_3359_;
goto v___jp_3353_;
}
v___jp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = l_Nat_reprFast(v___y_3354_);
v___x_3356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
v___x_3357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3352_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3360_, lean_object* v_as_3361_, size_t v_i_3362_, size_t v_stop_3363_, lean_object* v_b_3364_){
_start:
{
lean_object* v___y_3366_; uint8_t v___x_3370_; 
v___x_3370_ = lean_usize_dec_eq(v_i_3362_, v_stop_3363_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v_fst_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3371_ = lean_array_uget_borrowed(v_as_3361_, v_i_3362_);
v_fst_3372_ = lean_ctor_get(v___x_3371_, 0);
v___x_3373_ = 1;
lean_inc_ref(v_env_3360_);
v___x_3374_ = l_Lean_Environment_setExporting(v_env_3360_, v___x_3373_);
lean_inc(v_fst_3372_);
v___x_3375_ = l_Lean_Environment_contains(v___x_3374_, v_fst_3372_, v___x_3370_);
if (v___x_3375_ == 0)
{
v___y_3366_ = v_b_3364_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3376_; 
lean_inc(v___x_3371_);
v___x_3376_ = lean_array_push(v_b_3364_, v___x_3371_);
v___y_3366_ = v___x_3376_;
goto v___jp_3365_;
}
}
else
{
lean_dec_ref(v_env_3360_);
return v_b_3364_;
}
v___jp_3365_:
{
size_t v___x_3367_; size_t v___x_3368_; 
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_add(v_i_3362_, v___x_3367_);
v_i_3362_ = v___x_3368_;
v_b_3364_ = v___y_3366_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3377_, lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_){
_start:
{
size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; lean_object* v_res_3384_; 
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3377_, v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_, v_b_3381_);
lean_dec_ref(v_as_3378_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3385_, lean_object* v_m_3386_){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___y_3390_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___x_3410_; 
v___x_3387_ = lean_unsigned_to_nat(0u);
v___x_3388_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3388_, v_m_3386_);
v___x_3405_ = lean_array_get_size(v___x_3404_);
v___x_3410_ = lean_nat_dec_eq(v___x_3405_, v___x_3387_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___y_3414_; uint8_t v___x_3416_; 
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_nat_sub(v___x_3405_, v___x_3411_);
v___x_3416_ = lean_nat_dec_le(v___x_3387_, v___x_3412_);
if (v___x_3416_ == 0)
{
lean_inc(v___x_3412_);
v___y_3414_ = v___x_3412_;
goto v___jp_3413_;
}
else
{
v___y_3414_ = v___x_3387_;
goto v___jp_3413_;
}
v___jp_3413_:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_nat_dec_le(v___y_3414_, v___x_3412_);
if (v___x_3415_ == 0)
{
lean_dec(v___x_3412_);
lean_inc(v___y_3414_);
v___y_3407_ = v___y_3414_;
v___y_3408_ = v___y_3414_;
goto v___jp_3406_;
}
else
{
v___y_3407_ = v___y_3414_;
v___y_3408_ = v___x_3412_;
goto v___jp_3406_;
}
}
}
else
{
v___y_3390_ = v___x_3404_;
goto v___jp_3389_;
}
v___jp_3389_:
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = lean_array_get_size(v___y_3390_);
v___x_3392_ = lean_nat_dec_lt(v___x_3387_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
lean_dec_ref(v_env_3385_);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3388_);
lean_ctor_set(v___x_3393_, 1, v___x_3388_);
lean_ctor_set(v___x_3393_, 2, v___y_3390_);
return v___x_3393_;
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
if (v___x_3394_ == 0)
{
if (v___x_3392_ == 0)
{
lean_object* v___x_3395_; 
lean_dec_ref(v_env_3385_);
v___x_3395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3388_);
lean_ctor_set(v___x_3395_, 1, v___x_3388_);
lean_ctor_set(v___x_3395_, 2, v___y_3390_);
return v___x_3395_;
}
else
{
size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3396_ = ((size_t)0ULL);
v___x_3397_ = lean_usize_of_nat(v___x_3391_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3385_, v___y_3390_, v___x_3396_, v___x_3397_, v___x_3388_);
lean_inc_ref(v___x_3398_);
v___x_3399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
lean_ctor_set(v___x_3399_, 2, v___y_3390_);
return v___x_3399_;
}
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = lean_usize_of_nat(v___x_3391_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3385_, v___y_3390_, v___x_3400_, v___x_3401_, v___x_3388_);
lean_inc_ref(v___x_3402_);
v___x_3403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
lean_ctor_set(v___x_3403_, 2, v___y_3390_);
return v___x_3403_;
}
}
}
v___jp_3406_:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3405_, v___x_3404_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
v___y_3390_ = v___x_3409_;
goto v___jp_3389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3417_, lean_object* v_m_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3417_, v_m_3418_);
lean_dec(v_m_3418_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3420_, lean_object* v_p_3421_){
_start:
{
lean_object* v_fst_3422_; lean_object* v_snd_3423_; lean_object* v___x_3424_; 
v_fst_3422_ = lean_ctor_get(v_p_3421_, 0);
lean_inc(v_fst_3422_);
v_snd_3423_ = lean_ctor_get(v_p_3421_, 1);
lean_inc(v_snd_3423_);
lean_dec_ref(v_p_3421_);
v___x_3424_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3422_, v_snd_3423_, v_s_3420_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3425_, lean_object* v_x_3426_, lean_object* v_x_3427_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3425_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3430_, lean_object* v_x_3431_, lean_object* v_x_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3430_, v_x_3431_, v_x_3432_);
lean_dec_ref(v_x_3432_);
lean_dec_ref(v_x_3431_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3435_){
_start:
{
if (lean_obj_tag(v_as_3435_) == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
else
{
lean_object* v_head_3439_; lean_object* v_tail_3440_; lean_object* v___x_3441_; 
v_head_3439_ = lean_ctor_get(v_as_3435_, 0);
lean_inc(v_head_3439_);
v_tail_3440_ = lean_ctor_get(v_as_3435_, 1);
lean_inc(v_tail_3440_);
lean_dec_ref_known(v_as_3435_, 2);
v___x_3441_ = l_Lean_registerBuiltinAttribute(v_head_3439_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_dec_ref_known(v___x_3441_, 1);
v_as_3435_ = v_tail_3440_;
goto _start;
}
else
{
lean_dec(v_tail_3440_);
return v___x_3441_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3446_, lean_object* v_snd_3447_, lean_object* v_a_3448_, lean_object* v_fst_3449_, lean_object* v_decl_3450_, lean_object* v_stx_3451_, uint8_t v_kind_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3451_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3499_) == 0)
{
uint8_t v___x_3500_; uint8_t v___x_3501_; 
lean_dec_ref_known(v___x_3499_, 1);
v___x_3500_ = 0;
v___x_3501_ = l_Lean_instBEqAttributeKind_beq(v_kind_3452_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v_decl_3450_);
lean_dec_ref(v_a_3448_);
lean_dec(v_snd_3447_);
lean_dec_ref(v_validate_3446_);
v___x_3502_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3449_, v_kind_3452_, v___y_3453_, v___y_3454_);
return v___x_3502_;
}
else
{
v___y_3493_ = v___y_3453_;
v___y_3494_ = v___y_3454_;
goto v___jp_3492_;
}
}
else
{
lean_dec(v_decl_3450_);
lean_dec(v_fst_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_snd_3447_);
lean_dec_ref(v_validate_3446_);
return v___x_3499_;
}
v___jp_3456_:
{
lean_object* v___x_3459_; 
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3457_);
lean_inc(v_snd_3447_);
lean_inc(v_decl_3450_);
v___x_3459_ = lean_apply_5(v_validate_3446_, v_decl_3450_, v_snd_3447_, v___y_3457_, v___y_3458_, lean_box(0));
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3490_; 
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3491_);
v___x_3461_ = v___x_3459_;
v_isShared_3462_ = v_isSharedCheck_3490_;
goto v_resetjp_3460_;
}
else
{
lean_dec(v___x_3459_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3490_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v_toEnvExtension_3464_; lean_object* v_env_3465_; lean_object* v_nextMacroScope_3466_; lean_object* v_ngen_3467_; lean_object* v_auxDeclNGen_3468_; lean_object* v_traceState_3469_; lean_object* v_messages_3470_; lean_object* v_infoState_3471_; lean_object* v_snapshotTasks_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3488_; 
v___x_3463_ = lean_st_ref_take(v___y_3458_);
v_toEnvExtension_3464_ = lean_ctor_get(v_a_3448_, 0);
v_env_3465_ = lean_ctor_get(v___x_3463_, 0);
v_nextMacroScope_3466_ = lean_ctor_get(v___x_3463_, 1);
v_ngen_3467_ = lean_ctor_get(v___x_3463_, 2);
v_auxDeclNGen_3468_ = lean_ctor_get(v___x_3463_, 3);
v_traceState_3469_ = lean_ctor_get(v___x_3463_, 4);
v_messages_3470_ = lean_ctor_get(v___x_3463_, 6);
v_infoState_3471_ = lean_ctor_get(v___x_3463_, 7);
v_snapshotTasks_3472_ = lean_ctor_get(v___x_3463_, 8);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3463_, 5);
lean_dec(v_unused_3489_);
v___x_3474_ = v___x_3463_;
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_snapshotTasks_3472_);
lean_inc(v_infoState_3471_);
lean_inc(v_messages_3470_);
lean_inc(v_traceState_3469_);
lean_inc(v_auxDeclNGen_3468_);
lean_inc(v_ngen_3467_);
lean_inc(v_nextMacroScope_3466_);
lean_inc(v_env_3465_);
lean_dec(v___x_3463_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_asyncMode_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v_asyncMode_3476_ = lean_ctor_get(v_toEnvExtension_3464_, 2);
lean_inc(v_asyncMode_3476_);
lean_inc(v_decl_3450_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v_decl_3450_);
lean_ctor_set(v___x_3477_, 1, v_snd_3447_);
v___x_3478_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3448_, v_env_3465_, v___x_3477_, v_asyncMode_3476_, v_decl_3450_);
lean_dec(v_asyncMode_3476_);
v___x_3479_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 5, v___x_3479_);
lean_ctor_set(v___x_3474_, 0, v___x_3478_);
v___x_3481_ = v___x_3474_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_nextMacroScope_3466_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_ngen_3467_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_auxDeclNGen_3468_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_traceState_3469_);
lean_ctor_set(v_reuseFailAlloc_3487_, 5, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3487_, 6, v_messages_3470_);
lean_ctor_set(v_reuseFailAlloc_3487_, 7, v_infoState_3471_);
lean_ctor_set(v_reuseFailAlloc_3487_, 8, v_snapshotTasks_3472_);
v___x_3481_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3482_ = lean_st_ref_set(v___y_3458_, v___x_3481_);
v___x_3483_ = lean_box(0);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3483_);
v___x_3485_ = v___x_3461_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
else
{
lean_dec(v_decl_3450_);
lean_dec_ref(v_a_3448_);
lean_dec(v_snd_3447_);
return v___x_3459_;
}
}
v___jp_3492_:
{
lean_object* v___x_3495_; lean_object* v_env_3496_; lean_object* v___x_3497_; 
v___x_3495_ = lean_st_ref_get(v___y_3494_);
v_env_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_ref(v_env_3496_);
lean_dec(v___x_3495_);
v___x_3497_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3496_, v_decl_3450_);
lean_dec_ref(v_env_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_dec(v_fst_3449_);
v___y_3457_ = v___y_3493_;
v___y_3458_ = v___y_3494_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3498_; 
lean_dec_ref_known(v___x_3497_, 1);
lean_dec_ref(v_a_3448_);
lean_dec(v_snd_3447_);
lean_dec_ref(v_validate_3446_);
v___x_3498_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3449_, v_decl_3450_, v___y_3493_, v___y_3494_);
return v___x_3498_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3503_, lean_object* v_snd_3504_, lean_object* v_a_3505_, lean_object* v_fst_3506_, lean_object* v_decl_3507_, lean_object* v_stx_3508_, lean_object* v_kind_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
uint8_t v_kind_boxed_3513_; lean_object* v_res_3514_; 
v_kind_boxed_3513_ = lean_unbox(v_kind_3509_);
v_res_3514_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3503_, v_snd_3504_, v_a_3505_, v_fst_3506_, v_decl_3507_, v_stx_3508_, v_kind_boxed_3513_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3515_, lean_object* v_decl_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3520_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3521_ = l_Lean_MessageData_ofName(v_fst_3515_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3524_, v___y_3517_, v___y_3518_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3526_, lean_object* v_decl_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3526_, v_decl_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v_decl_3527_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3532_, lean_object* v_a_3533_, lean_object* v_ref_3534_, uint8_t v_applicationTime_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
if (lean_obj_tag(v_a_3536_) == 0)
{
lean_object* v___x_3538_; 
lean_dec(v_ref_3534_);
lean_dec_ref(v_a_3533_);
lean_dec_ref(v_validate_3532_);
v___x_3538_ = l_List_reverse___redArg(v_a_3537_);
return v___x_3538_;
}
else
{
lean_object* v_head_3539_; lean_object* v_snd_3540_; lean_object* v_tail_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3556_; 
v_head_3539_ = lean_ctor_get(v_a_3536_, 0);
lean_inc(v_head_3539_);
v_snd_3540_ = lean_ctor_get(v_head_3539_, 1);
lean_inc(v_snd_3540_);
v_tail_3541_ = lean_ctor_get(v_a_3536_, 1);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_a_3536_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v_a_3536_, 0);
lean_dec(v_unused_3557_);
v___x_3543_ = v_a_3536_;
v_isShared_3544_ = v_isSharedCheck_3556_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_tail_3541_);
lean_dec(v_a_3536_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3556_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_fst_3545_; lean_object* v_fst_3546_; lean_object* v_snd_3547_; lean_object* v___f_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
v_fst_3545_ = lean_ctor_get(v_head_3539_, 0);
lean_inc_n(v_fst_3545_, 3);
lean_dec(v_head_3539_);
v_fst_3546_ = lean_ctor_get(v_snd_3540_, 0);
lean_inc(v_fst_3546_);
v_snd_3547_ = lean_ctor_get(v_snd_3540_, 1);
lean_inc(v_snd_3547_);
lean_dec(v_snd_3540_);
v___f_3548_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3548_, 0, v_fst_3545_);
lean_inc_ref(v_a_3533_);
lean_inc_ref(v_validate_3532_);
v___f_3549_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3549_, 0, v_validate_3532_);
lean_closure_set(v___f_3549_, 1, v_snd_3547_);
lean_closure_set(v___f_3549_, 2, v_a_3533_);
lean_closure_set(v___f_3549_, 3, v_fst_3545_);
lean_inc(v_ref_3534_);
v___x_3550_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3550_, 0, v_ref_3534_);
lean_ctor_set(v___x_3550_, 1, v_fst_3545_);
lean_ctor_set(v___x_3550_, 2, v_fst_3546_);
lean_ctor_set_uint8(v___x_3550_, sizeof(void*)*3, v_applicationTime_3535_);
v___x_3551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___f_3549_);
lean_ctor_set(v___x_3551_, 2, v___f_3548_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v_a_3537_);
lean_ctor_set(v___x_3543_, 0, v___x_3551_);
v___x_3553_ = v___x_3543_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_a_3537_);
v___x_3553_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
v_a_3536_ = v_tail_3541_;
v_a_3537_ = v___x_3553_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3558_, lean_object* v_a_3559_, lean_object* v_ref_3560_, lean_object* v_applicationTime_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_){
_start:
{
uint8_t v_applicationTime_boxed_3564_; lean_object* v_res_3565_; 
v_applicationTime_boxed_3564_ = lean_unbox(v_applicationTime_3561_);
v_res_3565_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3558_, v_a_3559_, v_ref_3560_, v_applicationTime_boxed_3564_, v_a_3562_, v_a_3563_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3579_, lean_object* v_validate_3580_, uint8_t v_applicationTime_3581_, lean_object* v_ref_3582_){
_start:
{
lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___f_3584_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3585_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3586_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3587_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3591_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3582_);
v___x_3592_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3592_, 0, v_ref_3582_);
lean_ctor_set(v___x_3592_, 1, v___f_3588_);
lean_ctor_set(v___x_3592_, 2, v___f_3589_);
lean_ctor_set(v___x_3592_, 3, v___f_3587_);
lean_ctor_set(v___x_3592_, 4, v___f_3586_);
lean_ctor_set(v___x_3592_, 5, v___f_3585_);
lean_ctor_set(v___x_3592_, 6, v___x_3590_);
lean_ctor_set(v___x_3592_, 7, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
lean_ctor_set(v___x_3593_, 1, v___f_3584_);
v___x_3594_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_n(v_a_3595_, 2);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = lean_box(0);
v___x_3597_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3580_, v_a_3595_, v_ref_3582_, v_applicationTime_3581_, v_attrDescrs_3579_, v___x_3596_);
lean_inc(v___x_3597_);
v___x_3598_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3606_; 
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3598_, 0);
lean_dec(v_unused_3607_);
v___x_3600_ = v___x_3598_;
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v___x_3598_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3606_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3597_);
lean_ctor_set(v___x_3602_, 1, v_a_3595_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v___x_3597_);
lean_dec(v_a_3595_);
v_a_3608_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3598_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3598_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_ref_3582_);
lean_dec_ref(v_validate_3580_);
lean_dec(v_attrDescrs_3579_);
v_a_3616_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3594_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3594_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3624_, lean_object* v_validate_3625_, lean_object* v_applicationTime_3626_, lean_object* v_ref_3627_, lean_object* v_a_3628_){
_start:
{
uint8_t v_applicationTime_boxed_3629_; lean_object* v_res_3630_; 
v_applicationTime_boxed_3629_ = lean_unbox(v_applicationTime_3626_);
v_res_3630_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3624_, v_validate_3625_, v_applicationTime_boxed_3629_, v_ref_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3631_, lean_object* v_attrDescrs_3632_, lean_object* v_validate_3633_, uint8_t v_applicationTime_3634_, lean_object* v_ref_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3632_, v_validate_3633_, v_applicationTime_3634_, v_ref_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3638_, lean_object* v_attrDescrs_3639_, lean_object* v_validate_3640_, lean_object* v_applicationTime_3641_, lean_object* v_ref_3642_, lean_object* v_a_3643_){
_start:
{
uint8_t v_applicationTime_boxed_3644_; lean_object* v_res_3645_; 
v_applicationTime_boxed_3644_ = lean_unbox(v_applicationTime_3641_);
v_res_3645_ = l_Lean_registerEnumAttributes(v_00_u03b1_3638_, v_attrDescrs_3639_, v_validate_3640_, v_applicationTime_boxed_3644_, v_ref_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3646_, lean_object* v_env_3647_, lean_object* v_as_3648_, size_t v_i_3649_, size_t v_stop_3650_, lean_object* v_b_3651_){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3647_, v_as_3648_, v_i_3649_, v_stop_3650_, v_b_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3653_, lean_object* v_env_3654_, lean_object* v_as_3655_, lean_object* v_i_3656_, lean_object* v_stop_3657_, lean_object* v_b_3658_){
_start:
{
size_t v_i_boxed_3659_; size_t v_stop_boxed_3660_; lean_object* v_res_3661_; 
v_i_boxed_3659_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_stop_boxed_3660_ = lean_unbox_usize(v_stop_3657_);
lean_dec(v_stop_3657_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3653_, v_env_3654_, v_as_3655_, v_i_boxed_3659_, v_stop_boxed_3660_, v_b_3658_);
lean_dec_ref(v_as_3655_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3662_, lean_object* v_newState_3663_, lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3663_, v_x_3664_, v_x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3667_, lean_object* v_newState_3668_, lean_object* v_x_3669_, lean_object* v_x_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3667_, v_newState_3668_, v_x_3669_, v_x_3670_);
lean_dec(v_newState_3668_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3672_, lean_object* v_validate_3673_, lean_object* v_a_3674_, lean_object* v_ref_3675_, uint8_t v_applicationTime_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3673_, v_a_3674_, v_ref_3675_, v_applicationTime_3676_, v_a_3677_, v_a_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_validate_3681_, lean_object* v_a_3682_, lean_object* v_ref_3683_, lean_object* v_applicationTime_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
uint8_t v_applicationTime_boxed_3687_; lean_object* v_res_3688_; 
v_applicationTime_boxed_3687_ = lean_unbox(v_applicationTime_3684_);
v_res_3688_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3680_, v_validate_3681_, v_a_3682_, v_ref_3683_, v_applicationTime_boxed_3687_, v_a_3685_, v_a_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3689_, lean_object* v_attr_3690_, lean_object* v_env_3691_, lean_object* v_decl_3692_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = lean_box(1);
v___x_3694_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3691_, v_decl_3692_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_ext_3695_; lean_object* v_toEnvExtension_3696_; lean_object* v_asyncMode_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v_inst_3689_);
v_ext_3695_ = lean_ctor_get(v_attr_3690_, 1);
lean_inc_ref(v_ext_3695_);
lean_dec_ref(v_attr_3690_);
v_toEnvExtension_3696_ = lean_ctor_get(v_ext_3695_, 0);
v_asyncMode_3697_ = lean_ctor_get(v_toEnvExtension_3696_, 2);
lean_inc(v_asyncMode_3697_);
lean_inc(v_decl_3692_);
v___x_3698_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3693_, v_ext_3695_, v_env_3691_, v_asyncMode_3697_, v_decl_3692_);
lean_dec(v_asyncMode_3697_);
lean_dec_ref(v_ext_3695_);
v___x_3699_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3698_, v_decl_3692_);
lean_dec(v_decl_3692_);
lean_dec(v___x_3698_);
return v___x_3699_;
}
else
{
lean_object* v_val_3700_; lean_object* v_ext_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3731_; 
v_val_3700_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v___x_3694_, 1);
v_ext_3701_ = lean_ctor_get(v_attr_3690_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_attr_3690_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_attr_3690_, 0);
lean_dec(v_unused_3732_);
v___x_3703_ = v_attr_3690_;
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_ext_3701_);
lean_dec(v_attr_3690_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3731_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3705_ = 0;
v___x_3706_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3693_, v_ext_3701_, v_env_3691_, v_val_3700_, v___x_3705_);
lean_dec(v_val_3700_);
lean_dec_ref(v_env_3691_);
lean_dec_ref(v_ext_3701_);
v___x_3707_ = lean_unsigned_to_nat(0u);
v___x_3708_ = lean_array_get_size(v___x_3706_);
v___x_3709_ = lean_nat_dec_lt(v___x_3707_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3706_);
lean_del_object(v___x_3703_);
lean_dec(v_decl_3692_);
lean_dec(v_inst_3689_);
v___x_3710_ = lean_box(0);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3711_ = lean_unsigned_to_nat(1u);
v___x_3712_ = lean_nat_sub(v___x_3708_, v___x_3711_);
v___x_3713_ = lean_nat_dec_le(v___x_3707_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec(v___x_3712_);
lean_dec_ref(v___x_3706_);
lean_del_object(v___x_3703_);
lean_dec(v_decl_3692_);
lean_dec(v_inst_3689_);
v___x_3714_ = lean_box(0);
return v___x_3714_;
}
else
{
lean_object* v___f_3715_; lean_object* v___x_3717_; 
v___f_3715_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 1, v_inst_3689_);
lean_ctor_set(v___x_3703_, 0, v_decl_3692_);
v___x_3717_ = v___x_3703_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_decl_3692_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_inst_3689_);
v___x_3717_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3719_ = l_Array_binSearchAux___redArg(v___f_3715_, v___x_3718_, v___x_3706_, v___x_3717_, v___x_3707_, v___x_3712_);
lean_dec_ref(v___x_3706_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_box(0);
return v___x_3720_;
}
else
{
lean_object* v_val_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3729_; 
v_val_3721_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3723_ = v___x_3719_;
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_val_3721_);
lean_dec(v___x_3719_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3729_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_snd_3725_; lean_object* v___x_3727_; 
v_snd_3725_ = lean_ctor_get(v_val_3721_, 1);
lean_inc(v_snd_3725_);
lean_dec(v_val_3721_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v_snd_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_snd_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3733_, lean_object* v_inst_3734_, lean_object* v_attr_3735_, lean_object* v_env_3736_, lean_object* v_decl_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3734_, v_attr_3735_, v_env_3736_, v_decl_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3747_, lean_object* v_env_3748_, lean_object* v_decl_3749_, lean_object* v_val_3750_){
_start:
{
lean_object* v_ext_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3815_; 
v_ext_3751_ = lean_ctor_get(v_attrs_3747_, 1);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_attrs_3747_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v_attrs_3747_, 0);
lean_dec(v_unused_3816_);
v___x_3753_ = v_attrs_3747_;
v_isShared_3754_ = v_isSharedCheck_3815_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_ext_3751_);
lean_dec(v_attrs_3747_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3815_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_toEnvExtension_3755_; lean_object* v_name_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v_pfx_3766_; lean_object* v___x_3767_; 
v_toEnvExtension_3755_ = lean_ctor_get(v_ext_3751_, 0);
v_name_3756_ = lean_ctor_get(v_ext_3751_, 1);
v___x_3757_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3758_ = 1;
lean_inc(v_name_3756_);
v___x_3759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3756_, v___x_3758_);
v___x_3760_ = lean_string_append(v___x_3757_, v___x_3759_);
lean_dec_ref(v___x_3759_);
v___x_3761_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
lean_inc(v_decl_3749_);
v___x_3763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3749_, v___x_3758_);
v___x_3764_ = lean_string_append(v___x_3762_, v___x_3763_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
v___x_3767_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3748_, v_decl_3749_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_asyncMode_3768_; uint8_t v___x_3775_; 
v_asyncMode_3768_ = lean_ctor_get(v_toEnvExtension_3755_, 2);
lean_inc(v_asyncMode_3768_);
lean_inc(v_decl_3749_);
lean_inc_ref(v_env_3748_);
v___x_3775_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3748_, v_decl_3749_, v_asyncMode_3768_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___y_3779_; lean_object* v___x_3783_; 
lean_dec(v_asyncMode_3768_);
lean_del_object(v___x_3753_);
lean_dec_ref(v_ext_3751_);
lean_dec(v_val_3750_);
lean_dec(v_decl_3749_);
v___x_3776_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3777_ = lean_string_append(v_pfx_3766_, v___x_3776_);
v___x_3783_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3748_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3779_ = v___x_3784_;
goto v___jp_3778_;
}
else
{
lean_object* v_val_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_val_3785_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_val_3785_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3786_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3785_, v___x_3758_);
v___x_3788_ = l_addParenHeuristic(v___x_3787_);
v___x_3789_ = lean_string_append(v___x_3786_, v___x_3788_);
lean_dec_ref(v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3791_ = lean_string_append(v___x_3789_, v___x_3790_);
v___y_3779_ = v___x_3791_;
goto v___jp_3778_;
}
v___jp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3780_ = lean_string_append(v___x_3777_, v___y_3779_);
lean_dec_ref(v___y_3779_);
v___x_3781_ = lean_string_append(v___x_3780_, v___x_3765_);
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
return v___x_3782_;
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_box(1);
lean_inc(v_decl_3749_);
lean_inc_ref(v_env_3748_);
v___x_3793_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3792_, v_ext_3751_, v_env_3748_, v_asyncMode_3768_, v_decl_3749_);
v___x_3794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3793_, v_decl_3749_);
lean_dec(v___x_3793_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_dec_ref(v_pfx_3766_);
goto v___jp_3769_;
}
else
{
lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3803_; 
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; 
v_unused_3804_ = lean_ctor_get(v___x_3794_, 0);
lean_dec(v_unused_3804_);
v___x_3796_ = v___x_3794_;
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
else
{
lean_dec(v___x_3794_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3803_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
if (v___x_3775_ == 0)
{
lean_del_object(v___x_3796_);
lean_dec_ref(v_pfx_3766_);
goto v___jp_3769_;
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
lean_dec(v_asyncMode_3768_);
lean_del_object(v___x_3753_);
lean_dec_ref(v_ext_3751_);
lean_dec(v_val_3750_);
lean_dec(v_decl_3749_);
lean_dec_ref(v_env_3748_);
v___x_3798_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3799_ = lean_string_append(v_pfx_3766_, v___x_3798_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set_tag(v___x_3796_, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3799_);
v___x_3801_ = v___x_3796_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
v___jp_3769_:
{
lean_object* v___x_3771_; 
lean_inc(v_decl_3749_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 1, v_val_3750_);
lean_ctor_set(v___x_3753_, 0, v_decl_3749_);
v___x_3771_ = v___x_3753_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_decl_3749_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_val_3750_);
v___x_3771_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3751_, v_env_3748_, v___x_3771_, v_asyncMode_3768_, v_decl_3749_);
lean_dec(v_asyncMode_3768_);
v___x_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
}
}
else
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3813_; 
lean_del_object(v___x_3753_);
lean_dec_ref(v_ext_3751_);
lean_dec(v_val_3750_);
lean_dec(v_decl_3749_);
lean_dec_ref(v_env_3748_);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v___x_3767_, 0);
lean_dec(v_unused_3814_);
v___x_3806_ = v___x_3767_;
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v___x_3767_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v___x_3808_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3809_ = lean_string_append(v_pfx_3766_, v___x_3808_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3809_);
v___x_3811_ = v___x_3806_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3817_, lean_object* v_attrs_3818_, lean_object* v_env_3819_, lean_object* v_decl_3820_, lean_object* v_val_3821_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3818_, v_env_3819_, v_decl_3820_, v_val_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3824_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3825_ = lean_st_mk_ref(v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3831_, lean_object* v_builder_3832_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v___x_3834_ = l_Lean_attributeImplBuilderTableRef;
v___x_3835_ = lean_st_ref_get(v___x_3834_);
v___x_3836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3835_, v_builderId_3831_);
lean_dec(v___x_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3837_ = lean_st_ref_take(v___x_3834_);
v___x_3838_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3837_, v_builderId_3831_, v_builder_3832_);
v___x_3839_ = lean_st_ref_set(v___x_3834_, v___x_3838_);
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
else
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_dec_ref(v_builder_3832_);
v___x_3841_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3842_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3831_, v___x_3836_);
v___x_3843_ = lean_string_append(v___x_3841_, v___x_3842_);
lean_dec_ref(v___x_3842_);
v___x_3844_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3845_ = lean_string_append(v___x_3843_, v___x_3844_);
v___x_3846_ = lean_mk_io_user_error(v___x_3845_);
v___x_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3848_, lean_object* v_builder_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_registerAttributeImplBuilder(v_builderId_3848_, v_builder_3849_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3852_){
_start:
{
if (lean_obj_tag(v_e_3852_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3862_; 
v_a_3854_ = lean_ctor_get(v_e_3852_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_e_3852_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3856_ = v_e_3852_;
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v_e_3852_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3862_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_mk_io_user_error(v_a_3854_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set_tag(v___x_3856_, 1);
lean_ctor_set(v___x_3856_, 0, v___x_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
v_a_3863_ = lean_ctor_get(v_e_3852_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_e_3852_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v_e_3852_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v_e_3852_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
lean_ctor_set_tag(v___x_3865_, 0);
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3871_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3874_, lean_object* v_e_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3878_, lean_object* v_e_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3878_, v_e_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3882_, lean_object* v_x_3883_){
_start:
{
if (lean_obj_tag(v_x_3883_) == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_box(0);
return v___x_3884_;
}
else
{
lean_object* v_key_3885_; lean_object* v_value_3886_; lean_object* v_tail_3887_; uint8_t v___x_3888_; 
v_key_3885_ = lean_ctor_get(v_x_3883_, 0);
v_value_3886_ = lean_ctor_get(v_x_3883_, 1);
v_tail_3887_ = lean_ctor_get(v_x_3883_, 2);
v___x_3888_ = lean_name_eq(v_key_3885_, v_a_3882_);
if (v___x_3888_ == 0)
{
v_x_3883_ = v_tail_3887_;
goto _start;
}
else
{
lean_object* v___x_3890_; 
lean_inc(v_value_3886_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_value_3886_);
return v___x_3890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3891_, lean_object* v_x_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3891_, v_x_3892_);
lean_dec(v_x_3892_);
lean_dec(v_a_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_buckets_3896_; lean_object* v___x_3897_; uint64_t v___y_3899_; 
v_buckets_3896_ = lean_ctor_get(v_m_3894_, 1);
v___x_3897_ = lean_array_get_size(v_buckets_3896_);
if (lean_obj_tag(v_a_3895_) == 0)
{
uint64_t v___x_3913_; 
v___x_3913_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3899_ = v___x_3913_;
goto v___jp_3898_;
}
else
{
uint64_t v_hash_3914_; 
v_hash_3914_ = lean_ctor_get_uint64(v_a_3895_, sizeof(void*)*2);
v___y_3899_ = v_hash_3914_;
goto v___jp_3898_;
}
v___jp_3898_:
{
uint64_t v___x_3900_; uint64_t v___x_3901_; uint64_t v_fold_3902_; uint64_t v___x_3903_; uint64_t v___x_3904_; uint64_t v___x_3905_; size_t v___x_3906_; size_t v___x_3907_; size_t v___x_3908_; size_t v___x_3909_; size_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3900_ = 32ULL;
v___x_3901_ = lean_uint64_shift_right(v___y_3899_, v___x_3900_);
v_fold_3902_ = lean_uint64_xor(v___y_3899_, v___x_3901_);
v___x_3903_ = 16ULL;
v___x_3904_ = lean_uint64_shift_right(v_fold_3902_, v___x_3903_);
v___x_3905_ = lean_uint64_xor(v_fold_3902_, v___x_3904_);
v___x_3906_ = lean_uint64_to_usize(v___x_3905_);
v___x_3907_ = lean_usize_of_nat(v___x_3897_);
v___x_3908_ = ((size_t)1ULL);
v___x_3909_ = lean_usize_sub(v___x_3907_, v___x_3908_);
v___x_3910_ = lean_usize_land(v___x_3906_, v___x_3909_);
v___x_3911_ = lean_array_uget_borrowed(v_buckets_3896_, v___x_3910_);
v___x_3912_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3895_, v___x_3911_);
return v___x_3912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_m_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_builderId_3923_; lean_object* v_ref_3924_; lean_object* v_args_3925_; lean_object* v___x_3926_; 
v___x_3921_ = l_Lean_attributeImplBuilderTableRef;
v___x_3922_ = lean_st_ref_get(v___x_3921_);
v_builderId_3923_ = lean_ctor_get(v_e_3919_, 0);
lean_inc(v_builderId_3923_);
v_ref_3924_ = lean_ctor_get(v_e_3919_, 1);
lean_inc(v_ref_3924_);
v_args_3925_ = lean_ctor_get(v_e_3919_, 2);
lean_inc(v_args_3925_);
lean_dec_ref(v_e_3919_);
v___x_3926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3922_, v_builderId_3923_);
lean_dec(v___x_3922_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v___x_3927_; uint8_t v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec(v_args_3925_);
lean_dec(v_ref_3924_);
v___x_3927_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3928_ = 1;
v___x_3929_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3923_, v___x_3928_);
v___x_3930_ = lean_string_append(v___x_3927_, v___x_3929_);
lean_dec_ref(v___x_3929_);
v___x_3931_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3932_ = lean_string_append(v___x_3930_, v___x_3931_);
v___x_3933_ = lean_mk_io_user_error(v___x_3932_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
else
{
lean_object* v_val_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v_builderId_3923_);
v_val_3935_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v___x_3926_, 1);
v___x_3936_ = lean_apply_2(v_val_3935_, v_ref_3924_, v_args_3925_);
v___x_3937_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3936_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_Lean_mkAttributeImplOfEntry(v_e_3938_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3941_, lean_object* v_m_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3942_, v_a_3943_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3945_, lean_object* v_m_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3945_, v_m_3946_, v_a_3947_);
lean_dec(v_a_3947_);
lean_dec_ref(v_m_3946_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3949_, lean_object* v_a_3950_, lean_object* v_x_3951_){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3950_, v_x_3951_);
return v___x_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3953_, lean_object* v_a_3954_, lean_object* v_x_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3953_, v_a_3954_, v_x_3955_);
lean_dec(v_x_3955_);
lean_dec(v_a_3954_);
return v_res_3956_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3958_ = lean_box(0);
v___x_3959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v___x_3957_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3960_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3963_ = l_Lean_attributeMapRef;
v___x_3964_ = lean_st_ref_get(v___x_3963_);
v___x_3965_ = lean_box(0);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___x_3964_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3975_, lean_object* v_opts_3976_, lean_object* v_declName_3977_){
_start:
{
uint8_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = 0;
lean_inc(v_declName_3977_);
lean_inc_ref(v_env_3975_);
v___x_3981_ = l_Lean_Environment_find_x3f(v_env_3975_, v_declName_3977_, v___x_3980_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
lean_dec_ref(v_env_3975_);
v___x_3982_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3983_ = 1;
v___x_3984_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3977_, v___x_3983_);
v___x_3985_ = lean_string_append(v___x_3982_, v___x_3984_);
lean_dec_ref(v___x_3984_);
v___x_3986_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3987_ = lean_string_append(v___x_3985_, v___x_3986_);
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
return v___x_3988_;
}
else
{
lean_object* v_val_3989_; lean_object* v___x_3990_; 
v_val_3989_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_val_3989_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3990_ = l_Lean_ConstantInfo_type(v_val_3989_);
lean_dec(v_val_3989_);
if (lean_obj_tag(v___x_3990_) == 4)
{
lean_object* v_declName_3991_; 
v_declName_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_declName_3991_);
lean_dec_ref_known(v___x_3990_, 2);
if (lean_obj_tag(v_declName_3991_) == 1)
{
lean_object* v_pre_3992_; 
v_pre_3992_ = lean_ctor_get(v_declName_3991_, 0);
lean_inc(v_pre_3992_);
if (lean_obj_tag(v_pre_3992_) == 1)
{
lean_object* v_pre_3993_; 
v_pre_3993_ = lean_ctor_get(v_pre_3992_, 0);
if (lean_obj_tag(v_pre_3993_) == 0)
{
lean_object* v_str_3994_; lean_object* v_str_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; 
v_str_3994_ = lean_ctor_get(v_declName_3991_, 1);
lean_inc_ref(v_str_3994_);
lean_dec_ref_known(v_declName_3991_, 2);
v_str_3995_ = lean_ctor_get(v_pre_3992_, 1);
lean_inc_ref(v_str_3995_);
lean_dec_ref_known(v_pre_3992_, 2);
v___x_3996_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3997_ = lean_string_dec_eq(v_str_3995_, v___x_3996_);
lean_dec_ref(v_str_3995_);
if (v___x_3997_ == 0)
{
lean_dec_ref(v_str_3994_);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
else
{
lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3998_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3999_ = lean_string_dec_eq(v_str_3994_, v___x_3998_);
lean_dec_ref(v_str_3994_);
if (v___x_3999_ == 0)
{
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
else
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Lean_Environment_evalConst___redArg(v_env_3975_, v_opts_3976_, v_declName_3977_, v___x_3999_);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
return v___x_4000_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3992_, 2);
lean_dec_ref_known(v_declName_3991_, 2);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
}
else
{
lean_dec(v_pre_3992_);
lean_dec_ref_known(v_declName_3991_, 2);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
}
else
{
lean_dec(v_declName_3991_);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
}
else
{
lean_dec_ref(v___x_3990_);
lean_dec(v_declName_3977_);
lean_dec_ref(v_env_3975_);
goto v___jp_3978_;
}
}
v___jp_3978_:
{
lean_object* v___x_3979_; 
v___x_3979_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4001_, lean_object* v_opts_4002_, lean_object* v_declName_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4001_, v_opts_4002_, v_declName_4003_);
lean_dec_ref(v_opts_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4005_, size_t v_i_4006_, size_t v_stop_4007_, lean_object* v_b_4008_){
_start:
{
uint8_t v___x_4010_; 
v___x_4010_ = lean_usize_dec_eq(v_i_4006_, v_stop_4007_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_array_uget_borrowed(v_as_4005_, v_i_4006_);
lean_inc(v___x_4011_);
v___x_4012_ = l_Lean_mkAttributeImplOfEntry(v___x_4011_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_toAttributeImplCore_4014_; lean_object* v_name_4015_; lean_object* v___x_4016_; size_t v___x_4017_; size_t v___x_4018_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v_toAttributeImplCore_4014_ = lean_ctor_get(v_a_4013_, 0);
v_name_4015_ = lean_ctor_get(v_toAttributeImplCore_4014_, 1);
lean_inc(v_name_4015_);
v___x_4016_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4008_, v_name_4015_, v_a_4013_);
v___x_4017_ = ((size_t)1ULL);
v___x_4018_ = lean_usize_add(v_i_4006_, v___x_4017_);
v_i_4006_ = v___x_4018_;
v_b_4008_ = v___x_4016_;
goto _start;
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v_b_4008_);
v_a_4020_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4012_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4012_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
else
{
lean_object* v___x_4028_; 
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v_b_4008_);
return v___x_4028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4029_, lean_object* v_i_4030_, lean_object* v_stop_4031_, lean_object* v_b_4032_, lean_object* v___y_4033_){
_start:
{
size_t v_i_boxed_4034_; size_t v_stop_boxed_4035_; lean_object* v_res_4036_; 
v_i_boxed_4034_ = lean_unbox_usize(v_i_4030_);
lean_dec(v_i_4030_);
v_stop_boxed_4035_ = lean_unbox_usize(v_stop_4031_);
lean_dec(v_stop_4031_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4029_, v_i_boxed_4034_, v_stop_boxed_4035_, v_b_4032_);
lean_dec_ref(v_as_4029_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4037_, size_t v_i_4038_, size_t v_stop_4039_, lean_object* v_b_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_a_4044_; lean_object* v___y_4049_; uint8_t v___x_4051_; 
v___x_4051_ = lean_usize_dec_eq(v_i_4038_, v_stop_4039_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4052_ = lean_array_uget_borrowed(v_as_4037_, v_i_4038_);
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = lean_array_get_size(v___x_4052_);
v___x_4055_ = lean_nat_dec_lt(v___x_4053_, v___x_4054_);
if (v___x_4055_ == 0)
{
v_a_4044_ = v_b_4040_;
goto v___jp_4043_;
}
else
{
uint8_t v___x_4056_; 
v___x_4056_ = lean_nat_dec_le(v___x_4054_, v___x_4054_);
if (v___x_4056_ == 0)
{
if (v___x_4055_ == 0)
{
v_a_4044_ = v_b_4040_;
goto v___jp_4043_;
}
else
{
size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = lean_usize_of_nat(v___x_4054_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4052_, v___x_4057_, v___x_4058_, v_b_4040_);
v___y_4049_ = v___x_4059_;
goto v___jp_4048_;
}
}
else
{
size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = ((size_t)0ULL);
v___x_4061_ = lean_usize_of_nat(v___x_4054_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4052_, v___x_4060_, v___x_4061_, v_b_4040_);
v___y_4049_ = v___x_4062_;
goto v___jp_4048_;
}
}
}
else
{
lean_object* v___x_4063_; 
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_b_4040_);
return v___x_4063_;
}
v___jp_4043_:
{
size_t v___x_4045_; size_t v___x_4046_; 
v___x_4045_ = ((size_t)1ULL);
v___x_4046_ = lean_usize_add(v_i_4038_, v___x_4045_);
v_i_4038_ = v___x_4046_;
v_b_4040_ = v_a_4044_;
goto _start;
}
v___jp_4048_:
{
if (lean_obj_tag(v___y_4049_) == 0)
{
lean_object* v_a_4050_; 
v_a_4050_ = lean_ctor_get(v___y_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___y_4049_, 1);
v_a_4044_ = v_a_4050_;
goto v___jp_4043_;
}
else
{
return v___y_4049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4064_, lean_object* v_i_4065_, lean_object* v_stop_4066_, lean_object* v_b_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
size_t v_i_boxed_4070_; size_t v_stop_boxed_4071_; lean_object* v_res_4072_; 
v_i_boxed_4070_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_stop_boxed_4071_ = lean_unbox_usize(v_stop_4066_);
lean_dec(v_stop_4066_);
v_res_4072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4064_, v_i_boxed_4070_, v_stop_boxed_4071_, v_b_4067_, v___y_4068_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v_as_4064_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4073_, lean_object* v_a_4074_){
_start:
{
lean_object* v_a_4077_; lean_object* v___y_4082_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4092_ = l_Lean_attributeMapRef;
v___x_4093_ = lean_st_ref_get(v___x_4092_);
v___x_4094_ = lean_unsigned_to_nat(0u);
v___x_4095_ = lean_array_get_size(v_es_4073_);
v___x_4096_ = lean_nat_dec_lt(v___x_4094_, v___x_4095_);
if (v___x_4096_ == 0)
{
v_a_4077_ = v___x_4093_;
goto v___jp_4076_;
}
else
{
uint8_t v___x_4097_; 
v___x_4097_ = lean_nat_dec_le(v___x_4095_, v___x_4095_);
if (v___x_4097_ == 0)
{
if (v___x_4096_ == 0)
{
v_a_4077_ = v___x_4093_;
goto v___jp_4076_;
}
else
{
size_t v___x_4098_; size_t v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = ((size_t)0ULL);
v___x_4099_ = lean_usize_of_nat(v___x_4095_);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4073_, v___x_4098_, v___x_4099_, v___x_4093_, v_a_4074_);
v___y_4082_ = v___x_4100_;
goto v___jp_4081_;
}
}
else
{
size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = ((size_t)0ULL);
v___x_4102_ = lean_usize_of_nat(v___x_4095_);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4073_, v___x_4101_, v___x_4102_, v___x_4093_, v_a_4074_);
v___y_4082_ = v___x_4103_;
goto v___jp_4081_;
}
}
v___jp_4076_:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = lean_box(0);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
lean_ctor_set(v___x_4079_, 1, v_a_4077_);
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
return v___x_4080_;
}
v___jp_4081_:
{
if (lean_obj_tag(v___y_4082_) == 0)
{
lean_object* v_a_4083_; 
v_a_4083_ = lean_ctor_get(v___y_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___y_4082_, 1);
v_a_4077_ = v_a_4083_;
goto v___jp_4076_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v___y_4082_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___y_4082_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___y_4082_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___y_4082_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4104_, v_a_4105_);
lean_dec_ref(v_a_4105_);
lean_dec_ref(v_es_4104_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4108_, size_t v_i_4109_, size_t v_stop_4110_, lean_object* v_b_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4108_, v_i_4109_, v_stop_4110_, v_b_4111_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4115_, lean_object* v_i_4116_, lean_object* v_stop_4117_, lean_object* v_b_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
size_t v_i_boxed_4121_; size_t v_stop_boxed_4122_; lean_object* v_res_4123_; 
v_i_boxed_4121_ = lean_unbox_usize(v_i_4116_);
lean_dec(v_i_4116_);
v_stop_boxed_4122_ = lean_unbox_usize(v_stop_4117_);
lean_dec(v_stop_4117_);
v_res_4123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4115_, v_i_boxed_4121_, v_stop_boxed_4122_, v_b_4118_, v___y_4119_);
lean_dec_ref(v___y_4119_);
lean_dec_ref(v_as_4115_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4124_, lean_object* v_e_4125_){
_start:
{
lean_object* v_snd_4126_; lean_object* v_toAttributeImplCore_4127_; lean_object* v_fst_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4146_; 
v_snd_4126_ = lean_ctor_get(v_e_4125_, 1);
lean_inc(v_snd_4126_);
v_toAttributeImplCore_4127_ = lean_ctor_get(v_snd_4126_, 0);
v_fst_4128_ = lean_ctor_get(v_e_4125_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_e_4125_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_e_4125_, 1);
lean_dec(v_unused_4147_);
v___x_4130_ = v_e_4125_;
v_isShared_4131_ = v_isSharedCheck_4146_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_fst_4128_);
lean_dec(v_e_4125_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4146_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v_newEntries_4132_; lean_object* v_map_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4145_; 
v_newEntries_4132_ = lean_ctor_get(v_s_4124_, 0);
v_map_4133_ = lean_ctor_get(v_s_4124_, 1);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_s_4124_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4135_ = v_s_4124_;
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_map_4133_);
lean_inc(v_newEntries_4132_);
lean_dec(v_s_4124_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v_name_4137_; lean_object* v___x_4139_; 
v_name_4137_ = lean_ctor_get(v_toAttributeImplCore_4127_, 1);
lean_inc(v_name_4137_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 1);
lean_ctor_set(v___x_4130_, 1, v_newEntries_4132_);
v___x_4139_ = v___x_4130_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_fst_4128_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v_newEntries_4132_);
v___x_4139_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
v___x_4140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4133_, v_name_4137_, v_snd_4126_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 1, v___x_4140_);
lean_ctor_set(v___x_4135_, 0, v___x_4139_);
v___x_4142_ = v___x_4135_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4148_, lean_object* v_s_4149_){
_start:
{
lean_object* v_newEntries_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v_newEntries_4150_ = lean_ctor_get(v_s_4149_, 0);
lean_inc(v_newEntries_4150_);
lean_dec_ref(v_s_4149_);
v___x_4151_ = l_List_reverse___redArg(v_newEntries_4150_);
v___x_4152_ = lean_array_mk(v___x_4151_);
lean_inc_ref_n(v___x_4152_, 2);
v___x_4153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
lean_ctor_set(v___x_4153_, 2, v___x_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4154_, lean_object* v_s_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4154_, v_s_4155_);
lean_dec_ref(v_x_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4157_){
_start:
{
lean_object* v_newEntries_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4169_; 
v_newEntries_4158_ = lean_ctor_get(v_s_4157_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_s_4157_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v_s_4157_, 1);
lean_dec(v_unused_4170_);
v___x_4160_ = v_s_4157_;
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_newEntries_4158_);
lean_dec(v_s_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4169_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4162_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4163_ = l_List_lengthTR___redArg(v_newEntries_4158_);
lean_dec(v_newEntries_4158_);
v___x_4164_ = l_Nat_reprFast(v___x_4163_);
v___x_4165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 5);
lean_ctor_set(v___x_4160_, 1, v___x_4165_);
lean_ctor_set(v___x_4160_, 0, v___x_4162_);
v___x_4167_ = v___x_4160_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4162_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4171_){
_start:
{
lean_object* v_newEntries_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_newEntries_4172_ = lean_ctor_get(v_s_4171_, 0);
lean_inc(v_newEntries_4172_);
lean_dec_ref(v_s_4171_);
v___x_4173_ = l_List_reverse___redArg(v_newEntries_4172_);
v___x_4174_ = lean_array_mk(v___x_4173_);
return v___x_4174_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___f_4186_; lean_object* v___f_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4184_ = lean_box(0);
v___x_4185_ = lean_box(2);
v___f_4186_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4187_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4188_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4190_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4191_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4192_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___x_4190_);
lean_ctor_set(v___x_4192_, 2, v___x_4189_);
lean_ctor_set(v___x_4192_, 3, v___x_4188_);
lean_ctor_set(v___x_4192_, 4, v___f_4187_);
lean_ctor_set(v___x_4192_, 5, v___f_4186_);
lean_ctor_set(v___x_4192_, 6, v___x_4185_);
lean_ctor_set(v___x_4192_, 7, v___x_4184_);
return v___x_4192_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___f_4193_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4194_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___f_4193_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4198_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4197_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4203_ = l_Lean_attributeMapRef;
v___x_4204_ = lean_st_ref_get(v___x_4203_);
v___x_4205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4204_, v_n_4201_);
lean_dec(v___x_4204_);
v___x_4206_ = lean_box(v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_isBuiltinAttribute(v_n_4208_);
lean_dec(v_n_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4211_, lean_object* v_x_4212_){
_start:
{
if (lean_obj_tag(v_x_4212_) == 0)
{
return v_x_4211_;
}
else
{
lean_object* v_key_4213_; lean_object* v_tail_4214_; lean_object* v___x_4215_; 
v_key_4213_ = lean_ctor_get(v_x_4212_, 0);
v_tail_4214_ = lean_ctor_get(v_x_4212_, 2);
lean_inc(v_key_4213_);
v___x_4215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4215_, 0, v_key_4213_);
lean_ctor_set(v___x_4215_, 1, v_x_4211_);
v_x_4211_ = v___x_4215_;
v_x_4212_ = v_tail_4214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4217_, lean_object* v_x_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4217_, v_x_4218_);
lean_dec(v_x_4218_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4220_, size_t v_i_4221_, size_t v_stop_4222_, lean_object* v_b_4223_){
_start:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_usize_dec_eq(v_i_4221_, v_stop_4222_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; size_t v___x_4227_; size_t v___x_4228_; 
v___x_4225_ = lean_array_uget_borrowed(v_as_4220_, v_i_4221_);
v___x_4226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4223_, v___x_4225_);
v___x_4227_ = ((size_t)1ULL);
v___x_4228_ = lean_usize_add(v_i_4221_, v___x_4227_);
v_i_4221_ = v___x_4228_;
v_b_4223_ = v___x_4226_;
goto _start;
}
else
{
return v_b_4223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_stop_4232_, lean_object* v_b_4233_){
_start:
{
size_t v_i_boxed_4234_; size_t v_stop_boxed_4235_; lean_object* v_res_4236_; 
v_i_boxed_4234_ = lean_unbox_usize(v_i_4231_);
lean_dec(v_i_4231_);
v_stop_boxed_4235_ = lean_unbox_usize(v_stop_4232_);
lean_dec(v_stop_4232_);
v_res_4236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4230_, v_i_boxed_4234_, v_stop_boxed_4235_, v_b_4233_);
lean_dec_ref(v_as_4230_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v_buckets_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
v___x_4238_ = l_Lean_attributeMapRef;
v___x_4239_ = lean_st_ref_get(v___x_4238_);
v_buckets_4240_ = lean_ctor_get(v___x_4239_, 1);
lean_inc_ref(v_buckets_4240_);
lean_dec(v___x_4239_);
v___x_4241_ = lean_box(0);
v___x_4242_ = lean_unsigned_to_nat(0u);
v___x_4243_ = lean_array_get_size(v_buckets_4240_);
v___x_4244_ = lean_nat_dec_lt(v___x_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref(v_buckets_4240_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4241_);
return v___x_4245_;
}
else
{
uint8_t v___x_4246_; 
v___x_4246_ = lean_nat_dec_le(v___x_4243_, v___x_4243_);
if (v___x_4246_ == 0)
{
if (v___x_4244_ == 0)
{
lean_object* v___x_4247_; 
lean_dec_ref(v_buckets_4240_);
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4241_);
return v___x_4247_;
}
else
{
size_t v___x_4248_; size_t v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v___x_4248_ = ((size_t)0ULL);
v___x_4249_ = lean_usize_of_nat(v___x_4243_);
v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4240_, v___x_4248_, v___x_4249_, v___x_4241_);
lean_dec_ref(v_buckets_4240_);
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
return v___x_4251_;
}
}
else
{
size_t v___x_4252_; size_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4252_ = ((size_t)0ULL);
v___x_4253_ = lean_usize_of_nat(v___x_4243_);
v___x_4254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4240_, v___x_4252_, v___x_4253_, v___x_4241_);
lean_dec_ref(v_buckets_4240_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
return v___x_4255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_getBuiltinAttributeNames();
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4261_ = l_Lean_attributeMapRef;
v___x_4262_ = lean_st_ref_get(v___x_4261_);
v___x_4263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4262_, v_attrName_4259_);
lean_dec(v___x_4262_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v___x_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4264_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4265_ = 1;
v___x_4266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4259_, v___x_4265_);
v___x_4267_ = lean_string_append(v___x_4264_, v___x_4266_);
lean_dec_ref(v___x_4266_);
v___x_4268_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4269_ = lean_string_append(v___x_4267_, v___x_4268_);
v___x_4270_ = lean_mk_io_user_error(v___x_4269_);
v___x_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
return v___x_4271_;
}
else
{
lean_object* v_val_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_attrName_4259_);
v_val_4272_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4263_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_val_4272_);
lean_dec(v___x_4263_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set_tag(v___x_4274_, 0);
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_val_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4280_);
return v_res_4282_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4283_, lean_object* v_attrName_4284_){
_start:
{
lean_object* v___x_4285_; lean_object* v_toEnvExtension_4286_; lean_object* v_asyncMode_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v_map_4291_; uint8_t v___x_4292_; 
v___x_4285_ = l_Lean_attributeExtension;
v_toEnvExtension_4286_ = lean_ctor_get(v___x_4285_, 0);
v_asyncMode_4287_ = lean_ctor_get(v_toEnvExtension_4286_, 2);
v___x_4288_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4289_ = lean_box(0);
v___x_4290_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4288_, v___x_4285_, v_env_4283_, v_asyncMode_4287_, v___x_4289_);
v_map_4291_ = lean_ctor_get(v___x_4290_, 1);
lean_inc_ref(v_map_4291_);
lean_dec(v___x_4290_);
v___x_4292_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4291_, v_attrName_4284_);
lean_dec_ref(v_map_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4293_, lean_object* v_attrName_4294_){
_start:
{
uint8_t v_res_4295_; lean_object* v_r_4296_; 
v_res_4295_ = l_Lean_isAttribute(v_env_4293_, v_attrName_4294_);
lean_dec(v_attrName_4294_);
v_r_4296_ = lean_box(v_res_4295_);
return v_r_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4297_){
_start:
{
lean_object* v___x_4298_; lean_object* v_toEnvExtension_4299_; lean_object* v_asyncMode_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v_map_4304_; lean_object* v_buckets_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4298_ = l_Lean_attributeExtension;
v_toEnvExtension_4299_ = lean_ctor_get(v___x_4298_, 0);
v_asyncMode_4300_ = lean_ctor_get(v_toEnvExtension_4299_, 2);
v___x_4301_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4302_ = lean_box(0);
v___x_4303_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4301_, v___x_4298_, v_env_4297_, v_asyncMode_4300_, v___x_4302_);
v_map_4304_ = lean_ctor_get(v___x_4303_, 1);
lean_inc_ref(v_map_4304_);
lean_dec(v___x_4303_);
v_buckets_4305_ = lean_ctor_get(v_map_4304_, 1);
lean_inc_ref(v_buckets_4305_);
lean_dec_ref(v_map_4304_);
v___x_4306_ = lean_box(0);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = lean_array_get_size(v_buckets_4305_);
v___x_4309_ = lean_nat_dec_lt(v___x_4307_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_dec_ref(v_buckets_4305_);
return v___x_4306_;
}
else
{
uint8_t v___x_4310_; 
v___x_4310_ = lean_nat_dec_le(v___x_4308_, v___x_4308_);
if (v___x_4310_ == 0)
{
if (v___x_4309_ == 0)
{
lean_dec_ref(v_buckets_4305_);
return v___x_4306_;
}
else
{
size_t v___x_4311_; size_t v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = ((size_t)0ULL);
v___x_4312_ = lean_usize_of_nat(v___x_4308_);
v___x_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4305_, v___x_4311_, v___x_4312_, v___x_4306_);
lean_dec_ref(v_buckets_4305_);
return v___x_4313_;
}
}
else
{
size_t v___x_4314_; size_t v___x_4315_; lean_object* v___x_4316_; 
v___x_4314_ = ((size_t)0ULL);
v___x_4315_ = lean_usize_of_nat(v___x_4308_);
v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4305_, v___x_4314_, v___x_4315_, v___x_4306_);
lean_dec_ref(v_buckets_4305_);
return v___x_4316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4317_, lean_object* v_attrName_4318_){
_start:
{
lean_object* v___x_4319_; lean_object* v_toEnvExtension_4320_; lean_object* v_asyncMode_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v_map_4325_; lean_object* v___x_4326_; 
v___x_4319_ = l_Lean_attributeExtension;
v_toEnvExtension_4320_ = lean_ctor_get(v___x_4319_, 0);
v_asyncMode_4321_ = lean_ctor_get(v_toEnvExtension_4320_, 2);
v___x_4322_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4323_ = lean_box(0);
v___x_4324_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4322_, v___x_4319_, v_env_4317_, v_asyncMode_4321_, v___x_4323_);
v_map_4325_ = lean_ctor_get(v___x_4324_, 1);
lean_inc_ref(v_map_4325_);
lean_dec(v___x_4324_);
v___x_4326_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4325_, v_attrName_4318_);
lean_dec_ref(v_map_4325_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v___x_4327_; uint8_t v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4327_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4328_ = 1;
v___x_4329_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4318_, v___x_4328_);
v___x_4330_ = lean_string_append(v___x_4327_, v___x_4329_);
lean_dec_ref(v___x_4329_);
v___x_4331_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4332_ = lean_string_append(v___x_4330_, v___x_4331_);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
return v___x_4333_;
}
else
{
lean_object* v_val_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_attrName_4318_);
v_val_4334_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4326_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_val_4334_);
lean_dec(v___x_4326_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_val_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4342_, lean_object* v_builderId_4343_, lean_object* v_ref_4344_, lean_object* v_args_4345_){
_start:
{
lean_object* v_entry_4347_; lean_object* v___x_4348_; 
v_entry_4347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4347_, 0, v_builderId_4343_);
lean_ctor_set(v_entry_4347_, 1, v_ref_4344_);
lean_ctor_set(v_entry_4347_, 2, v_args_4345_);
lean_inc_ref(v_entry_4347_);
v___x_4348_ = l_Lean_mkAttributeImplOfEntry(v_entry_4347_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4374_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4351_ = v___x_4348_;
v_isShared_4352_ = v_isSharedCheck_4374_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4348_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4374_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v_toAttributeImplCore_4353_; lean_object* v_name_4354_; uint8_t v___x_4355_; 
v_toAttributeImplCore_4353_ = lean_ctor_get(v_a_4349_, 0);
v_name_4354_ = lean_ctor_get(v_toAttributeImplCore_4353_, 1);
lean_inc_ref(v_env_4342_);
v___x_4355_ = l_Lean_isAttribute(v_env_4342_, v_name_4354_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; lean_object* v_toEnvExtension_4357_; lean_object* v_asyncMode_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4356_ = l_Lean_attributeExtension;
v_toEnvExtension_4357_ = lean_ctor_get(v___x_4356_, 0);
v_asyncMode_4358_ = lean_ctor_get(v_toEnvExtension_4357_, 2);
v___x_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4359_, 0, v_entry_4347_);
lean_ctor_set(v___x_4359_, 1, v_a_4349_);
v___x_4360_ = lean_box(0);
v___x_4361_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4356_, v_env_4342_, v___x_4359_, v_asyncMode_4358_, v___x_4360_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v___x_4361_);
v___x_4363_ = v___x_4351_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
lean_inc(v_name_4354_);
lean_dec(v_a_4349_);
lean_dec_ref_known(v_entry_4347_, 3);
lean_dec_ref(v_env_4342_);
v___x_4365_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4354_, v___x_4355_);
v___x_4367_ = lean_string_append(v___x_4365_, v___x_4366_);
lean_dec_ref(v___x_4366_);
v___x_4368_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4369_ = lean_string_append(v___x_4367_, v___x_4368_);
v___x_4370_ = lean_mk_io_user_error(v___x_4369_);
if (v_isShared_4352_ == 0)
{
lean_ctor_set_tag(v___x_4351_, 1);
lean_ctor_set(v___x_4351_, 0, v___x_4370_);
v___x_4372_ = v___x_4351_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec_ref_known(v_entry_4347_, 3);
lean_dec_ref(v_env_4342_);
v_a_4375_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4348_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4348_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4383_, lean_object* v_builderId_4384_, lean_object* v_ref_4385_, lean_object* v_args_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_registerAttributeOfBuilder(v_env_4383_, v_builderId_4384_, v_ref_4385_, v_args_4386_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
if (lean_obj_tag(v_x_4389_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v_a_4393_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v_x_4389_, 1);
v___x_4394_ = l_Lean_stringToMessageData(v_a_4393_);
v___x_4395_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4394_, v___y_4390_, v___y_4391_);
return v___x_4395_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
v_a_4396_ = lean_ctor_get(v_x_4389_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_x_4389_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v_x_4389_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v_x_4389_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
lean_ctor_set_tag(v___x_4398_, 0);
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4409_, lean_object* v_attrName_4410_, lean_object* v_stx_4411_, uint8_t v_kind_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___x_4416_; lean_object* v_env_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4416_ = lean_st_ref_get(v_a_4414_);
v_env_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc_ref(v_env_4417_);
lean_dec(v___x_4416_);
v___x_4418_ = l_Lean_getAttributeImpl(v_env_4417_, v_attrName_4410_);
v___x_4419_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4418_, v_a_4413_, v_a_4414_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v_add_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v_add_4421_ = lean_ctor_get(v_a_4420_, 1);
lean_inc_ref(v_add_4421_);
lean_dec(v_a_4420_);
v___x_4422_ = lean_box(v_kind_4412_);
lean_inc(v_a_4414_);
lean_inc_ref(v_a_4413_);
v___x_4423_ = lean_apply_6(v_add_4421_, v_declName_4409_, v_stx_4411_, v___x_4422_, v_a_4413_, v_a_4414_, lean_box(0));
return v___x_4423_;
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_stx_4411_);
lean_dec(v_declName_4409_);
v_a_4424_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4419_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4419_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4432_, lean_object* v_attrName_4433_, lean_object* v_stx_4434_, lean_object* v_kind_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
uint8_t v_kind_boxed_4439_; lean_object* v_res_4440_; 
v_kind_boxed_4439_ = lean_unbox(v_kind_4435_);
v_res_4440_ = l_Lean_Attribute_add(v_declName_4432_, v_attrName_4433_, v_stx_4434_, v_kind_boxed_4439_, v_a_4436_, v_a_4437_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4441_, lean_object* v_x_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4442_, v___y_4443_, v___y_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4447_, lean_object* v_x_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4447_, v_x_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4453_, lean_object* v_attrName_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v___x_4458_; lean_object* v_env_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4458_ = lean_st_ref_get(v_a_4456_);
v_env_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc_ref(v_env_4459_);
lean_dec(v___x_4458_);
v___x_4460_ = l_Lean_getAttributeImpl(v_env_4459_, v_attrName_4454_);
v___x_4461_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4460_, v_a_4455_, v_a_4456_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; lean_object* v_erase_4463_; lean_object* v___x_4464_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
v_erase_4463_ = lean_ctor_get(v_a_4462_, 2);
lean_inc_ref(v_erase_4463_);
lean_dec(v_a_4462_);
lean_inc(v_a_4456_);
lean_inc_ref(v_a_4455_);
v___x_4464_ = lean_apply_4(v_erase_4463_, v_declName_4453_, v_a_4455_, v_a_4456_, lean_box(0));
return v___x_4464_;
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_dec(v_declName_4453_);
v_a_4465_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4461_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4461_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4473_, lean_object* v_attrName_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l_Lean_Attribute_erase(v_declName_4473_, v_attrName_4474_, v_a_4475_, v_a_4476_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4479_, lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4480_) == 0)
{
return v_x_4479_;
}
else
{
lean_object* v_key_4481_; lean_object* v_value_4482_; lean_object* v_tail_4483_; lean_object* v_newEntries_4484_; lean_object* v_map_4485_; uint8_t v___x_4486_; 
v_key_4481_ = lean_ctor_get(v_x_4480_, 0);
lean_inc(v_key_4481_);
v_value_4482_ = lean_ctor_get(v_x_4480_, 1);
lean_inc(v_value_4482_);
v_tail_4483_ = lean_ctor_get(v_x_4480_, 2);
lean_inc(v_tail_4483_);
lean_dec_ref_known(v_x_4480_, 3);
v_newEntries_4484_ = lean_ctor_get(v_x_4479_, 0);
v_map_4485_ = lean_ctor_get(v_x_4479_, 1);
v___x_4486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4485_, v_key_4481_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4495_; 
lean_inc_ref(v_map_4485_);
lean_inc(v_newEntries_4484_);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_x_4479_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; lean_object* v_unused_4497_; 
v_unused_4496_ = lean_ctor_get(v_x_4479_, 1);
lean_dec(v_unused_4496_);
v_unused_4497_ = lean_ctor_get(v_x_4479_, 0);
lean_dec(v_unused_4497_);
v___x_4488_ = v_x_4479_;
v_isShared_4489_ = v_isSharedCheck_4495_;
goto v_resetjp_4487_;
}
else
{
lean_dec(v_x_4479_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4495_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4490_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4485_, v_key_4481_, v_value_4482_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 1, v___x_4490_);
v___x_4492_ = v___x_4488_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_newEntries_4484_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
v_x_4479_ = v___x_4492_;
v_x_4480_ = v_tail_4483_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4482_);
lean_dec(v_key_4481_);
v_x_4480_ = v_tail_4483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4499_, size_t v_i_4500_, size_t v_stop_4501_, lean_object* v_b_4502_){
_start:
{
uint8_t v___x_4503_; 
v___x_4503_ = lean_usize_dec_eq(v_i_4500_, v_stop_4501_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; lean_object* v___x_4505_; size_t v___x_4506_; size_t v___x_4507_; 
v___x_4504_ = lean_array_uget_borrowed(v_as_4499_, v_i_4500_);
lean_inc(v___x_4504_);
v___x_4505_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4502_, v___x_4504_);
v___x_4506_ = ((size_t)1ULL);
v___x_4507_ = lean_usize_add(v_i_4500_, v___x_4506_);
v_i_4500_ = v___x_4507_;
v_b_4502_ = v___x_4505_;
goto _start;
}
else
{
return v_b_4502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4509_, lean_object* v_i_4510_, lean_object* v_stop_4511_, lean_object* v_b_4512_){
_start:
{
size_t v_i_boxed_4513_; size_t v_stop_boxed_4514_; lean_object* v_res_4515_; 
v_i_boxed_4513_ = lean_unbox_usize(v_i_4510_);
lean_dec(v_i_4510_);
v_stop_boxed_4514_ = lean_unbox_usize(v_stop_4511_);
lean_dec(v_stop_4511_);
v_res_4515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4509_, v_i_boxed_4513_, v_stop_boxed_4514_, v_b_4512_);
lean_dec_ref(v_as_4509_);
return v_res_4515_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4516_){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___y_4522_; lean_object* v_toEnvExtension_4525_; lean_object* v_asyncMode_4526_; lean_object* v_buckets_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; 
v___x_4518_ = l_Lean_attributeMapRef;
v___x_4519_ = lean_st_ref_get(v___x_4518_);
v___x_4520_ = l_Lean_attributeExtension;
v_toEnvExtension_4525_ = lean_ctor_get(v___x_4520_, 0);
v_asyncMode_4526_ = lean_ctor_get(v_toEnvExtension_4525_, 2);
v_buckets_4527_ = lean_ctor_get(v___x_4519_, 1);
lean_inc_ref(v_buckets_4527_);
lean_dec(v___x_4519_);
v___x_4528_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4529_ = lean_box(0);
lean_inc_ref(v_env_4516_);
v___x_4530_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4528_, v___x_4520_, v_env_4516_, v_asyncMode_4526_, v___x_4529_);
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = lean_array_get_size(v_buckets_4527_);
v___x_4533_ = lean_nat_dec_lt(v___x_4531_, v___x_4532_);
if (v___x_4533_ == 0)
{
lean_dec_ref(v_buckets_4527_);
v___y_4522_ = v___x_4530_;
goto v___jp_4521_;
}
else
{
uint8_t v___x_4534_; 
v___x_4534_ = lean_nat_dec_le(v___x_4532_, v___x_4532_);
if (v___x_4534_ == 0)
{
if (v___x_4533_ == 0)
{
lean_dec_ref(v_buckets_4527_);
v___y_4522_ = v___x_4530_;
goto v___jp_4521_;
}
else
{
size_t v___x_4535_; size_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = ((size_t)0ULL);
v___x_4536_ = lean_usize_of_nat(v___x_4532_);
v___x_4537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4527_, v___x_4535_, v___x_4536_, v___x_4530_);
lean_dec_ref(v_buckets_4527_);
v___y_4522_ = v___x_4537_;
goto v___jp_4521_;
}
}
else
{
size_t v___x_4538_; size_t v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = ((size_t)0ULL);
v___x_4539_ = lean_usize_of_nat(v___x_4532_);
v___x_4540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4527_, v___x_4538_, v___x_4539_, v___x_4530_);
lean_dec_ref(v_buckets_4527_);
v___y_4522_ = v___x_4540_;
goto v___jp_4521_;
}
}
v___jp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4520_, v_env_4516_, v___y_4522_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
return v___x_4524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = lean_update_env_attributes(v_env_4541_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v_size_4547_; lean_object* v___x_4548_; 
v___x_4545_ = l_Lean_attributeMapRef;
v___x_4546_ = lean_st_ref_get(v___x_4545_);
v_size_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc(v_size_4547_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_size_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = lean_get_num_attributes();
return v_res_4550_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedAttributeApplicationTime_default = _init_l_Lean_instInhabitedAttributeApplicationTime_default();
l_Lean_instInhabitedAttributeApplicationTime = _init_l_Lean_instInhabitedAttributeApplicationTime();
l_Lean_instInhabitedAttributeKind_default = _init_l_Lean_instInhabitedAttributeKind_default();
l_Lean_instInhabitedAttributeKind = _init_l_Lean_instInhabitedAttributeKind();
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeMapRef);
lean_dec_ref(res);
l_Lean_instInhabitedTagAttribute_default = _init_l_Lean_instInhabitedTagAttribute_default();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute_default);
l_Lean_instInhabitedTagAttribute = _init_l_Lean_instInhabitedTagAttribute();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeImplBuilderTableRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeImplBuilderTableRef);
lean_dec_ref(res);
l_Lean_instInhabitedAttributeExtensionState_default = _init_l_Lean_instInhabitedAttributeExtensionState_default();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState_default);
l_Lean_instInhabitedAttributeExtensionState = _init_l_Lean_instInhabitedAttributeExtensionState();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState);
res = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_AttributeImplCore_ref___autoParam = _init_l_Lean_AttributeImplCore_ref___autoParam();
lean_mark_persistent(l_Lean_AttributeImplCore_ref___autoParam);
l_Lean_registerTagAttribute___auto__1 = _init_l_Lean_registerTagAttribute___auto__1();
lean_mark_persistent(l_Lean_registerTagAttribute___auto__1);
l_Lean_registerEnumAttributes___auto__1 = _init_l_Lean_registerEnumAttributes___auto__1();
lean_mark_persistent(l_Lean_registerEnumAttributes___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_MetaAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
