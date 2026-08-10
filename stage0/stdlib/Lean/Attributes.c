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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_buckets_440_; lean_object* v___x_441_; uint64_t v___y_443_; 
v_buckets_440_ = lean_ctor_get(v_m_438_, 1);
v___x_441_ = lean_array_get_size(v_buckets_440_);
if (lean_obj_tag(v_a_439_) == 0)
{
uint64_t v___x_457_; 
v___x_457_ = 1723ULL;
v___y_443_ = v___x_457_;
goto v___jp_442_;
}
else
{
uint64_t v_hash_458_; 
v_hash_458_ = lean_ctor_get_uint64(v_a_439_, sizeof(void*)*2);
v___y_443_ = v_hash_458_;
goto v___jp_442_;
}
v___jp_442_:
{
uint64_t v___x_444_; uint64_t v___x_445_; uint64_t v_fold_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v___x_449_; size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_444_ = 32ULL;
v___x_445_ = lean_uint64_shift_right(v___y_443_, v___x_444_);
v_fold_446_ = lean_uint64_xor(v___y_443_, v___x_445_);
v___x_447_ = 16ULL;
v___x_448_ = lean_uint64_shift_right(v_fold_446_, v___x_447_);
v___x_449_ = lean_uint64_xor(v_fold_446_, v___x_448_);
v___x_450_ = lean_uint64_to_usize(v___x_449_);
v___x_451_ = lean_usize_of_nat(v___x_441_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_sub(v___x_451_, v___x_452_);
v___x_454_ = lean_usize_land(v___x_450_, v___x_453_);
v___x_455_ = lean_array_uget_borrowed(v_buckets_440_, v___x_454_);
v___x_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_439_, v___x_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_m_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_dec(v_b_464_);
lean_dec(v_a_463_);
return v_x_465_;
}
else
{
lean_object* v_key_466_; lean_object* v_value_467_; lean_object* v_tail_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_480_; 
v_key_466_ = lean_ctor_get(v_x_465_, 0);
v_value_467_ = lean_ctor_get(v_x_465_, 1);
v_tail_468_ = lean_ctor_get(v_x_465_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_480_ == 0)
{
v___x_470_ = v_x_465_;
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_tail_468_);
lean_inc(v_value_467_);
lean_inc(v_key_466_);
lean_dec(v_x_465_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_480_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; 
v___x_472_ = lean_name_eq(v_key_466_, v_a_463_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_463_, v_b_464_, v_tail_468_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 2, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_key_466_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_value_467_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
lean_object* v___x_478_; 
lean_dec(v_value_467_);
lean_dec(v_key_466_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_b_464_);
lean_ctor_set(v___x_470_, 0, v_a_463_);
v___x_478_ = v___x_470_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_463_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_b_464_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_tail_468_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
return v_x_481_;
}
else
{
lean_object* v_key_483_; lean_object* v_value_484_; lean_object* v_tail_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_511_; 
v_key_483_ = lean_ctor_get(v_x_482_, 0);
v_value_484_ = lean_ctor_get(v_x_482_, 1);
v_tail_485_ = lean_ctor_get(v_x_482_, 2);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_511_ == 0)
{
v___x_487_ = v_x_482_;
v_isShared_488_ = v_isSharedCheck_511_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_tail_485_);
lean_inc(v_value_484_);
lean_inc(v_key_483_);
lean_dec(v_x_482_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_511_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; uint64_t v___y_491_; 
v___x_489_ = lean_array_get_size(v_x_481_);
if (lean_obj_tag(v_key_483_) == 0)
{
uint64_t v___x_509_; 
v___x_509_ = 1723ULL;
v___y_491_ = v___x_509_;
goto v___jp_490_;
}
else
{
uint64_t v_hash_510_; 
v_hash_510_ = lean_ctor_get_uint64(v_key_483_, sizeof(void*)*2);
v___y_491_ = v_hash_510_;
goto v___jp_490_;
}
v___jp_490_:
{
uint64_t v___x_492_; uint64_t v___x_493_; uint64_t v_fold_494_; uint64_t v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_492_ = 32ULL;
v___x_493_ = lean_uint64_shift_right(v___y_491_, v___x_492_);
v_fold_494_ = lean_uint64_xor(v___y_491_, v___x_493_);
v___x_495_ = 16ULL;
v___x_496_ = lean_uint64_shift_right(v_fold_494_, v___x_495_);
v___x_497_ = lean_uint64_xor(v_fold_494_, v___x_496_);
v___x_498_ = lean_uint64_to_usize(v___x_497_);
v___x_499_ = lean_usize_of_nat(v___x_489_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_sub(v___x_499_, v___x_500_);
v___x_502_ = lean_usize_land(v___x_498_, v___x_501_);
v___x_503_ = lean_array_uget_borrowed(v_x_481_, v___x_502_);
lean_inc(v___x_503_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 2, v___x_503_);
v___x_505_ = v___x_487_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_key_483_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_value_484_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v___x_503_);
v___x_505_ = v_reuseFailAlloc_508_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_array_uset(v_x_481_, v___x_502_, v___x_505_);
v_x_481_ = v___x_506_;
v_x_482_ = v_tail_485_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_512_, lean_object* v_source_513_, lean_object* v_target_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_source_513_);
v___x_516_ = lean_nat_dec_lt(v_i_512_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v_source_513_);
lean_dec(v_i_512_);
return v_target_514_;
}
else
{
lean_object* v_es_517_; lean_object* v___x_518_; lean_object* v_source_519_; lean_object* v_target_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_es_517_ = lean_array_fget(v_source_513_, v_i_512_);
v___x_518_ = lean_box(0);
v_source_519_ = lean_array_fset(v_source_513_, v_i_512_, v___x_518_);
v_target_520_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_514_, v_es_517_);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_add(v_i_512_, v___x_521_);
lean_dec(v_i_512_);
v_i_512_ = v___x_522_;
v_source_513_ = v_source_519_;
v_target_514_ = v_target_520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_nbuckets_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_525_ = lean_array_get_size(v_data_524_);
v___x_526_ = lean_unsigned_to_nat(2u);
v_nbuckets_527_ = lean_nat_mul(v___x_525_, v___x_526_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_box(0);
v___x_530_ = lean_mk_array(v_nbuckets_527_, v___x_529_);
v___x_531_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_528_, v_data_524_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_532_, lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
lean_object* v_size_535_; lean_object* v_buckets_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_582_; 
v_size_535_ = lean_ctor_get(v_m_532_, 0);
v_buckets_536_ = lean_ctor_get(v_m_532_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_m_532_);
if (v_isSharedCheck_582_ == 0)
{
v___x_538_ = v_m_532_;
v_isShared_539_ = v_isSharedCheck_582_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_buckets_536_);
lean_inc(v_size_535_);
lean_dec(v_m_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_582_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; uint64_t v___y_542_; 
v___x_540_ = lean_array_get_size(v_buckets_536_);
if (lean_obj_tag(v_a_533_) == 0)
{
uint64_t v___x_580_; 
v___x_580_ = 1723ULL;
v___y_542_ = v___x_580_;
goto v___jp_541_;
}
else
{
uint64_t v_hash_581_; 
v_hash_581_ = lean_ctor_get_uint64(v_a_533_, sizeof(void*)*2);
v___y_542_ = v_hash_581_;
goto v___jp_541_;
}
v___jp_541_:
{
uint64_t v___x_543_; uint64_t v___x_544_; uint64_t v_fold_545_; uint64_t v___x_546_; uint64_t v___x_547_; uint64_t v___x_548_; size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; lean_object* v_bkt_554_; uint8_t v___x_555_; 
v___x_543_ = 32ULL;
v___x_544_ = lean_uint64_shift_right(v___y_542_, v___x_543_);
v_fold_545_ = lean_uint64_xor(v___y_542_, v___x_544_);
v___x_546_ = 16ULL;
v___x_547_ = lean_uint64_shift_right(v_fold_545_, v___x_546_);
v___x_548_ = lean_uint64_xor(v_fold_545_, v___x_547_);
v___x_549_ = lean_uint64_to_usize(v___x_548_);
v___x_550_ = lean_usize_of_nat(v___x_540_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_sub(v___x_550_, v___x_551_);
v___x_553_ = lean_usize_land(v___x_549_, v___x_552_);
v_bkt_554_ = lean_array_uget_borrowed(v_buckets_536_, v___x_553_);
v___x_555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_533_, v_bkt_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v_size_x27_557_; lean_object* v___x_558_; lean_object* v_buckets_x27_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v_size_x27_557_ = lean_nat_add(v_size_535_, v___x_556_);
lean_dec(v_size_535_);
lean_inc(v_bkt_554_);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v_a_533_);
lean_ctor_set(v___x_558_, 1, v_b_534_);
lean_ctor_set(v___x_558_, 2, v_bkt_554_);
v_buckets_x27_559_ = lean_array_uset(v_buckets_536_, v___x_553_, v___x_558_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_nat_mul(v_size_x27_557_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(3u);
v___x_563_ = lean_nat_div(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_array_get_size(v_buckets_x27_559_);
v___x_565_ = lean_nat_dec_le(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
if (v___x_565_ == 0)
{
lean_object* v_val_566_; lean_object* v___x_568_; 
v_val_566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_559_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_val_566_);
lean_ctor_set(v___x_538_, 0, v_size_x27_557_);
v___x_568_ = v___x_538_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_val_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
lean_object* v___x_571_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_buckets_x27_559_);
lean_ctor_set(v___x_538_, 0, v_size_x27_557_);
v___x_571_ = v___x_538_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_size_x27_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_buckets_x27_559_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v___x_573_; lean_object* v_buckets_x27_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_bkt_554_);
v___x_573_ = lean_box(0);
v_buckets_x27_574_ = lean_array_uset(v_buckets_536_, v___x_553_, v___x_573_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_533_, v_b_534_, v_bkt_554_);
v___x_576_ = lean_array_uset(v_buckets_x27_574_, v___x_553_, v___x_575_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_576_);
v___x_578_ = v___x_538_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_size_535_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_585_ = lean_mk_io_user_error(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_588_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_toAttributeImplCore_592_; lean_object* v_name_593_; uint8_t v___x_594_; 
v___x_590_ = l_Lean_attributeMapRef;
v___x_591_ = lean_st_ref_get(v___x_590_);
v_toAttributeImplCore_592_ = lean_ctor_get(v_attr_588_, 0);
v_name_593_ = lean_ctor_get(v_toAttributeImplCore_592_, 1);
lean_inc(v_name_593_);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_591_, v_name_593_);
lean_dec(v___x_591_);
if (v___x_594_ == 0)
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_initializing();
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_name_593_);
lean_dec_ref(v_attr_588_);
v___x_596_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_st_ref_take(v___x_590_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_598_, v_name_593_, v_attr_588_);
v___x_600_ = lean_st_ref_set(v___x_590_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec_ref(v_attr_588_);
v___x_602_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_603_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_593_, v___x_594_);
v___x_604_ = lean_string_append(v___x_602_, v___x_603_);
lean_dec_ref(v___x_603_);
v___x_605_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
v___x_607_ = lean_mk_io_user_error(v___x_606_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_registerBuiltinAttribute(v_attr_609_);
return v_res_611_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_m_613_, lean_object* v_a_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_613_, v_a_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_616_, v_m_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_m_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_621_, lean_object* v_m_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_622_, v_a_623_, v_b_624_);
return v___x_625_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_626_, lean_object* v_a_627_, lean_object* v_x_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_627_, v_x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_630_, lean_object* v_a_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_630_, v_a_631_, v_x_632_);
lean_dec(v_x_632_);
lean_dec(v_a_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_635_, lean_object* v_data_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_638_, lean_object* v_a_639_, lean_object* v_b_640_, lean_object* v_x_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_639_, v_b_640_, v_x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_643_, lean_object* v_i_644_, lean_object* v_source_645_, lean_object* v_target_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_644_, v_source_645_, v_target_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_649_, v_x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_fileName_657_; lean_object* v_fileMap_658_; lean_object* v_options_659_; lean_object* v_currRecDepth_660_; lean_object* v_maxRecDepth_661_; lean_object* v_ref_662_; lean_object* v_currNamespace_663_; lean_object* v_openDecls_664_; lean_object* v_initHeartbeats_665_; lean_object* v_maxHeartbeats_666_; lean_object* v_quotContext_667_; lean_object* v_currMacroScope_668_; uint8_t v_diag_669_; lean_object* v_cancelTk_x3f_670_; uint8_t v_suppressElabErrors_671_; lean_object* v_inheritedTraceOptions_672_; lean_object* v_ref_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_fileName_657_ = lean_ctor_get(v___y_654_, 0);
v_fileMap_658_ = lean_ctor_get(v___y_654_, 1);
v_options_659_ = lean_ctor_get(v___y_654_, 2);
v_currRecDepth_660_ = lean_ctor_get(v___y_654_, 3);
v_maxRecDepth_661_ = lean_ctor_get(v___y_654_, 4);
v_ref_662_ = lean_ctor_get(v___y_654_, 5);
v_currNamespace_663_ = lean_ctor_get(v___y_654_, 6);
v_openDecls_664_ = lean_ctor_get(v___y_654_, 7);
v_initHeartbeats_665_ = lean_ctor_get(v___y_654_, 8);
v_maxHeartbeats_666_ = lean_ctor_get(v___y_654_, 9);
v_quotContext_667_ = lean_ctor_get(v___y_654_, 10);
v_currMacroScope_668_ = lean_ctor_get(v___y_654_, 11);
v_diag_669_ = lean_ctor_get_uint8(v___y_654_, sizeof(void*)*14);
v_cancelTk_x3f_670_ = lean_ctor_get(v___y_654_, 12);
v_suppressElabErrors_671_ = lean_ctor_get_uint8(v___y_654_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_672_ = lean_ctor_get(v___y_654_, 13);
v_ref_673_ = l_Lean_replaceRef(v_ref_652_, v_ref_662_);
lean_inc_ref(v_inheritedTraceOptions_672_);
lean_inc(v_cancelTk_x3f_670_);
lean_inc(v_currMacroScope_668_);
lean_inc(v_quotContext_667_);
lean_inc(v_maxHeartbeats_666_);
lean_inc(v_initHeartbeats_665_);
lean_inc(v_openDecls_664_);
lean_inc(v_currNamespace_663_);
lean_inc(v_maxRecDepth_661_);
lean_inc(v_currRecDepth_660_);
lean_inc_ref(v_options_659_);
lean_inc_ref(v_fileMap_658_);
lean_inc_ref(v_fileName_657_);
v___x_674_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_674_, 0, v_fileName_657_);
lean_ctor_set(v___x_674_, 1, v_fileMap_658_);
lean_ctor_set(v___x_674_, 2, v_options_659_);
lean_ctor_set(v___x_674_, 3, v_currRecDepth_660_);
lean_ctor_set(v___x_674_, 4, v_maxRecDepth_661_);
lean_ctor_set(v___x_674_, 5, v_ref_673_);
lean_ctor_set(v___x_674_, 6, v_currNamespace_663_);
lean_ctor_set(v___x_674_, 7, v_openDecls_664_);
lean_ctor_set(v___x_674_, 8, v_initHeartbeats_665_);
lean_ctor_set(v___x_674_, 9, v_maxHeartbeats_666_);
lean_ctor_set(v___x_674_, 10, v_quotContext_667_);
lean_ctor_set(v___x_674_, 11, v_currMacroScope_668_);
lean_ctor_set(v___x_674_, 12, v_cancelTk_x3f_670_);
lean_ctor_set(v___x_674_, 13, v_inheritedTraceOptions_672_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*14, v_diag_669_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*14 + 1, v_suppressElabErrors_671_);
v___x_675_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_653_, v___x_674_, v___y_655_);
lean_dec_ref_known(v___x_674_, 14);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_676_, lean_object* v_msg_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_676_, v_msg_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v_ref_676_);
return v_res_681_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; uint8_t v___y_713_; lean_object* v___x_719_; uint8_t v___x_720_; 
lean_inc(v_stx_698_);
v___x_702_ = l_Lean_Syntax_getKind(v_stx_698_);
v___x_719_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_720_ = lean_name_eq(v___x_702_, v___x_719_);
if (v___x_720_ == 0)
{
v___y_713_ = v___x_720_;
goto v___jp_712_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = l_Lean_Syntax_getArg(v_stx_698_, v___x_721_);
v___x_723_ = l_Lean_Syntax_isNone(v___x_722_);
lean_dec(v___x_722_);
v___y_713_ = v___x_723_;
goto v___jp_712_;
}
v___jp_703_:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_705_ = lean_name_eq(v___x_702_, v___x_704_);
lean_dec(v___x_702_);
if (v___x_705_ == 0)
{
if (lean_obj_tag(v_stx_698_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_709_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_698_, v___x_708_, v_a_699_, v_a_700_);
lean_dec(v_stx_698_);
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_stx_698_);
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
goto v___jp_703_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = l_Lean_Syntax_getArg(v_stx_698_, v___x_714_);
v___x_716_ = l_Lean_Syntax_isNone(v___x_715_);
lean_dec(v___x_715_);
if (v___x_716_ == 0)
{
goto v___jp_703_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v___x_702_);
lean_dec(v_stx_698_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_729_, lean_object* v_ref_730_, lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_730_, v_msg_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_736_, lean_object* v_ref_737_, lean_object* v_msg_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_736_, v_ref_737_, v_msg_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v_ref_737_);
return v_res_742_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
lean_inc(v_stx_758_);
v___x_770_ = l_Lean_Syntax_getKind(v_stx_758_);
v___x_771_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_772_ = lean_name_eq(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_774_ = lean_name_eq(v___x_770_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_776_ = lean_name_eq(v___x_770_, v___x_775_);
lean_dec(v___x_770_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_778_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_758_, v___x_777_, v_a_759_, v_a_760_);
lean_dec(v_stx_758_);
return v___x_778_;
}
else
{
goto v___jp_762_;
}
}
else
{
lean_dec(v___x_770_);
goto v___jp_762_;
}
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_dec(v___x_770_);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = l_Lean_Syntax_getArg(v_stx_758_, v___x_779_);
lean_dec(v_stx_758_);
v___x_781_ = l_Lean_Syntax_isNone(v___x_780_);
if (v___x_781_ == 0)
{
if (v___x_772_ == 0)
{
lean_dec(v___x_780_);
goto v___jp_767_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_Syntax_getArg(v___x_780_, v___x_782_);
lean_dec(v___x_780_);
v___x_784_ = l_Lean_Syntax_isIdent(v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v___x_783_);
goto v___jp_767_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
}
else
{
lean_dec(v___x_780_);
goto v___jp_767_;
}
}
v___jp_762_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = l_Lean_Syntax_getArg(v_stx_758_, v___x_763_);
lean_dec(v_stx_758_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_box(0);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_791_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
lean_inc(v_stx_795_);
v___x_799_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_795_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_813_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_813_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_813_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
if (lean_obj_tag(v_a_800_) == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_802_);
v___x_804_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_795_);
v___x_805_ = l_Lean_MessageData_ofSyntax(v_stx_795_);
v___x_806_ = l_Lean_indentD(v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_795_, v___x_807_, v_a_796_, v_a_797_);
lean_dec(v_stx_795_);
return v___x_808_;
}
else
{
lean_object* v_val_809_; lean_object* v___x_811_; 
lean_dec(v_stx_795_);
v_val_809_ = lean_ctor_get(v_a_800_, 0);
lean_inc(v_val_809_);
lean_dec_ref_known(v_a_800_, 1);
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 0, v_val_809_);
v___x_811_ = v___x_802_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_stx_795_);
v_a_814_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_799_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_799_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Attribute_Builtin_getIdent(v_stx_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_827_, v_a_828_, v_a_829_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_852_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_852_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_852_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_852_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
if (lean_obj_tag(v_a_832_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v_val_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v_val_840_ = lean_ctor_get(v_a_832_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_832_);
if (v_isSharedCheck_851_ == 0)
{
v___x_842_ = v_a_832_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_val_840_);
lean_dec(v_a_832_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_Syntax_getId(v_val_840_);
lean_dec(v_val_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_846_);
v___x_848_ = v___x_834_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
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
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_831_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_831_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Attribute_Builtin_getIdent(v_stx_866_, v_a_867_, v_a_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_879_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_879_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = l_Lean_Syntax_getId(v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_875_);
v___x_877_ = v___x_873_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_870_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_870_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Attribute_Builtin_getId(v_stx_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_892_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = l_Lean_Syntax_isNone(v_optPrioStx_896_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = l_Lean_Syntax_getArg(v_optPrioStx_896_, v___x_901_);
v___x_903_ = l_Lean_Syntax_isNatLit_x3f(v___x_902_);
lean_dec(v___x_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_904_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_896_);
v___x_905_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_896_);
v___x_906_ = l_Lean_indentD(v___x_905_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_896_, v___x_907_, v_a_897_, v_a_898_);
lean_dec(v_optPrioStx_896_);
return v___x_908_;
}
else
{
lean_object* v_val_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v_optPrioStx_896_);
v_val_909_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_903_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_val_909_);
lean_dec(v___x_903_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set_tag(v___x_911_, 0);
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_val_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_optPrioStx_896_);
v___x_917_ = lean_unsigned_to_nat(1000u);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_926_ = l_Lean_stringToMessageData(v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
lean_inc(v_stx_927_);
v___x_931_ = l_Lean_Syntax_getKind(v_stx_927_);
v___x_932_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_933_ = lean_name_eq(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_934_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_927_);
v___x_935_ = l_Lean_MessageData_ofSyntax(v_stx_927_);
v___x_936_ = l_Lean_indentD(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_934_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_927_, v___x_937_, v_a_928_, v_a_929_);
lean_dec(v_stx_927_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = l_Lean_Syntax_getArg(v_stx_927_, v___x_939_);
lean_dec(v_stx_927_);
v___x_941_ = l_Lean_getAttrParamOptPrio(v___x_940_, v_a_928_, v_a_929_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Attribute_Builtin_getPrio(v_stx_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_946_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_name_958_, uint8_t v_kind_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___y_966_; 
v___x_960_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_961_ = l_Lean_MessageData_ofName(v_name_958_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
switch(v_kind_959_)
{
case 0:
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_966_ = v___x_973_;
goto v___jp_965_;
}
case 1:
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_966_ = v___x_974_;
goto v___jp_965_;
}
default: 
{
lean_object* v___x_975_; 
v___x_975_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_966_ = v___x_975_;
goto v___jp_965_;
}
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_inc_ref(v___y_966_);
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___y_966_);
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_964_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwError___redArg(v_inst_956_, v_inst_957_, v___x_971_);
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_name_978_, lean_object* v_kind_979_){
_start:
{
uint8_t v_kind_boxed_980_; lean_object* v_res_981_; 
v_kind_boxed_980_ = lean_unbox(v_kind_979_);
v_res_981_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_976_, v_inst_977_, v_name_978_, v_kind_boxed_980_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_00_u03b1_985_, lean_object* v_name_986_, uint8_t v_kind_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_983_, v_inst_984_, v_name_986_, v_kind_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_989_, lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_00_u03b1_992_, lean_object* v_name_993_, lean_object* v_kind_994_){
_start:
{
uint8_t v_kind_boxed_995_; lean_object* v_res_996_; 
v_kind_boxed_995_ = lean_unbox(v_kind_994_);
v_res_996_ = l_Lean_throwAttrMustBeGlobal(v_m_989_, v_inst_990_, v_inst_991_, v_00_u03b1_992_, v_name_993_, v_kind_boxed_995_);
return v_res_996_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_attrName_1008_, lean_object* v_declName_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1011_ = l_Lean_MessageData_ofName(v_attrName_1008_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = 0;
v___x_1016_ = l_Lean_MessageData_ofConstName(v_declName_1009_, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1014_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_throwError___redArg(v_inst_1006_, v_inst_1007_, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_00_u03b1_1024_, lean_object* v_attrName_1025_, lean_object* v_declName_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1022_, v_inst_1023_, v_attrName_1025_, v_declName_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_attrName_1036_, lean_object* v_declName_1037_, lean_object* v_asyncPrefix_x3f_1038_){
_start:
{
lean_object* v___y_1040_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1038_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_MessageData_nil;
v___y_1040_ = v___x_1053_;
goto v___jp_1039_;
}
else
{
lean_object* v_val_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_val_1054_ = lean_ctor_get(v_asyncPrefix_x3f_1038_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_asyncPrefix_x3f_1038_, 1);
v___x_1055_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1056_ = l_Lean_MessageData_ofName(v_val_1054_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___y_1040_ = v___x_1059_;
goto v___jp_1039_;
}
v___jp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1041_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1042_ = l_Lean_MessageData_ofName(v_attrName_1036_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = 0;
v___x_1047_ = l_Lean_MessageData_ofConstName(v_declName_1037_, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1045_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___y_1040_);
v___x_1052_ = l_Lean_throwError___redArg(v_inst_1034_, v_inst_1035_, v___x_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1060_, lean_object* v_inst_1061_, lean_object* v_inst_1062_, lean_object* v_00_u03b1_1063_, lean_object* v_attrName_1064_, lean_object* v_declName_1065_, lean_object* v_asyncPrefix_x3f_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1061_, v_inst_1062_, v_attrName_1064_, v_declName_1065_, v_asyncPrefix_x3f_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_attrName_1082_, lean_object* v_declName_1083_, lean_object* v_givenType_1084_, lean_object* v_expectedType_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1086_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1087_ = l_Lean_MessageData_ofName(v_attrName_1082_);
lean_inc_ref(v___x_1087_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = 0;
v___x_1092_ = l_Lean_MessageData_ofConstName(v_declName_1083_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1090_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_indentExpr(v_givenType_1084_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v___x_1087_);
v___x_1101_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_indentExpr(v_expectedType_1085_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_throwError___redArg(v_inst_1080_, v_inst_1081_, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_00_u03b1_1109_, lean_object* v_attrName_1110_, lean_object* v_declName_1111_, lean_object* v_givenType_1112_, lean_object* v_expectedType_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1107_, v_inst_1108_, v_attrName_1110_, v_declName_1111_, v_givenType_1112_, v_expectedType_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1115_, uint8_t v_skipRealize_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v_env_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1119_ = lean_st_ref_get(v___y_1117_);
v_env_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc_ref(v_env_1120_);
lean_dec(v___x_1119_);
v___x_1121_ = l_Lean_Environment_contains(v_env_1120_, v_constName_1115_, v_skipRealize_1116_);
v___x_1122_ = lean_box(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1124_, lean_object* v_skipRealize_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_skipRealize_boxed_1128_; lean_object* v_res_1129_; 
v_skipRealize_boxed_1128_ = lean_unbox(v_skipRealize_1125_);
v_res_1129_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1124_, v_skipRealize_boxed_1128_, v___y_1126_);
lean_dec(v___y_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1130_, uint8_t v_skipRealize_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1130_, v_skipRealize_1131_, v___y_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1136_, lean_object* v_skipRealize_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_skipRealize_boxed_1141_; lean_object* v_res_1142_; 
v_skipRealize_boxed_1141_ = lean_unbox(v_skipRealize_1137_);
v_res_1142_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1136_, v_skipRealize_boxed_1141_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1143_, uint8_t v_isExporting_1144_, lean_object* v___x_1145_, lean_object* v_a_x3f_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v_env_1149_; lean_object* v_nextMacroScope_1150_; lean_object* v_ngen_1151_; lean_object* v_auxDeclNGen_1152_; lean_object* v_traceState_1153_; lean_object* v_messages_1154_; lean_object* v_infoState_1155_; lean_object* v_snapshotTasks_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1167_; 
v___x_1148_ = lean_st_ref_take(v___y_1143_);
v_env_1149_ = lean_ctor_get(v___x_1148_, 0);
v_nextMacroScope_1150_ = lean_ctor_get(v___x_1148_, 1);
v_ngen_1151_ = lean_ctor_get(v___x_1148_, 2);
v_auxDeclNGen_1152_ = lean_ctor_get(v___x_1148_, 3);
v_traceState_1153_ = lean_ctor_get(v___x_1148_, 4);
v_messages_1154_ = lean_ctor_get(v___x_1148_, 6);
v_infoState_1155_ = lean_ctor_get(v___x_1148_, 7);
v_snapshotTasks_1156_ = lean_ctor_get(v___x_1148_, 8);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v___x_1148_, 5);
lean_dec(v_unused_1168_);
v___x_1158_ = v___x_1148_;
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snapshotTasks_1156_);
lean_inc(v_infoState_1155_);
lean_inc(v_messages_1154_);
lean_inc(v_traceState_1153_);
lean_inc(v_auxDeclNGen_1152_);
lean_inc(v_ngen_1151_);
lean_inc(v_nextMacroScope_1150_);
lean_inc(v_env_1149_);
lean_dec(v___x_1148_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1167_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = l_Lean_Environment_setExporting(v_env_1149_, v_isExporting_1144_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 5, v___x_1145_);
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_nextMacroScope_1150_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_ngen_1151_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_auxDeclNGen_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_traceState_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1166_, 6, v_messages_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 7, v_infoState_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 8, v_snapshotTasks_1156_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_st_ref_set(v___y_1143_, v___x_1162_);
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1169_, lean_object* v_isExporting_1170_, lean_object* v___x_1171_, lean_object* v_a_x3f_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_isExporting_boxed_1174_; lean_object* v_res_1175_; 
v_isExporting_boxed_1174_ = lean_unbox(v_isExporting_1170_);
v_res_1175_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1169_, v_isExporting_boxed_1174_, v___x_1171_, v_a_x3f_1172_);
lean_dec(v_a_x3f_1172_);
lean_dec(v___y_1169_);
return v_res_1175_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1176_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1181_, uint8_t v_isExporting_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v_env_1187_; uint8_t v_isExporting_1188_; lean_object* v___x_1239_; uint8_t v_isModule_1240_; 
v___x_1186_ = lean_st_ref_get(v___y_1184_);
v_env_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc_ref(v_env_1187_);
lean_dec(v___x_1186_);
v_isExporting_1188_ = lean_ctor_get_uint8(v_env_1187_, sizeof(void*)*8);
v___x_1239_ = l_Lean_Environment_header(v_env_1187_);
lean_dec_ref(v_env_1187_);
v_isModule_1240_ = lean_ctor_get_uint8(v___x_1239_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1239_);
if (v_isModule_1240_ == 0)
{
lean_object* v___x_1241_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1241_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1241_;
}
else
{
if (v_isExporting_1188_ == 0)
{
if (v_isExporting_1182_ == 0)
{
lean_object* v___x_1242_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1242_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1242_;
}
else
{
goto v___jp_1189_;
}
}
else
{
if (v_isExporting_1182_ == 0)
{
goto v___jp_1189_;
}
else
{
lean_object* v___x_1243_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1243_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1243_;
}
}
}
v___jp_1189_:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v_nextMacroScope_1192_; lean_object* v_ngen_1193_; lean_object* v_auxDeclNGen_1194_; lean_object* v_traceState_1195_; lean_object* v_messages_1196_; lean_object* v_infoState_1197_; lean_object* v_snapshotTasks_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1237_; 
v___x_1190_ = lean_st_ref_take(v___y_1184_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
v_nextMacroScope_1192_ = lean_ctor_get(v___x_1190_, 1);
v_ngen_1193_ = lean_ctor_get(v___x_1190_, 2);
v_auxDeclNGen_1194_ = lean_ctor_get(v___x_1190_, 3);
v_traceState_1195_ = lean_ctor_get(v___x_1190_, 4);
v_messages_1196_ = lean_ctor_get(v___x_1190_, 6);
v_infoState_1197_ = lean_ctor_get(v___x_1190_, 7);
v_snapshotTasks_1198_ = lean_ctor_get(v___x_1190_, 8);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1190_, 5);
lean_dec(v_unused_1238_);
v___x_1200_ = v___x_1190_;
v_isShared_1201_ = v_isSharedCheck_1237_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snapshotTasks_1198_);
lean_inc(v_infoState_1197_);
lean_inc(v_messages_1196_);
lean_inc(v_traceState_1195_);
lean_inc(v_auxDeclNGen_1194_);
lean_inc(v_ngen_1193_);
lean_inc(v_nextMacroScope_1192_);
lean_inc(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1237_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Environment_setExporting(v_env_1191_, v_isExporting_1182_);
v___x_1203_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 5, v___x_1203_);
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_nextMacroScope_1192_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_ngen_1193_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_auxDeclNGen_1194_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_traceState_1195_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_messages_1196_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_infoState_1197_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_snapshotTasks_1198_);
v___x_1205_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v_r_1207_; 
v___x_1206_ = lean_st_ref_set(v___y_1184_, v___x_1205_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v_r_1207_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
if (lean_obj_tag(v_r_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1224_; 
v_a_1208_ = lean_ctor_get(v_r_1207_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_r_1207_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1210_ = v_r_1207_;
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v_r_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1224_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
lean_inc(v_a_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 1);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v___x_1214_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1184_, v_isExporting_1188_, v___x_1203_, v___x_1213_);
lean_dec_ref(v___x_1213_);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1222_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_a_1208_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1208_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1225_ = lean_ctor_get(v_r_1207_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v_r_1207_, 1);
v___x_1226_ = lean_box(0);
v___x_1227_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1184_, v_isExporting_1188_, v___x_1203_, v___x_1226_);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1227_, 0);
lean_dec(v_unused_1235_);
v___x_1229_ = v___x_1227_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 1);
lean_ctor_set(v___x_1229_, 0, v_a_1225_);
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1225_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1244_, lean_object* v_isExporting_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v_isExporting_boxed_1249_; lean_object* v_res_1250_; 
v_isExporting_boxed_1249_ = lean_unbox(v_isExporting_1245_);
v_res_1250_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1244_, v_isExporting_boxed_1249_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1251_, lean_object* v_x_1252_, uint8_t v_isExporting_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1252_, v_isExporting_1253_, v___y_1254_, v___y_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_x_1259_, lean_object* v_isExporting_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_isExporting_boxed_1264_; lean_object* v_res_1265_; 
v_isExporting_boxed_1264_ = lean_unbox(v_isExporting_1260_);
v_res_1265_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1258_, v_x_1259_, v_isExporting_boxed_1264_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1265_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1266_, lean_object* v_opt_1267_){
_start:
{
lean_object* v_name_1268_; lean_object* v_defValue_1269_; lean_object* v_map_1270_; lean_object* v___x_1271_; 
v_name_1268_ = lean_ctor_get(v_opt_1267_, 0);
v_defValue_1269_ = lean_ctor_get(v_opt_1267_, 1);
v_map_1270_ = lean_ctor_get(v_opts_1266_, 0);
v___x_1271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1270_, v_name_1268_);
if (lean_obj_tag(v___x_1271_) == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_unbox(v_defValue_1269_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1271_, 1);
if (lean_obj_tag(v_val_1273_) == 1)
{
uint8_t v_v_1274_; 
v_v_1274_ = lean_ctor_get_uint8(v_val_1273_, 0);
lean_dec_ref_known(v_val_1273_, 0);
return v_v_1274_;
}
else
{
uint8_t v___x_1275_; 
lean_dec(v_val_1273_);
v___x_1275_ = lean_unbox(v_defValue_1269_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1276_, lean_object* v_opt_1277_){
_start:
{
uint8_t v_res_1278_; lean_object* v_r_1279_; 
v_res_1278_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1276_, v_opt_1277_);
lean_dec_ref(v_opt_1277_);
lean_dec_ref(v_opts_1276_);
v_r_1279_ = lean_box(v_res_1278_);
return v_r_1279_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1287_, uint8_t v_suppressElabErrors_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1289_) == 1)
{
lean_object* v_pre_1290_; 
v_pre_1290_ = lean_ctor_get(v_x_1289_, 0);
switch(lean_obj_tag(v_pre_1290_))
{
case 1:
{
lean_object* v_pre_1291_; 
v_pre_1291_ = lean_ctor_get(v_pre_1290_, 0);
switch(lean_obj_tag(v_pre_1291_))
{
case 0:
{
lean_object* v_str_1292_; lean_object* v_str_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_str_1292_ = lean_ctor_get(v_x_1289_, 1);
v_str_1293_ = lean_ctor_get(v_pre_1290_, 1);
v___x_1294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1295_ = lean_string_dec_eq(v_str_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1297_ = lean_string_dec_eq(v_str_1293_, v___x_1296_);
if (v___x_1297_ == 0)
{
return v___y_1287_;
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1299_ = lean_string_dec_eq(v_str_1292_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___y_1287_;
}
else
{
return v_suppressElabErrors_1288_;
}
}
}
else
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1301_ = lean_string_dec_eq(v_str_1292_, v___x_1300_);
if (v___x_1301_ == 0)
{
return v___y_1287_;
}
else
{
return v_suppressElabErrors_1288_;
}
}
}
case 1:
{
lean_object* v_pre_1302_; 
v_pre_1302_ = lean_ctor_get(v_pre_1291_, 0);
if (lean_obj_tag(v_pre_1302_) == 0)
{
lean_object* v_str_1303_; lean_object* v_str_1304_; lean_object* v_str_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_str_1303_ = lean_ctor_get(v_x_1289_, 1);
v_str_1304_ = lean_ctor_get(v_pre_1290_, 1);
v_str_1305_ = lean_ctor_get(v_pre_1291_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1307_ = lean_string_dec_eq(v_str_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___y_1287_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1309_ = lean_string_dec_eq(v_str_1304_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___y_1287_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1311_ = lean_string_dec_eq(v_str_1303_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___y_1287_;
}
else
{
return v_suppressElabErrors_1288_;
}
}
}
}
else
{
return v___y_1287_;
}
}
default: 
{
return v___y_1287_;
}
}
}
case 0:
{
lean_object* v_str_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_str_1312_ = lean_ctor_get(v_x_1289_, 1);
v___x_1313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1314_ = lean_string_dec_eq(v_str_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
return v___y_1287_;
}
else
{
return v_suppressElabErrors_1288_;
}
}
default: 
{
return v___y_1287_;
}
}
}
else
{
return v___y_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1315_, lean_object* v_suppressElabErrors_1316_, lean_object* v_x_1317_){
_start:
{
uint8_t v___y_4996__boxed_1318_; uint8_t v_suppressElabErrors_boxed_1319_; uint8_t v_res_1320_; lean_object* v_r_1321_; 
v___y_4996__boxed_1318_ = lean_unbox(v___y_1315_);
v_suppressElabErrors_boxed_1319_ = lean_unbox(v_suppressElabErrors_1316_);
v_res_1320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4996__boxed_1318_, v_suppressElabErrors_boxed_1319_, v_x_1317_);
lean_dec(v_x_1317_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1322_, lean_object* v_msgData_1323_, uint8_t v_severity_1324_, uint8_t v_isSilent_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; uint8_t v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1368_; uint8_t v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; uint8_t v___x_1413_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1421_; uint8_t v___y_1423_; uint8_t v___x_1438_; 
v___x_1413_ = 2;
v___x_1438_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1324_, v___x_1413_);
if (v___x_1438_ == 0)
{
v___y_1423_ = v___x_1438_;
goto v___jp_1422_;
}
else
{
uint8_t v___x_1439_; 
lean_inc_ref(v_msgData_1323_);
v___x_1439_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1323_);
v___y_1423_ = v___x_1439_;
goto v___jp_1422_;
}
v___jp_1329_:
{
lean_object* v___x_1339_; lean_object* v_currNamespace_1340_; lean_object* v_openDecls_1341_; lean_object* v_env_1342_; lean_object* v_nextMacroScope_1343_; lean_object* v_ngen_1344_; lean_object* v_auxDeclNGen_1345_; lean_object* v_traceState_1346_; lean_object* v_cache_1347_; lean_object* v_messages_1348_; lean_object* v_infoState_1349_; lean_object* v_snapshotTasks_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1364_; 
v___x_1339_ = lean_st_ref_take(v___y_1338_);
v_currNamespace_1340_ = lean_ctor_get(v___y_1337_, 6);
v_openDecls_1341_ = lean_ctor_get(v___y_1337_, 7);
v_env_1342_ = lean_ctor_get(v___x_1339_, 0);
v_nextMacroScope_1343_ = lean_ctor_get(v___x_1339_, 1);
v_ngen_1344_ = lean_ctor_get(v___x_1339_, 2);
v_auxDeclNGen_1345_ = lean_ctor_get(v___x_1339_, 3);
v_traceState_1346_ = lean_ctor_get(v___x_1339_, 4);
v_cache_1347_ = lean_ctor_get(v___x_1339_, 5);
v_messages_1348_ = lean_ctor_get(v___x_1339_, 6);
v_infoState_1349_ = lean_ctor_get(v___x_1339_, 7);
v_snapshotTasks_1350_ = lean_ctor_get(v___x_1339_, 8);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1352_ = v___x_1339_;
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snapshotTasks_1350_);
lean_inc(v_infoState_1349_);
lean_inc(v_messages_1348_);
lean_inc(v_cache_1347_);
lean_inc(v_traceState_1346_);
lean_inc(v_auxDeclNGen_1345_);
lean_inc(v_ngen_1344_);
lean_inc(v_nextMacroScope_1343_);
lean_inc(v_env_1342_);
lean_dec(v___x_1339_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1364_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_inc(v_openDecls_1341_);
lean_inc(v_currNamespace_1340_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_currNamespace_1340_);
lean_ctor_set(v___x_1354_, 1, v_openDecls_1341_);
v___x_1355_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc_ref(v___y_1331_);
v___x_1356_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1356_, 0, v___y_1331_);
lean_ctor_set(v___x_1356_, 1, v___y_1332_);
lean_ctor_set(v___x_1356_, 2, v___y_1333_);
lean_ctor_set(v___x_1356_, 3, v___y_1334_);
lean_ctor_set(v___x_1356_, 4, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5, v___y_1336_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5 + 1, v___y_1330_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5 + 2, v_isSilent_1325_);
v___x_1357_ = l_Lean_MessageLog_add(v___x_1356_, v_messages_1348_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 6, v___x_1357_);
v___x_1359_ = v___x_1352_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_env_1342_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_nextMacroScope_1343_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_ngen_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_auxDeclNGen_1345_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_traceState_1346_);
lean_ctor_set(v_reuseFailAlloc_1363_, 5, v_cache_1347_);
lean_ctor_set(v_reuseFailAlloc_1363_, 6, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 7, v_infoState_1349_);
lean_ctor_set(v_reuseFailAlloc_1363_, 8, v_snapshotTasks_1350_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_st_ref_set(v___y_1338_, v___x_1359_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
v___jp_1365_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1389_; 
v___x_1374_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1323_);
v___x_1375_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1374_, v___y_1326_, v___y_1327_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1389_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1389_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_inc_ref_n(v___y_1372_, 2);
v___x_1380_ = l_Lean_FileMap_toPosition(v___y_1372_, v___y_1371_);
lean_dec(v___y_1371_);
v___x_1381_ = l_Lean_FileMap_toPosition(v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1370_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v___y_1366_);
v___y_1330_ = v___y_1368_;
v___y_1331_ = v___y_1367_;
v___y_1332_ = v___x_1380_;
v___y_1333_ = v___x_1382_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_a_1376_;
v___y_1336_ = v___y_1369_;
v___y_1337_ = v___y_1326_;
v___y_1338_ = v___y_1327_;
goto v___jp_1329_;
}
else
{
uint8_t v___x_1384_; 
lean_inc(v_a_1376_);
v___x_1384_ = l_Lean_MessageData_hasTag(v___y_1366_, v_a_1376_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1382_, 1);
lean_dec_ref(v___x_1380_);
lean_dec(v_a_1376_);
v___x_1385_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1385_);
v___x_1387_ = v___x_1378_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_del_object(v___x_1378_);
v___y_1330_ = v___y_1368_;
v___y_1331_ = v___y_1367_;
v___y_1332_ = v___x_1380_;
v___y_1333_ = v___x_1382_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v_a_1376_;
v___y_1336_ = v___y_1369_;
v___y_1337_ = v___y_1326_;
v___y_1338_ = v___y_1327_;
goto v___jp_1329_;
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Syntax_getTailPos_x3f(v___y_1394_, v___y_1395_);
lean_dec(v___y_1394_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_inc(v___y_1398_);
v___y_1366_ = v___y_1391_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1392_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1396_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v___y_1397_;
v___y_1373_ = v___y_1398_;
goto v___jp_1365_;
}
else
{
lean_object* v_val_1400_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___y_1366_ = v___y_1391_;
v___y_1367_ = v___y_1393_;
v___y_1368_ = v___y_1392_;
v___y_1369_ = v___y_1395_;
v___y_1370_ = v___y_1396_;
v___y_1371_ = v___y_1398_;
v___y_1372_ = v___y_1397_;
v___y_1373_ = v_val_1400_;
goto v___jp_1365_;
}
}
v___jp_1401_:
{
lean_object* v_ref_1409_; lean_object* v___x_1410_; 
v_ref_1409_ = l_Lean_replaceRef(v_ref_1322_, v___y_1404_);
v___x_1410_ = l_Lean_Syntax_getPos_x3f(v_ref_1409_, v___y_1405_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___y_1391_ = v___y_1402_;
v___y_1392_ = v___y_1408_;
v___y_1393_ = v___y_1403_;
v___y_1394_ = v_ref_1409_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v___y_1406_;
v___y_1397_ = v___y_1407_;
v___y_1398_ = v___x_1411_;
goto v___jp_1390_;
}
else
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1410_, 1);
v___y_1391_ = v___y_1402_;
v___y_1392_ = v___y_1408_;
v___y_1393_ = v___y_1403_;
v___y_1394_ = v_ref_1409_;
v___y_1395_ = v___y_1405_;
v___y_1396_ = v___y_1406_;
v___y_1397_ = v___y_1407_;
v___y_1398_ = v_val_1412_;
goto v___jp_1390_;
}
}
v___jp_1414_:
{
if (v___y_1421_ == 0)
{
v___y_1402_ = v___y_1418_;
v___y_1403_ = v___y_1416_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v_severity_1324_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___y_1418_;
v___y_1403_ = v___y_1416_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1420_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___x_1413_;
goto v___jp_1401_;
}
}
v___jp_1422_:
{
if (v___y_1423_ == 0)
{
lean_object* v_fileName_1424_; lean_object* v_fileMap_1425_; lean_object* v_options_1426_; lean_object* v_ref_1427_; uint8_t v_suppressElabErrors_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; uint8_t v___x_1432_; uint8_t v___x_1433_; 
v_fileName_1424_ = lean_ctor_get(v___y_1326_, 0);
v_fileMap_1425_ = lean_ctor_get(v___y_1326_, 1);
v_options_1426_ = lean_ctor_get(v___y_1326_, 2);
v_ref_1427_ = lean_ctor_get(v___y_1326_, 5);
v_suppressElabErrors_1428_ = lean_ctor_get_uint8(v___y_1326_, sizeof(void*)*14 + 1);
v___x_1429_ = lean_box(v___y_1423_);
v___x_1430_ = lean_box(v_suppressElabErrors_1428_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1431_, 0, v___x_1429_);
lean_closure_set(v___f_1431_, 1, v___x_1430_);
v___x_1432_ = 1;
v___x_1433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1324_, v___x_1432_);
if (v___x_1433_ == 0)
{
v___y_1415_ = v_ref_1427_;
v___y_1416_ = v_fileName_1424_;
v___y_1417_ = v_suppressElabErrors_1428_;
v___y_1418_ = v___f_1431_;
v___y_1419_ = v_fileMap_1425_;
v___y_1420_ = v___y_1423_;
v___y_1421_ = v___x_1433_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = l_Lean_warningAsError;
v___x_1435_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1426_, v___x_1434_);
v___y_1415_ = v_ref_1427_;
v___y_1416_ = v_fileName_1424_;
v___y_1417_ = v_suppressElabErrors_1428_;
v___y_1418_ = v___f_1431_;
v___y_1419_ = v_fileMap_1425_;
v___y_1420_ = v___y_1423_;
v___y_1421_ = v___x_1435_;
goto v___jp_1414_;
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec_ref(v_msgData_1323_);
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1440_, lean_object* v_msgData_1441_, lean_object* v_severity_1442_, lean_object* v_isSilent_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_severity_boxed_1447_; uint8_t v_isSilent_boxed_1448_; lean_object* v_res_1449_; 
v_severity_boxed_1447_ = lean_unbox(v_severity_1442_);
v_isSilent_boxed_1448_ = lean_unbox(v_isSilent_1443_);
v_res_1449_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1440_, v_msgData_1441_, v_severity_boxed_1447_, v_isSilent_boxed_1448_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_ref_1440_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1450_, uint8_t v_severity_1451_, uint8_t v_isSilent_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_ref_1456_; lean_object* v___x_1457_; 
v_ref_1456_ = lean_ctor_get(v___y_1453_, 5);
v___x_1457_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1456_, v_msgData_1450_, v_severity_1451_, v_isSilent_1452_, v___y_1453_, v___y_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1458_, lean_object* v_severity_1459_, lean_object* v_isSilent_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_severity_boxed_1464_; uint8_t v_isSilent_boxed_1465_; lean_object* v_res_1466_; 
v_severity_boxed_1464_ = lean_unbox(v_severity_1459_);
v_isSilent_boxed_1465_ = lean_unbox(v_isSilent_1460_);
v_res_1466_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1458_, v_severity_boxed_1464_, v_isSilent_boxed_1465_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
uint8_t v___x_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = 1;
v___x_1472_ = 0;
v___x_1473_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1467_, v___x_1471_, v___x_1472_, v___y_1468_, v___y_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_options_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_options_1482_ = lean_ctor_get(v___y_1480_, 2);
v___x_1483_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1482_, v_opt_1479_);
v___x_1484_ = lean_box(v___x_1483_);
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1486_, v___y_1487_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_opt_1486_);
return v_res_1489_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_env_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1523_; 
v___x_1500_ = lean_st_ref_get(v___y_1498_);
v_env_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref(v_env_1501_);
lean_dec(v___x_1500_);
v___x_1502_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1503_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1502_, v___y_1497_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1523_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1523_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v_isExporting_1513_; 
v_isExporting_1513_ = lean_ctor_get_uint8(v_env_1501_, sizeof(void*)*8);
lean_dec_ref(v_env_1501_);
if (v_isExporting_1513_ == 0)
{
lean_dec(v_a_1504_);
lean_dec(v_id_1496_);
goto v___jp_1508_;
}
else
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_isPrivateName(v_id_1496_);
if (v___x_1514_ == 0)
{
lean_dec(v_a_1504_);
lean_dec(v_id_1496_);
goto v___jp_1508_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_unbox(v_a_1504_);
lean_dec(v_a_1504_);
if (v___x_1515_ == 0)
{
lean_dec(v_id_1496_);
goto v___jp_1508_;
}
else
{
lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1506_);
v___x_1516_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1517_ = 0;
v___x_1518_ = l_Lean_MessageData_ofConstName(v_id_1496_, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1516_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1521_, v___y_1497_, v___y_1498_);
return v___x_1522_;
}
}
}
v___jp_1508_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1532_, uint8_t v_isModule_1533_, lean_object* v_attrName_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
lean_inc(v_declName_1532_);
v___x_1538_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1532_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref_known(v___x_1538_, 1);
lean_inc(v_declName_1532_);
v___x_1539_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1532_, v_isModule_1533_, v___y_1536_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1560_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_a_1540_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_del_object(v___x_1542_);
v___x_1545_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1546_ = l_Lean_MessageData_ofName(v_attrName_1534_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
v___x_1551_ = l_Lean_MessageData_ofConstName(v_declName_1532_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1549_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1554_, v___y_1535_, v___y_1536_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_dec(v_a_1540_);
lean_dec(v_attrName_1534_);
lean_dec(v_declName_1532_);
v___x_1556_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1556_);
v___x_1558_ = v___x_1542_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_dec(v_attrName_1534_);
lean_dec(v_declName_1532_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1561_, lean_object* v_isModule_1562_, lean_object* v_attrName_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_isModule_boxed_1567_; lean_object* v_res_1568_; 
v_isModule_boxed_1567_ = lean_unbox(v_isModule_1562_);
v_res_1568_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1561_, v_isModule_boxed_1567_, v_attrName_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1569_, lean_object* v_declName_1570_, uint8_t v_attrKind_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v_env_1579_; lean_object* v___x_1580_; uint8_t v_isModule_1581_; 
v___x_1575_ = lean_st_ref_get(v_a_1573_);
v_env_1579_ = lean_ctor_get(v___x_1575_, 0);
lean_inc_ref(v_env_1579_);
lean_dec(v___x_1575_);
v___x_1580_ = l_Lean_Environment_header(v_env_1579_);
lean_dec_ref(v_env_1579_);
v_isModule_1581_ = lean_ctor_get_uint8(v___x_1580_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1580_);
if (v_isModule_1581_ == 0)
{
lean_dec(v_declName_1570_);
lean_dec(v_attrName_1569_);
goto v___jp_1576_;
}
else
{
uint8_t v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = 1;
v___x_1583_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1571_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_box(v_isModule_1581_);
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1585_, 0, v_declName_1570_);
lean_closure_set(v___f_1585_, 1, v___x_1584_);
lean_closure_set(v___f_1585_, 2, v_attrName_1569_);
v___x_1586_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1585_, v_isModule_1581_, v_a_1572_, v_a_1573_);
return v___x_1586_;
}
else
{
lean_dec(v_declName_1570_);
lean_dec(v_attrName_1569_);
goto v___jp_1576_;
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1587_, lean_object* v_declName_1588_, lean_object* v_attrKind_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
uint8_t v_attrKind_boxed_1593_; lean_object* v_res_1594_; 
v_attrKind_boxed_1593_ = lean_unbox(v_attrKind_1589_);
v_res_1594_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1587_, v_declName_1588_, v_attrKind_boxed_1593_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1595_, v___y_1596_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_opt_1600_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1608_, lean_object* v_declName_1609_, uint8_t v_attrKind_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_env_1616_; lean_object* v___x_1617_; uint8_t v_isModule_1618_; 
v___x_1614_ = lean_st_ref_get(v_a_1612_);
v___x_1615_ = lean_st_ref_get(v_a_1612_);
v_env_1616_ = lean_ctor_get(v___x_1614_, 0);
lean_inc_ref(v_env_1616_);
lean_dec(v___x_1614_);
v___x_1617_ = l_Lean_Environment_header(v_env_1616_);
lean_dec_ref(v_env_1616_);
v_isModule_1618_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1617_);
if (v_isModule_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec(v___x_1615_);
v___x_1619_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1608_, v_declName_1609_, v_attrKind_1610_, v_a_1611_, v_a_1612_);
return v___x_1619_;
}
else
{
lean_object* v_env_1620_; uint8_t v___x_1621_; 
v_env_1620_ = lean_ctor_get(v___x_1615_, 0);
lean_inc_ref(v_env_1620_);
lean_dec(v___x_1615_);
lean_inc(v_declName_1609_);
v___x_1621_ = l_Lean_isMarkedMeta(v_env_1620_, v_declName_1609_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1622_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1623_ = l_Lean_MessageData_ofName(v_attrName_1608_);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_MessageData_ofConstName(v_declName_1609_, v___x_1621_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1630_, v_a_1611_, v_a_1612_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1608_, v_declName_1609_, v_attrKind_1610_, v_a_1611_, v_a_1612_);
return v___x_1632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1633_, lean_object* v_declName_1634_, lean_object* v_attrKind_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
uint8_t v_attrKind_boxed_1639_; lean_object* v_res_1640_; 
v_attrKind_boxed_1639_ = lean_unbox(v_attrKind_1635_);
v_res_1640_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1633_, v_declName_1634_, v_attrKind_boxed_1639_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1649_, v___y_1650_);
lean_dec_ref(v___y_1650_);
lean_dec_ref(v_x_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1653_, lean_object* v_x_1654_){
_start:
{
lean_inc(v_s_1653_);
return v_s_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1655_, v_x_1656_);
lean_dec(v_x_1656_);
lean_dec(v_s_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1665_, v_x_1666_);
lean_dec(v_x_1666_);
lean_dec_ref(v_x_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_box(0);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1670_);
lean_dec(v_x_1670_);
return v_res_1671_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___f_1679_; lean_object* v___f_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___f_1677_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1678_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1679_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1680_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1683_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1681_);
lean_ctor_set(v___x_1683_, 2, v___f_1680_);
lean_ctor_set(v___x_1683_, 3, v___f_1679_);
lean_ctor_set(v___x_1683_, 4, v___f_1678_);
lean_ctor_set(v___x_1683_, 5, v___f_1677_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1685_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_registerTagAttribute___lam__0(v_x_1692_);
lean_dec(v_x_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
return v_x_1695_;
}
else
{
lean_object* v_head_1697_; lean_object* v_tail_1698_; uint8_t v___x_1699_; 
v_head_1697_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_head_1697_);
v_tail_1698_ = lean_ctor_get(v_x_1696_, 1);
lean_inc(v_tail_1698_);
lean_dec_ref_known(v_x_1696_, 2);
v___x_1699_ = l_Lean_NameSet_contains(v_newState_1694_, v_head_1697_);
if (v___x_1699_ == 0)
{
lean_dec(v_head_1697_);
v_x_1696_ = v_tail_1698_;
goto _start;
}
else
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_NameSet_insert(v_x_1695_, v_head_1697_);
v_x_1695_ = v___x_1701_;
v_x_1696_ = v_tail_1698_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1703_, v_x_1704_, v_x_1705_);
lean_dec(v_newState_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1707_, lean_object* v_newState_1708_, lean_object* v_newConsts_1709_, lean_object* v_s_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1708_, v_s_1710_, v_newConsts_1709_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1712_, lean_object* v_newState_1713_, lean_object* v_newConsts_1714_, lean_object* v_s_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_registerTagAttribute___lam__1(v_x_1712_, v_newState_1713_, v_newConsts_1714_, v_s_1715_);
lean_dec(v_newState_1713_);
lean_dec(v_x_1712_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v___y_1732_; 
v___x_1730_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1729_) == 0)
{
lean_object* v_size_1736_; 
v_size_1736_ = lean_ctor_get(v_s_1729_, 0);
lean_inc(v_size_1736_);
lean_dec_ref_known(v_s_1729_, 5);
v___y_1732_ = v_size_1736_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_unsigned_to_nat(0u);
v___y_1732_ = v___x_1737_;
goto v___jp_1731_;
}
v___jp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = l_Nat_reprFast(v___y_1732_);
v___x_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
v___x_1735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1730_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1738_, lean_object* v_pivot_1739_, lean_object* v_as_1740_, lean_object* v_i_1741_, lean_object* v_k_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_lt(v_k_1742_, v_hi_1738_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec(v_k_1742_);
v___x_1744_ = lean_array_fswap(v_as_1740_, v_i_1741_, v_hi_1738_);
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_i_1741_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; uint8_t v___x_1747_; 
v___x_1746_ = lean_array_fget_borrowed(v_as_1740_, v_k_1742_);
v___x_1747_ = l_Lean_Name_quickLt(v___x_1746_, v_pivot_1739_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_unsigned_to_nat(1u);
v___x_1749_ = lean_nat_add(v_k_1742_, v___x_1748_);
lean_dec(v_k_1742_);
v_k_1742_ = v___x_1749_;
goto _start;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_array_fswap(v_as_1740_, v_i_1741_, v_k_1742_);
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_i_1741_, v___x_1752_);
lean_dec(v_i_1741_);
v___x_1754_ = lean_nat_add(v_k_1742_, v___x_1752_);
lean_dec(v_k_1742_);
v_as_1740_ = v___x_1751_;
v_i_1741_ = v___x_1753_;
v_k_1742_ = v___x_1754_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1756_, lean_object* v_pivot_1757_, lean_object* v_as_1758_, lean_object* v_i_1759_, lean_object* v_k_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1756_, v_pivot_1757_, v_as_1758_, v_i_1759_, v_k_1760_);
lean_dec(v_pivot_1757_);
lean_dec(v_hi_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1762_, lean_object* v_as_1763_, lean_object* v_lo_1764_, lean_object* v_hi_1765_){
_start:
{
lean_object* v___y_1767_; uint8_t v___x_1777_; 
v___x_1777_ = lean_nat_dec_lt(v_lo_1764_, v_hi_1765_);
if (v___x_1777_ == 0)
{
lean_dec(v_lo_1764_);
return v_as_1763_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_mid_1780_; lean_object* v___y_1782_; lean_object* v___y_1788_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1778_ = lean_nat_add(v_lo_1764_, v_hi_1765_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v_mid_1780_ = lean_nat_shiftr(v___x_1778_, v___x_1779_);
lean_dec(v___x_1778_);
v___x_1793_ = lean_array_fget_borrowed(v_as_1763_, v_mid_1780_);
v___x_1794_ = lean_array_fget_borrowed(v_as_1763_, v_lo_1764_);
v___x_1795_ = l_Lean_Name_quickLt(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1788_ = v_as_1763_;
goto v___jp_1787_;
}
else
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_array_fswap(v_as_1763_, v_lo_1764_, v_mid_1780_);
v___y_1788_ = v___x_1796_;
goto v___jp_1787_;
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_array_fget_borrowed(v___y_1782_, v_mid_1780_);
v___x_1784_ = lean_array_fget_borrowed(v___y_1782_, v_hi_1765_);
v___x_1785_ = l_Lean_Name_quickLt(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec(v_mid_1780_);
v___y_1767_ = v___y_1782_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_array_fswap(v___y_1782_, v_mid_1780_, v_hi_1765_);
lean_dec(v_mid_1780_);
v___y_1767_ = v___x_1786_;
goto v___jp_1766_;
}
}
v___jp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1789_ = lean_array_fget_borrowed(v___y_1788_, v_hi_1765_);
v___x_1790_ = lean_array_fget_borrowed(v___y_1788_, v_lo_1764_);
v___x_1791_ = l_Lean_Name_quickLt(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
v___y_1782_ = v___y_1788_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_array_fswap(v___y_1788_, v_lo_1764_, v_hi_1765_);
v___y_1782_ = v___x_1792_;
goto v___jp_1781_;
}
}
}
v___jp_1766_:
{
lean_object* v_pivot_1768_; lean_object* v___x_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; uint8_t v___x_1772_; 
v_pivot_1768_ = lean_array_fget(v___y_1767_, v_hi_1765_);
lean_inc_n(v_lo_1764_, 2);
v___x_1769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1765_, v_pivot_1768_, v___y_1767_, v_lo_1764_, v_lo_1764_);
lean_dec(v_pivot_1768_);
v_fst_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_fst_1770_);
v_snd_1771_ = lean_ctor_get(v___x_1769_, 1);
lean_inc(v_snd_1771_);
lean_dec_ref(v___x_1769_);
v___x_1772_ = lean_nat_dec_le(v_hi_1765_, v_fst_1770_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1762_, v_snd_1771_, v_lo_1764_, v_fst_1770_);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_fst_1770_, v___x_1774_);
lean_dec(v_fst_1770_);
v_as_1763_ = v___x_1773_;
v_lo_1764_ = v___x_1775_;
goto _start;
}
else
{
lean_dec(v_fst_1770_);
lean_dec(v_lo_1764_);
return v_snd_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1797_, lean_object* v_as_1798_, lean_object* v_lo_1799_, lean_object* v_hi_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1797_, v_as_1798_, v_lo_1799_, v_hi_1800_);
lean_dec(v_hi_1800_);
lean_dec(v_n_1797_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1802_, lean_object* v_as_1803_, size_t v_i_1804_, size_t v_stop_1805_, lean_object* v_b_1806_){
_start:
{
lean_object* v___y_1808_; uint8_t v___x_1812_; 
v___x_1812_ = lean_usize_dec_eq(v_i_1804_, v_stop_1805_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1813_ = lean_array_uget_borrowed(v_as_1803_, v_i_1804_);
v___x_1814_ = 1;
lean_inc_ref(v_env_1802_);
v___x_1815_ = l_Lean_Environment_setExporting(v_env_1802_, v___x_1814_);
lean_inc(v___x_1813_);
v___x_1816_ = l_Lean_Environment_contains(v___x_1815_, v___x_1813_, v___x_1812_);
if (v___x_1816_ == 0)
{
v___y_1808_ = v_b_1806_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1817_; 
lean_inc(v___x_1813_);
v___x_1817_ = lean_array_push(v_b_1806_, v___x_1813_);
v___y_1808_ = v___x_1817_;
goto v___jp_1807_;
}
}
else
{
lean_dec_ref(v_env_1802_);
return v_b_1806_;
}
v___jp_1807_:
{
size_t v___x_1809_; size_t v___x_1810_; 
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_add(v_i_1804_, v___x_1809_);
v_i_1804_ = v___x_1810_;
v_b_1806_ = v___y_1808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1818_, lean_object* v_as_1819_, lean_object* v_i_1820_, lean_object* v_stop_1821_, lean_object* v_b_1822_){
_start:
{
size_t v_i_boxed_1823_; size_t v_stop_boxed_1824_; lean_object* v_res_1825_; 
v_i_boxed_1823_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_stop_boxed_1824_ = lean_unbox_usize(v_stop_1821_);
lean_dec(v_stop_1821_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1818_, v_as_1819_, v_i_boxed_1823_, v_stop_boxed_1824_, v_b_1822_);
lean_dec_ref(v_as_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_object* v_k_1828_; lean_object* v_l_1829_; lean_object* v_r_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_k_1828_ = lean_ctor_get(v_x_1827_, 1);
lean_inc(v_k_1828_);
v_l_1829_ = lean_ctor_get(v_x_1827_, 3);
lean_inc(v_l_1829_);
v_r_1830_ = lean_ctor_get(v_x_1827_, 4);
lean_inc(v_r_1830_);
lean_dec_ref_known(v_x_1827_, 5);
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1826_, v_l_1829_);
v___x_1832_ = lean_array_push(v___x_1831_, v_k_1828_);
v_init_1826_ = v___x_1832_;
v_x_1827_ = v_r_1830_;
goto _start;
}
else
{
return v_init_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1834_, lean_object* v_es_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___y_1839_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___x_1859_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1853_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1837_, v_es_1835_);
v___x_1854_ = lean_array_get_size(v___x_1853_);
v___x_1859_ = lean_nat_dec_eq(v___x_1854_, v___x_1836_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___y_1863_; uint8_t v___x_1865_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_sub(v___x_1854_, v___x_1860_);
v___x_1865_ = lean_nat_dec_le(v___x_1836_, v___x_1861_);
if (v___x_1865_ == 0)
{
lean_inc(v___x_1861_);
v___y_1863_ = v___x_1861_;
goto v___jp_1862_;
}
else
{
v___y_1863_ = v___x_1836_;
goto v___jp_1862_;
}
v___jp_1862_:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_nat_dec_le(v___y_1863_, v___x_1861_);
if (v___x_1864_ == 0)
{
lean_dec(v___x_1861_);
lean_inc(v___y_1863_);
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___y_1863_;
goto v___jp_1855_;
}
else
{
v___y_1856_ = v___y_1863_;
v___y_1857_ = v___x_1861_;
goto v___jp_1855_;
}
}
}
else
{
v___y_1839_ = v___x_1853_;
goto v___jp_1838_;
}
v___jp_1838_:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_array_get_size(v___y_1839_);
v___x_1841_ = lean_nat_dec_lt(v___x_1836_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v_env_1834_);
v___x_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1837_);
lean_ctor_set(v___x_1842_, 1, v___x_1837_);
lean_ctor_set(v___x_1842_, 2, v___y_1839_);
return v___x_1842_;
}
else
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_le(v___x_1840_, v___x_1840_);
if (v___x_1843_ == 0)
{
if (v___x_1841_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v_env_1834_);
v___x_1844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1837_);
lean_ctor_set(v___x_1844_, 1, v___x_1837_);
lean_ctor_set(v___x_1844_, 2, v___y_1839_);
return v___x_1844_;
}
else
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = lean_usize_of_nat(v___x_1840_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1834_, v___y_1839_, v___x_1845_, v___x_1846_, v___x_1837_);
lean_inc_ref(v___x_1847_);
v___x_1848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
lean_ctor_set(v___x_1848_, 2, v___y_1839_);
return v___x_1848_;
}
}
else
{
size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1840_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1834_, v___y_1839_, v___x_1849_, v___x_1850_, v___x_1837_);
lean_inc_ref(v___x_1851_);
v___x_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
lean_ctor_set(v___x_1852_, 2, v___y_1839_);
return v___x_1852_;
}
}
}
v___jp_1855_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1854_, v___x_1853_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
v___y_1839_ = v___x_1858_;
goto v___jp_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1866_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_registerTagAttribute___lam__4(v___x_1871_, v_x_1872_, v_x_1873_);
lean_dec_ref(v_x_1873_);
lean_dec_ref(v_x_1872_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_registerTagAttribute___lam__5(v___x_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1882_, lean_object* v_decl_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1887_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1888_ = l_Lean_MessageData_ofName(v_name_1882_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1891_, v___y_1884_, v___y_1885_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1893_, lean_object* v_decl_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_registerTagAttribute___lam__6(v_name_1893_, v_decl_1894_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v_decl_1894_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1899_, lean_object* v_declName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1904_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1905_ = l_Lean_MessageData_ofName(v_attrName_1899_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = 0;
v___x_1910_ = l_Lean_MessageData_ofConstName(v_declName_1900_, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1913_, v___y_1901_, v___y_1902_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1915_, lean_object* v_declName_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1915_, v_declName_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1921_, lean_object* v_declName_1922_, lean_object* v_asyncPrefix_x3f_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___y_1928_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1923_) == 0)
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_MessageData_nil;
v___y_1928_ = v___x_1941_;
goto v___jp_1927_;
}
else
{
lean_object* v_val_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_val_1942_ = lean_ctor_get(v_asyncPrefix_x3f_1923_, 0);
lean_inc(v_val_1942_);
lean_dec_ref_known(v_asyncPrefix_x3f_1923_, 1);
v___x_1943_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1944_ = l_Lean_MessageData_ofName(v_val_1942_);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___y_1928_ = v___x_1947_;
goto v___jp_1927_;
}
v___jp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1929_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1930_ = l_Lean_MessageData_ofName(v_attrName_1921_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = 0;
v___x_1935_ = l_Lean_MessageData_ofConstName(v_declName_1922_, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1933_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___y_1928_);
v___x_1940_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1939_, v___y_1924_, v___y_1925_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1948_, lean_object* v_declName_1949_, lean_object* v_asyncPrefix_x3f_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1948_, v_declName_1949_, v_asyncPrefix_x3f_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1955_, uint8_t v_kind_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___y_1966_; 
v___x_1960_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1961_ = l_Lean_MessageData_ofName(v_name_1955_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
switch(v_kind_1956_)
{
case 0:
{
lean_object* v___x_1973_; 
v___x_1973_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1966_ = v___x_1973_;
goto v___jp_1965_;
}
case 1:
{
lean_object* v___x_1974_; 
v___x_1974_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1966_ = v___x_1974_;
goto v___jp_1965_;
}
default: 
{
lean_object* v___x_1975_; 
v___x_1975_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1966_ = v___x_1975_;
goto v___jp_1965_;
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_inc_ref(v___y_1966_);
v___x_1967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___y_1966_);
v___x_1968_ = l_Lean_MessageData_ofFormat(v___x_1967_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1964_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1971_, v___y_1957_, v___y_1958_);
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1976_, lean_object* v_kind_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
uint8_t v_kind_boxed_1981_; lean_object* v_res_1982_; 
v_kind_boxed_1981_ = lean_unbox(v_kind_1977_);
v_res_1982_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1976_, v_kind_boxed_1981_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1983_, lean_object* v_a_1984_, lean_object* v_name_1985_, lean_object* v_decl_1986_, lean_object* v_stx_1987_, uint8_t v_kind_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1987_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2043_) == 0)
{
uint8_t v___x_2044_; uint8_t v___x_2045_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2044_ = 0;
v___x_2045_ = l_Lean_instBEqAttributeKind_beq(v_kind_1988_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec(v_decl_1986_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_validate_1983_);
v___x_2046_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1985_, v_kind_1988_, v___y_1989_, v___y_1990_);
return v___x_2046_;
}
else
{
v___y_2037_ = v___y_1989_;
v___y_2038_ = v___y_1990_;
goto v___jp_2036_;
}
}
else
{
lean_dec(v_decl_1986_);
lean_dec(v_name_1985_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_validate_1983_);
return v___x_2043_;
}
v___jp_1992_:
{
lean_object* v___x_1995_; 
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v_decl_1986_);
v___x_1995_ = lean_apply_4(v_validate_1983_, v_decl_1986_, v___y_1993_, v___y_1994_, lean_box(0));
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2025_; 
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_1995_, 0);
lean_dec(v_unused_2026_);
v___x_1997_ = v___x_1995_;
v_isShared_1998_ = v_isSharedCheck_2025_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v___x_1995_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2025_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v_toEnvExtension_2000_; lean_object* v_env_2001_; lean_object* v_nextMacroScope_2002_; lean_object* v_ngen_2003_; lean_object* v_auxDeclNGen_2004_; lean_object* v_traceState_2005_; lean_object* v_messages_2006_; lean_object* v_infoState_2007_; lean_object* v_snapshotTasks_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2023_; 
v___x_1999_ = lean_st_ref_take(v___y_1994_);
v_toEnvExtension_2000_ = lean_ctor_get(v_a_1984_, 0);
v_env_2001_ = lean_ctor_get(v___x_1999_, 0);
v_nextMacroScope_2002_ = lean_ctor_get(v___x_1999_, 1);
v_ngen_2003_ = lean_ctor_get(v___x_1999_, 2);
v_auxDeclNGen_2004_ = lean_ctor_get(v___x_1999_, 3);
v_traceState_2005_ = lean_ctor_get(v___x_1999_, 4);
v_messages_2006_ = lean_ctor_get(v___x_1999_, 6);
v_infoState_2007_ = lean_ctor_get(v___x_1999_, 7);
v_snapshotTasks_2008_ = lean_ctor_get(v___x_1999_, 8);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_1999_, 5);
lean_dec(v_unused_2024_);
v___x_2010_ = v___x_1999_;
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snapshotTasks_2008_);
lean_inc(v_infoState_2007_);
lean_inc(v_messages_2006_);
lean_inc(v_traceState_2005_);
lean_inc(v_auxDeclNGen_2004_);
lean_inc(v_ngen_2003_);
lean_inc(v_nextMacroScope_2002_);
lean_inc(v_env_2001_);
lean_dec(v___x_1999_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2023_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_asyncMode_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v_asyncMode_2012_ = lean_ctor_get(v_toEnvExtension_2000_, 2);
lean_inc(v_asyncMode_2012_);
lean_inc(v_decl_1986_);
v___x_2013_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1984_, v_env_2001_, v_decl_1986_, v_asyncMode_2012_, v_decl_1986_);
lean_dec(v_asyncMode_2012_);
v___x_2014_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 5, v___x_2014_);
lean_ctor_set(v___x_2010_, 0, v___x_2013_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_nextMacroScope_2002_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_ngen_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_auxDeclNGen_2004_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_traceState_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_messages_2006_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_infoState_2007_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_snapshotTasks_2008_);
v___x_2016_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2017_ = lean_st_ref_set(v___y_1994_, v___x_2016_);
v___x_2018_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2018_);
v___x_2020_ = v___x_1997_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
else
{
lean_dec(v_decl_1986_);
lean_dec_ref(v_a_1984_);
return v___x_1995_;
}
}
v___jp_2027_:
{
lean_object* v_toEnvExtension_2031_; lean_object* v_asyncMode_2032_; uint8_t v___x_2033_; 
v_toEnvExtension_2031_ = lean_ctor_get(v_a_1984_, 0);
v_asyncMode_2032_ = lean_ctor_get(v_toEnvExtension_2031_, 2);
lean_inc(v_decl_1986_);
lean_inc_ref(v___y_2028_);
v___x_2033_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2028_, v_decl_1986_, v_asyncMode_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_validate_1983_);
v___x_2034_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2028_);
v___x_2035_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1985_, v_decl_1986_, v___x_2034_, v___y_2029_, v___y_2030_);
return v___x_2035_;
}
else
{
lean_dec_ref(v___y_2028_);
lean_dec(v_name_1985_);
v___y_1993_ = v___y_2029_;
v___y_1994_ = v___y_2030_;
goto v___jp_1992_;
}
}
v___jp_2036_:
{
lean_object* v___x_2039_; lean_object* v_env_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_st_ref_get(v___y_2038_);
v_env_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc_ref(v_env_2040_);
lean_dec(v___x_2039_);
v___x_2041_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2040_, v_decl_1986_);
if (lean_obj_tag(v___x_2041_) == 0)
{
v___y_2028_ = v_env_2040_;
v___y_2029_ = v___y_2037_;
v___y_2030_ = v___y_2038_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref_known(v___x_2041_, 1);
lean_dec_ref(v_env_2040_);
lean_dec_ref(v_a_1984_);
lean_dec_ref(v_validate_1983_);
v___x_2042_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1985_, v_decl_1986_, v___y_2037_, v___y_2038_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2047_, lean_object* v_a_2048_, lean_object* v_name_2049_, lean_object* v_decl_2050_, lean_object* v_stx_2051_, lean_object* v_kind_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v_kind_boxed_2056_; lean_object* v_res_2057_; 
v_kind_boxed_2056_ = lean_unbox(v_kind_2052_);
v_res_2057_ = l_Lean_registerTagAttribute___lam__7(v_validate_2047_, v_a_2048_, v_name_2049_, v_decl_2050_, v_stx_2051_, v_kind_boxed_2056_, v___y_2053_, v___y_2054_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2057_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___f_2064_; 
v___x_2063_ = l_Lean_NameSet_empty;
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2064_, 0, v___x_2063_);
return v___f_2064_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___f_2066_; 
v___x_2065_ = l_Lean_NameSet_empty;
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2066_, 0, v___x_2065_);
return v___f_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2069_, lean_object* v_descr_2070_, lean_object* v_validate_2071_, lean_object* v_ref_2072_, uint8_t v_applicationTime_2073_, lean_object* v_asyncMode_2074_){
_start:
{
lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___f_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___f_2076_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2077_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2078_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2079_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2080_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2081_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2082_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2072_);
v___x_2083_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2083_, 0, v_ref_2072_);
lean_ctor_set(v___x_2083_, 1, v___f_2081_);
lean_ctor_set(v___x_2083_, 2, v___f_2080_);
lean_ctor_set(v___x_2083_, 3, v___f_2079_);
lean_ctor_set(v___x_2083_, 4, v___f_2078_);
lean_ctor_set(v___x_2083_, 5, v___f_2077_);
lean_ctor_set(v___x_2083_, 6, v_asyncMode_2074_);
lean_ctor_set(v___x_2083_, 7, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___f_2076_);
v___x_2085_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_n(v_a_2086_, 2);
lean_dec_ref_known(v___x_2085_, 1);
lean_inc_n(v_name_2069_, 2);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2087_, 0, v_name_2069_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2088_, 0, v_validate_2071_);
lean_closure_set(v___f_2088_, 1, v_a_2086_);
lean_closure_set(v___f_2088_, 2, v_name_2069_);
v___x_2089_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2089_, 0, v_ref_2072_);
lean_ctor_set(v___x_2089_, 1, v_name_2069_);
lean_ctor_set(v___x_2089_, 2, v_descr_2070_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*3, v_applicationTime_2073_);
v___x_2090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___f_2088_);
lean_ctor_set(v___x_2090_, 2, v___f_2087_);
lean_inc_ref(v___x_2090_);
v___x_2091_ = l_Lean_registerBuiltinAttribute(v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2099_; 
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v___x_2091_, 0);
lean_dec(v_unused_2100_);
v___x_2093_ = v___x_2091_;
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
else
{
lean_dec(v___x_2091_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2090_);
lean_ctor_set(v___x_2095_, 1, v_a_2086_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref_known(v___x_2090_, 3);
lean_dec(v_a_2086_);
v_a_2101_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2091_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2091_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_ref_2072_);
lean_dec_ref(v_validate_2071_);
lean_dec_ref(v_descr_2070_);
lean_dec(v_name_2069_);
v_a_2109_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2085_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2085_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2117_, lean_object* v_descr_2118_, lean_object* v_validate_2119_, lean_object* v_ref_2120_, lean_object* v_applicationTime_2121_, lean_object* v_asyncMode_2122_, lean_object* v_a_2123_){
_start:
{
uint8_t v_applicationTime_boxed_2124_; lean_object* v_res_2125_; 
v_applicationTime_boxed_2124_ = lean_unbox(v_applicationTime_2121_);
v_res_2125_ = l_Lean_registerTagAttribute(v_name_2117_, v_descr_2118_, v_validate_2119_, v_ref_2120_, v_applicationTime_boxed_2124_, v_asyncMode_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2126_, lean_object* v_t_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2126_, v_t_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2129_, lean_object* v_as_2130_, lean_object* v_lo_2131_, lean_object* v_hi_2132_, lean_object* v_w_2133_, lean_object* v_hlo_2134_, lean_object* v_hhi_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2129_, v_as_2130_, v_lo_2131_, v_hi_2132_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2137_, lean_object* v_as_2138_, lean_object* v_lo_2139_, lean_object* v_hi_2140_, lean_object* v_w_2141_, lean_object* v_hlo_2142_, lean_object* v_hhi_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2137_, v_as_2138_, v_lo_2139_, v_hi_2140_, v_w_2141_, v_hlo_2142_, v_hhi_2143_);
lean_dec(v_hi_2140_);
lean_dec(v_n_2137_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2145_, lean_object* v_attrName_2146_, lean_object* v_declName_2147_, lean_object* v_asyncPrefix_x3f_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2146_, v_declName_2147_, v_asyncPrefix_x3f_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_attrName_2154_, lean_object* v_declName_2155_, lean_object* v_asyncPrefix_x3f_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2153_, v_attrName_2154_, v_declName_2155_, v_asyncPrefix_x3f_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2161_, lean_object* v_attrName_2162_, lean_object* v_declName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2162_, v_declName_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_attrName_2169_, lean_object* v_declName_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2168_, v_attrName_2169_, v_declName_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, uint8_t v_kind_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2176_, v_kind_2177_, v___y_2178_, v___y_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2182_, lean_object* v_name_2183_, lean_object* v_kind_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_kind_boxed_2188_; lean_object* v_res_2189_; 
v_kind_boxed_2188_ = lean_unbox(v_kind_2184_);
v_res_2189_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2182_, v_name_2183_, v_kind_boxed_2188_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2190_, lean_object* v_lo_2191_, lean_object* v_hi_2192_, lean_object* v_hhi_2193_, lean_object* v_pivot_2194_, lean_object* v_as_2195_, lean_object* v_i_2196_, lean_object* v_k_2197_, lean_object* v_ilo_2198_, lean_object* v_ik_2199_, lean_object* v_w_2200_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2192_, v_pivot_2194_, v_as_2195_, v_i_2196_, v_k_2197_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2202_, lean_object* v_lo_2203_, lean_object* v_hi_2204_, lean_object* v_hhi_2205_, lean_object* v_pivot_2206_, lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_k_2209_, lean_object* v_ilo_2210_, lean_object* v_ik_2211_, lean_object* v_w_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2202_, v_lo_2203_, v_hi_2204_, v_hhi_2205_, v_pivot_2206_, v_as_2207_, v_i_2208_, v_k_2209_, v_ilo_2210_, v_ik_2211_, v_w_2212_);
lean_dec(v_pivot_2206_);
lean_dec(v_hi_2204_);
lean_dec(v_lo_2203_);
lean_dec(v_n_2202_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2214_, lean_object* v_decl_2215_, lean_object* v_env_2216_){
_start:
{
lean_object* v_ext_2217_; lean_object* v_toEnvExtension_2218_; lean_object* v_asyncMode_2219_; lean_object* v___x_2220_; 
v_ext_2217_ = lean_ctor_get(v_attr_2214_, 1);
lean_inc_ref(v_ext_2217_);
lean_dec_ref(v_attr_2214_);
v_toEnvExtension_2218_ = lean_ctor_get(v_ext_2217_, 0);
v_asyncMode_2219_ = lean_ctor_get(v_toEnvExtension_2218_, 2);
lean_inc(v_asyncMode_2219_);
lean_inc(v_decl_2215_);
v___x_2220_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2217_, v_env_2216_, v_decl_2215_, v_asyncMode_2219_, v_decl_2215_);
lean_dec(v_asyncMode_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2221_, lean_object* v___f_2222_, lean_object* v_____r_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_apply_1(v_modifyEnv_2221_, v___f_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2225_, lean_object* v_env_2226_, lean_object* v_decl_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_toBind_2230_, lean_object* v___f_2231_, lean_object* v_modifyEnv_2232_, lean_object* v___f_2233_, lean_object* v_____r_2234_){
_start:
{
lean_object* v_ext_2235_; lean_object* v_toEnvExtension_2236_; lean_object* v_attr_2237_; lean_object* v_asyncMode_2238_; uint8_t v___x_2239_; 
v_ext_2235_ = lean_ctor_get(v_attr_2225_, 1);
v_toEnvExtension_2236_ = lean_ctor_get(v_ext_2235_, 0);
lean_inc_ref(v_toEnvExtension_2236_);
v_attr_2237_ = lean_ctor_get(v_attr_2225_, 0);
lean_inc_ref(v_attr_2237_);
lean_dec_ref(v_attr_2225_);
v_asyncMode_2238_ = lean_ctor_get(v_toEnvExtension_2236_, 2);
lean_inc(v_asyncMode_2238_);
lean_dec_ref(v_toEnvExtension_2236_);
lean_inc(v_decl_2227_);
lean_inc_ref(v_env_2226_);
v___x_2239_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2226_, v_decl_2227_, v_asyncMode_2238_);
lean_dec(v_asyncMode_2238_);
if (v___x_2239_ == 0)
{
lean_object* v_toAttributeImplCore_2240_; lean_object* v_name_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec_ref(v___f_2233_);
lean_dec(v_modifyEnv_2232_);
v_toAttributeImplCore_2240_ = lean_ctor_get(v_attr_2237_, 0);
lean_inc_ref(v_toAttributeImplCore_2240_);
lean_dec_ref(v_attr_2237_);
v_name_2241_ = lean_ctor_get(v_toAttributeImplCore_2240_, 1);
lean_inc(v_name_2241_);
lean_dec_ref(v_toAttributeImplCore_2240_);
v___x_2242_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2226_);
v___x_2243_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2228_, v_inst_2229_, v_name_2241_, v_decl_2227_, v___x_2242_);
v___x_2244_ = lean_apply_4(v_toBind_2230_, lean_box(0), lean_box(0), v___x_2243_, v___f_2231_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; 
lean_dec_ref(v_attr_2237_);
lean_dec(v___f_2231_);
lean_dec(v_toBind_2230_);
lean_dec_ref(v_inst_2229_);
lean_dec_ref(v_inst_2228_);
lean_dec(v_decl_2227_);
lean_dec_ref(v_env_2226_);
v___x_2245_ = lean_apply_1(v_modifyEnv_2232_, v___f_2233_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2246_, lean_object* v_____r_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_apply_1(v___f_2246_, v_____r_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2249_, lean_object* v_decl_2250_, lean_object* v_inst_2251_, lean_object* v_inst_2252_, lean_object* v_toBind_2253_, lean_object* v___f_2254_, lean_object* v_modifyEnv_2255_, lean_object* v___f_2256_, lean_object* v_env_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
lean_inc_ref(v___f_2256_);
lean_inc(v_modifyEnv_2255_);
lean_inc(v___f_2254_);
lean_inc(v_toBind_2253_);
lean_inc_ref(v_inst_2252_);
lean_inc_ref(v_inst_2251_);
lean_inc(v_decl_2250_);
lean_inc_ref(v_env_2257_);
lean_inc_ref(v_attr_2249_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2258_, 0, v_attr_2249_);
lean_closure_set(v___f_2258_, 1, v_env_2257_);
lean_closure_set(v___f_2258_, 2, v_decl_2250_);
lean_closure_set(v___f_2258_, 3, v_inst_2251_);
lean_closure_set(v___f_2258_, 4, v_inst_2252_);
lean_closure_set(v___f_2258_, 5, v_toBind_2253_);
lean_closure_set(v___f_2258_, 6, v___f_2254_);
lean_closure_set(v___f_2258_, 7, v_modifyEnv_2255_);
lean_closure_set(v___f_2258_, 8, v___f_2256_);
v___x_2259_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2257_, v_decl_2250_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref(v___f_2258_);
v___x_2260_ = lean_box(0);
v___x_2261_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2249_, v_env_2257_, v_decl_2250_, v_inst_2251_, v_inst_2252_, v_toBind_2253_, v___f_2254_, v_modifyEnv_2255_, v___f_2256_, v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v_attr_2262_; lean_object* v_toAttributeImplCore_2263_; lean_object* v_name_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref_known(v___x_2259_, 1);
lean_dec_ref(v_env_2257_);
lean_dec_ref(v___f_2256_);
lean_dec(v_modifyEnv_2255_);
lean_dec(v___f_2254_);
v_attr_2262_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_attr_2262_);
lean_dec_ref(v_attr_2249_);
v_toAttributeImplCore_2263_ = lean_ctor_get(v_attr_2262_, 0);
lean_inc_ref(v_toAttributeImplCore_2263_);
lean_dec_ref(v_attr_2262_);
v_name_2264_ = lean_ctor_get(v_toAttributeImplCore_2263_, 1);
lean_inc(v_name_2264_);
lean_dec_ref(v_toAttributeImplCore_2263_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2265_, 0, v___f_2258_);
v___x_2266_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2251_, v_inst_2252_, v_name_2264_, v_decl_2250_);
v___x_2267_ = lean_apply_4(v_toBind_2253_, lean_box(0), lean_box(0), v___x_2266_, v___f_2265_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_attr_2271_, lean_object* v_decl_2272_){
_start:
{
lean_object* v_toBind_2273_; lean_object* v_getEnv_2274_; lean_object* v_modifyEnv_2275_; lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; 
v_toBind_2273_ = lean_ctor_get(v_inst_2268_, 1);
lean_inc_n(v_toBind_2273_, 2);
v_getEnv_2274_ = lean_ctor_get(v_inst_2270_, 0);
lean_inc(v_getEnv_2274_);
v_modifyEnv_2275_ = lean_ctor_get(v_inst_2270_, 1);
lean_inc_n(v_modifyEnv_2275_, 2);
lean_dec_ref(v_inst_2270_);
lean_inc(v_decl_2272_);
lean_inc_ref(v_attr_2271_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2276_, 0, v_attr_2271_);
lean_closure_set(v___f_2276_, 1, v_decl_2272_);
lean_inc_ref(v___f_2276_);
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2277_, 0, v_modifyEnv_2275_);
lean_closure_set(v___f_2277_, 1, v___f_2276_);
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2278_, 0, v_attr_2271_);
lean_closure_set(v___f_2278_, 1, v_decl_2272_);
lean_closure_set(v___f_2278_, 2, v_inst_2268_);
lean_closure_set(v___f_2278_, 3, v_inst_2269_);
lean_closure_set(v___f_2278_, 4, v_toBind_2273_);
lean_closure_set(v___f_2278_, 5, v___f_2277_);
lean_closure_set(v___f_2278_, 6, v_modifyEnv_2275_);
lean_closure_set(v___f_2278_, 7, v___f_2276_);
v___x_2279_ = lean_apply_4(v_toBind_2273_, lean_box(0), lean_box(0), v_getEnv_2274_, v___f_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_attr_2284_, lean_object* v_decl_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2281_, v_inst_2282_, v_inst_2283_, v_attr_2284_, v_decl_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2287_, lean_object* v_k_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_m_2293_; lean_object* v_a_2294_; uint8_t v___x_2295_; 
v___x_2291_ = lean_nat_add(v_x_2289_, v_x_2290_);
v___x_2292_ = lean_unsigned_to_nat(1u);
v_m_2293_ = lean_nat_shiftr(v___x_2291_, v___x_2292_);
lean_dec(v___x_2291_);
v_a_2294_ = lean_array_fget_borrowed(v_as_2287_, v_m_2293_);
v___x_2295_ = l_Lean_Name_quickLt(v_a_2294_, v_k_2288_);
if (v___x_2295_ == 0)
{
uint8_t v___x_2296_; 
lean_dec(v_x_2290_);
v___x_2296_ = l_Lean_Name_quickLt(v_k_2288_, v_a_2294_);
if (v___x_2296_ == 0)
{
uint8_t v___x_2297_; 
lean_dec(v_m_2293_);
lean_dec(v_x_2289_);
v___x_2297_ = 1;
return v___x_2297_;
}
else
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_nat_dec_eq(v_m_2293_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_nat_sub(v_m_2293_, v___x_2292_);
lean_dec(v_m_2293_);
v___x_2301_ = lean_nat_dec_lt(v___x_2300_, v_x_2289_);
if (v___x_2301_ == 0)
{
v_x_2290_ = v___x_2300_;
goto _start;
}
else
{
lean_dec(v___x_2300_);
lean_dec(v_x_2289_);
return v___x_2295_;
}
}
else
{
lean_dec(v_m_2293_);
lean_dec(v_x_2289_);
return v___x_2295_;
}
}
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
lean_dec(v_x_2289_);
v___x_2303_ = lean_nat_add(v_m_2293_, v___x_2292_);
lean_dec(v_m_2293_);
v___x_2304_ = lean_nat_dec_le(v___x_2303_, v_x_2290_);
if (v___x_2304_ == 0)
{
lean_dec(v___x_2303_);
lean_dec(v_x_2290_);
return v___x_2304_;
}
else
{
v_x_2289_ = v___x_2303_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2306_, lean_object* v_k_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
uint8_t v_res_2310_; lean_object* v_r_2311_; 
v_res_2310_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2306_, v_k_2307_, v_x_2308_, v_x_2309_);
lean_dec(v_k_2307_);
lean_dec_ref(v_as_2306_);
v_r_2311_ = lean_box(v_res_2310_);
return v_r_2311_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2312_, lean_object* v_env_2313_, lean_object* v_decl_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_box(1);
v___x_2316_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2313_, v_decl_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_ext_2317_; lean_object* v_toEnvExtension_2318_; lean_object* v_asyncMode_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_ext_2317_ = lean_ctor_get(v_attr_2312_, 1);
v_toEnvExtension_2318_ = lean_ctor_get(v_ext_2317_, 0);
v_asyncMode_2319_ = lean_ctor_get(v_toEnvExtension_2318_, 2);
lean_inc(v_decl_2314_);
v___x_2320_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2315_, v_ext_2317_, v_env_2313_, v_asyncMode_2319_, v_decl_2314_);
v___x_2321_ = l_Lean_NameSet_contains(v___x_2320_, v_decl_2314_);
lean_dec(v_decl_2314_);
lean_dec(v___x_2320_);
return v___x_2321_;
}
else
{
lean_object* v_val_2322_; lean_object* v_ext_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v_val_2322_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___x_2316_, 1);
v_ext_2323_ = lean_ctor_get(v_attr_2312_, 1);
v___x_2324_ = 0;
v___x_2325_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2315_, v_ext_2323_, v_env_2313_, v_val_2322_, v___x_2324_);
lean_dec(v_val_2322_);
lean_dec_ref(v_env_2313_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_array_get_size(v___x_2325_);
v___x_2328_ = lean_nat_dec_lt(v___x_2326_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec(v_decl_2314_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_nat_sub(v___x_2327_, v___x_2329_);
v___x_2331_ = lean_nat_dec_le(v___x_2326_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v___x_2330_);
lean_dec_ref(v___x_2325_);
lean_dec(v_decl_2314_);
return v___x_2331_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2325_, v_decl_2314_, v___x_2326_, v___x_2330_);
lean_dec(v_decl_2314_);
lean_dec_ref(v___x_2325_);
return v___x_2332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2333_, lean_object* v_env_2334_, lean_object* v_decl_2335_){
_start:
{
uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_res_2336_ = l_Lean_TagAttribute_hasTag(v_attr_2333_, v_env_2334_, v_decl_2335_);
lean_dec_ref(v_attr_2333_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2338_, lean_object* v_k_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2338_, v_k_2339_, v_x_2340_, v_x_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2344_, lean_object* v_k_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2344_, v_k_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
lean_dec(v_k_2345_);
lean_dec_ref(v_as_2344_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2356_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_x_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2360_, lean_object* v_x_2361_){
_start:
{
lean_inc_ref(v_s_2360_);
return v_s_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2362_, v_x_2363_);
lean_dec_ref(v_x_2363_);
lean_dec_ref(v_s_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2372_, v_x_2373_);
lean_dec_ref(v_x_2373_);
lean_dec_ref(v_x_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2377_);
lean_dec_ref(v_x_2377_);
return v_res_2378_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2384_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2387_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2388_);
lean_ctor_set(v___x_2390_, 2, v___f_2387_);
lean_ctor_set(v___x_2390_, 3, v___f_2386_);
lean_ctor_set(v___x_2390_, 4, v___f_2385_);
lean_ctor_set(v___x_2390_, 5, v___f_2384_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = 0;
v___x_2392_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2393_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2394_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___x_2392_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*2, v___x_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2400_, lean_object* v_p_2401_){
_start:
{
lean_object* v_fst_2402_; lean_object* v_snd_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2420_; 
v_fst_2402_ = lean_ctor_get(v_x_2400_, 0);
v_snd_2403_ = lean_ctor_get(v_x_2400_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_x_2400_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2405_ = v_x_2400_;
v_isShared_2406_ = v_isSharedCheck_2420_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_snd_2403_);
lean_inc(v_fst_2402_);
lean_dec(v_x_2400_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2420_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_fst_2407_ = lean_ctor_get(v_p_2401_, 0);
v_snd_2408_ = lean_ctor_get(v_p_2401_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_p_2401_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v_p_2401_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snd_2408_);
lean_inc(v_fst_2407_);
lean_dec(v_p_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
lean_inc(v_fst_2407_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 1);
lean_ctor_set(v___x_2405_, 1, v_fst_2402_);
lean_ctor_set(v___x_2405_, 0, v_fst_2407_);
v___x_2413_ = v___x_2405_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_fst_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_fst_2402_);
v___x_2413_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2407_, v_snd_2408_, v_snd_2403_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v___x_2414_);
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_k_2423_ = lean_ctor_get(v_x_2422_, 1);
v_v_2424_ = lean_ctor_get(v_x_2422_, 2);
v_l_2425_ = lean_ctor_get(v_x_2422_, 3);
v_r_2426_ = lean_ctor_get(v_x_2422_, 4);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2421_, v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_k_2423_);
lean_ctor_set(v___x_2428_, 1, v_v_2424_);
v___x_2429_ = lean_array_push(v___x_2427_, v___x_2428_);
v_init_2421_ = v___x_2429_;
v_x_2422_ = v_r_2426_;
goto _start;
}
else
{
return v_init_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2431_, lean_object* v_x_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2431_, v_x_2432_);
lean_dec(v_x_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2434_, lean_object* v_as_2435_, size_t v_i_2436_, size_t v_stop_2437_, lean_object* v_b_2438_){
_start:
{
lean_object* v___y_2440_; uint8_t v___x_2444_; 
v___x_2444_ = lean_usize_dec_eq(v_i_2436_, v_stop_2437_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_array_uget_borrowed(v_as_2435_, v_i_2436_);
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2434_, v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
v___y_2440_ = v_b_2438_;
goto v___jp_2439_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v___x_2446_, 1);
lean_inc(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
lean_ctor_set(v___x_2448_, 1, v_val_2447_);
v___x_2449_ = lean_array_push(v_b_2438_, v___x_2448_);
v___y_2440_ = v___x_2449_;
goto v___jp_2439_;
}
}
else
{
return v_b_2438_;
}
v___jp_2439_:
{
size_t v___x_2441_; size_t v___x_2442_; 
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2436_, v___x_2441_);
v_i_2436_ = v___x_2442_;
v_b_2438_ = v___y_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2450_, lean_object* v_as_2451_, lean_object* v_i_2452_, lean_object* v_stop_2453_, lean_object* v_b_2454_){
_start:
{
size_t v_i_boxed_2455_; size_t v_stop_boxed_2456_; lean_object* v_res_2457_; 
v_i_boxed_2455_ = lean_unbox_usize(v_i_2452_);
lean_dec(v_i_2452_);
v_stop_boxed_2456_ = lean_unbox_usize(v_stop_2453_);
lean_dec(v_stop_2453_);
v_res_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2450_, v_as_2451_, v_i_boxed_2455_, v_stop_boxed_2456_, v_b_2454_);
lean_dec_ref(v_as_2451_);
lean_dec(v_snd_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2458_, lean_object* v_as_2459_, lean_object* v_start_2460_, lean_object* v_stop_2461_){
_start:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2463_ = lean_nat_dec_lt(v_start_2460_, v_stop_2461_);
if (v___x_2463_ == 0)
{
return v___x_2462_;
}
else
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_array_get_size(v_as_2459_);
v___x_2465_ = lean_nat_dec_le(v_stop_2461_, v___x_2464_);
if (v___x_2465_ == 0)
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_nat_dec_lt(v_start_2460_, v___x_2464_);
if (v___x_2466_ == 0)
{
return v___x_2462_;
}
else
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_usize_of_nat(v_start_2460_);
v___x_2468_ = lean_usize_of_nat(v___x_2464_);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2458_, v_as_2459_, v___x_2467_, v___x_2468_, v___x_2462_);
return v___x_2469_;
}
}
else
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_usize_of_nat(v_start_2460_);
v___x_2471_ = lean_usize_of_nat(v_stop_2461_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2458_, v_as_2459_, v___x_2470_, v___x_2471_, v___x_2462_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2473_, lean_object* v_as_2474_, lean_object* v_start_2475_, lean_object* v_stop_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2473_, v_as_2474_, v_start_2475_, v_stop_2476_);
lean_dec(v_stop_2476_);
lean_dec(v_start_2475_);
lean_dec_ref(v_as_2474_);
lean_dec(v_snd_2473_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2478_, lean_object* v_pivot_2479_, lean_object* v_as_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_nat_dec_lt(v_k_2482_, v_hi_2478_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v_k_2482_);
v___x_2484_ = lean_array_fswap(v_as_2480_, v_i_2481_, v_hi_2478_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_i_2481_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; lean_object* v_fst_2487_; lean_object* v_fst_2488_; uint8_t v___x_2489_; 
v___x_2486_ = lean_array_fget_borrowed(v_as_2480_, v_k_2482_);
v_fst_2487_ = lean_ctor_get(v___x_2486_, 0);
v_fst_2488_ = lean_ctor_get(v_pivot_2479_, 0);
v___x_2489_ = l_Lean_Name_quickLt(v_fst_2487_, v_fst_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_k_2482_, v___x_2490_);
lean_dec(v_k_2482_);
v_k_2482_ = v___x_2491_;
goto _start;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2493_ = lean_array_fswap(v_as_2480_, v_i_2481_, v_k_2482_);
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = lean_nat_add(v_i_2481_, v___x_2494_);
lean_dec(v_i_2481_);
v___x_2496_ = lean_nat_add(v_k_2482_, v___x_2494_);
lean_dec(v_k_2482_);
v_as_2480_ = v___x_2493_;
v_i_2481_ = v___x_2495_;
v_k_2482_ = v___x_2496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2498_, lean_object* v_pivot_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2498_, v_pivot_2499_, v_as_2500_, v_i_2501_, v_k_2502_);
lean_dec_ref(v_pivot_2499_);
lean_dec(v_hi_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2504_, lean_object* v_b_2505_){
_start:
{
lean_object* v_fst_2506_; lean_object* v_fst_2507_; uint8_t v___x_2508_; 
v_fst_2506_ = lean_ctor_get(v_a_2504_, 0);
v_fst_2507_ = lean_ctor_get(v_b_2505_, 0);
v___x_2508_ = l_Lean_Name_quickLt(v_fst_2506_, v_fst_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2509_, lean_object* v_b_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2509_, v_b_2510_);
lean_dec_ref(v_b_2510_);
lean_dec_ref(v_a_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2513_, lean_object* v_as_2514_, lean_object* v_lo_2515_, lean_object* v_hi_2516_){
_start:
{
lean_object* v___y_2518_; uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_lt(v_lo_2515_, v_hi_2516_);
if (v___x_2528_ == 0)
{
lean_dec(v_lo_2515_);
return v_as_2514_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_mid_2531_; lean_object* v___y_2533_; lean_object* v___y_2539_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2529_ = lean_nat_add(v_lo_2515_, v_hi_2516_);
v___x_2530_ = lean_unsigned_to_nat(1u);
v_mid_2531_ = lean_nat_shiftr(v___x_2529_, v___x_2530_);
lean_dec(v___x_2529_);
v___x_2544_ = lean_array_fget_borrowed(v_as_2514_, v_mid_2531_);
v___x_2545_ = lean_array_fget_borrowed(v_as_2514_, v_lo_2515_);
v___x_2546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
v___y_2539_ = v_as_2514_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_array_fswap(v_as_2514_, v_lo_2515_, v_mid_2531_);
v___y_2539_ = v___x_2547_;
goto v___jp_2538_;
}
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_array_fget_borrowed(v___y_2533_, v_mid_2531_);
v___x_2535_ = lean_array_fget_borrowed(v___y_2533_, v_hi_2516_);
v___x_2536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_dec(v_mid_2531_);
v___y_2518_ = v___y_2533_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_array_fswap(v___y_2533_, v_mid_2531_, v_hi_2516_);
lean_dec(v_mid_2531_);
v___y_2518_ = v___x_2537_;
goto v___jp_2517_;
}
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2540_ = lean_array_fget_borrowed(v___y_2539_, v_hi_2516_);
v___x_2541_ = lean_array_fget_borrowed(v___y_2539_, v_lo_2515_);
v___x_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
v___y_2533_ = v___y_2539_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_fswap(v___y_2539_, v_lo_2515_, v_hi_2516_);
v___y_2533_ = v___x_2543_;
goto v___jp_2532_;
}
}
}
v___jp_2517_:
{
lean_object* v_pivot_2519_; lean_object* v___x_2520_; lean_object* v_fst_2521_; lean_object* v_snd_2522_; uint8_t v___x_2523_; 
v_pivot_2519_ = lean_array_fget(v___y_2518_, v_hi_2516_);
lean_inc_n(v_lo_2515_, 2);
v___x_2520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2516_, v_pivot_2519_, v___y_2518_, v_lo_2515_, v_lo_2515_);
lean_dec(v_pivot_2519_);
v_fst_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_fst_2521_);
v_snd_2522_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_snd_2522_);
lean_dec_ref(v___x_2520_);
v___x_2523_ = lean_nat_dec_le(v_hi_2516_, v_fst_2521_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2513_, v_snd_2522_, v_lo_2515_, v_fst_2521_);
v___x_2525_ = lean_unsigned_to_nat(1u);
v___x_2526_ = lean_nat_add(v_fst_2521_, v___x_2525_);
lean_dec(v_fst_2521_);
v_as_2514_ = v___x_2524_;
v_lo_2515_ = v___x_2526_;
goto _start;
}
else
{
lean_dec(v_fst_2521_);
lean_dec(v_lo_2515_);
return v_snd_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2548_, lean_object* v_as_2549_, lean_object* v_lo_2550_, lean_object* v_hi_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2548_, v_as_2549_, v_lo_2550_, v_hi_2551_);
lean_dec(v_hi_2551_);
lean_dec(v_n_2548_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2553_, lean_object* v_env_2554_, lean_object* v_as_2555_, size_t v_i_2556_, size_t v_stop_2557_, lean_object* v_b_2558_){
_start:
{
lean_object* v___y_2560_; uint8_t v___x_2564_; 
v___x_2564_ = lean_usize_dec_eq(v_i_2556_, v_stop_2557_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2565_ = lean_array_uget_borrowed(v_as_2555_, v_i_2556_);
v_fst_2566_ = lean_ctor_get(v___x_2565_, 0);
v_snd_2567_ = lean_ctor_get(v___x_2565_, 1);
lean_inc_ref(v_filterExport_2553_);
lean_inc(v_snd_2567_);
lean_inc(v_fst_2566_);
lean_inc_ref(v_env_2554_);
v___x_2568_ = lean_apply_3(v_filterExport_2553_, v_env_2554_, v_fst_2566_, v_snd_2567_);
v___x_2569_ = lean_unbox(v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2560_ = v_b_2558_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2570_; 
lean_inc(v___x_2565_);
v___x_2570_ = lean_array_push(v_b_2558_, v___x_2565_);
v___y_2560_ = v___x_2570_;
goto v___jp_2559_;
}
}
else
{
lean_dec_ref(v_env_2554_);
lean_dec_ref(v_filterExport_2553_);
return v_b_2558_;
}
v___jp_2559_:
{
size_t v___x_2561_; size_t v___x_2562_; 
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_add(v_i_2556_, v___x_2561_);
v_i_2556_ = v___x_2562_;
v_b_2558_ = v___y_2560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2571_, lean_object* v_env_2572_, lean_object* v_as_2573_, lean_object* v_i_2574_, lean_object* v_stop_2575_, lean_object* v_b_2576_){
_start:
{
size_t v_i_boxed_2577_; size_t v_stop_boxed_2578_; lean_object* v_res_2579_; 
v_i_boxed_2577_ = lean_unbox_usize(v_i_2574_);
lean_dec(v_i_2574_);
v_stop_boxed_2578_ = lean_unbox_usize(v_stop_2575_);
lean_dec(v_stop_2575_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2571_, v_env_2572_, v_as_2573_, v_i_boxed_2577_, v_stop_boxed_2578_, v_b_2576_);
lean_dec_ref(v_as_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2580_, uint8_t v_preserveOrder_2581_, lean_object* v_env_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v___y_2585_; 
if (v_preserveOrder_2581_ == 0)
{
lean_object* v_snd_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_r_2604_; lean_object* v___x_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___x_2610_; 
v_snd_2601_ = lean_ctor_get(v_x_2583_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v_x_2583_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2604_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2603_, v_snd_2601_);
lean_dec(v_snd_2601_);
v___x_2605_ = lean_array_get_size(v_r_2604_);
v___x_2610_ = lean_nat_dec_eq(v___x_2605_, v___x_2602_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___y_2614_; uint8_t v___x_2616_; 
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_sub(v___x_2605_, v___x_2611_);
v___x_2616_ = lean_nat_dec_le(v___x_2602_, v___x_2612_);
if (v___x_2616_ == 0)
{
lean_inc(v___x_2612_);
v___y_2614_ = v___x_2612_;
goto v___jp_2613_;
}
else
{
v___y_2614_ = v___x_2602_;
goto v___jp_2613_;
}
v___jp_2613_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_nat_dec_le(v___y_2614_, v___x_2612_);
if (v___x_2615_ == 0)
{
lean_dec(v___x_2612_);
lean_inc(v___y_2614_);
v___y_2607_ = v___y_2614_;
v___y_2608_ = v___y_2614_;
goto v___jp_2606_;
}
else
{
v___y_2607_ = v___y_2614_;
v___y_2608_ = v___x_2612_;
goto v___jp_2606_;
}
}
}
else
{
v___y_2585_ = v_r_2604_;
goto v___jp_2584_;
}
v___jp_2606_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2605_, v_r_2604_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
v___y_2585_ = v___x_2609_;
goto v___jp_2584_;
}
}
else
{
lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_fst_2617_ = lean_ctor_get(v_x_2583_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v_x_2583_, 1);
lean_inc(v_snd_2618_);
lean_dec_ref(v_x_2583_);
v___x_2619_ = lean_array_mk(v_fst_2617_);
v___x_2620_ = l_Array_reverse___redArg(v___x_2619_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = lean_array_get_size(v___x_2620_);
v___x_2623_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2618_, v___x_2620_, v___x_2621_, v___x_2622_);
lean_dec_ref(v___x_2620_);
lean_dec(v_snd_2618_);
v___y_2585_ = v___x_2623_;
goto v___jp_2584_;
}
v___jp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_array_get_size(v___y_2585_);
v___x_2588_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2589_ = lean_nat_dec_lt(v___x_2586_, v___x_2587_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v_env_2582_);
lean_dec_ref(v_filterExport_2580_);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
lean_ctor_set(v___x_2590_, 2, v___y_2585_);
return v___x_2590_;
}
else
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_le(v___x_2587_, v___x_2587_);
if (v___x_2591_ == 0)
{
if (v___x_2589_ == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref(v_env_2582_);
lean_dec_ref(v_filterExport_2580_);
v___x_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2588_);
lean_ctor_set(v___x_2592_, 1, v___x_2588_);
lean_ctor_set(v___x_2592_, 2, v___y_2585_);
return v___x_2592_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = lean_usize_of_nat(v___x_2587_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2580_, v_env_2582_, v___y_2585_, v___x_2593_, v___x_2594_, v___x_2588_);
lean_inc_ref(v___x_2595_);
v___x_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_ctor_set(v___x_2596_, 2, v___y_2585_);
return v___x_2596_;
}
}
else
{
size_t v___x_2597_; size_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = lean_usize_of_nat(v___x_2587_);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2580_, v_env_2582_, v___y_2585_, v___x_2597_, v___x_2598_, v___x_2588_);
lean_inc_ref(v___x_2599_);
v___x_2600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
lean_ctor_set(v___x_2600_, 2, v___y_2585_);
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2624_, lean_object* v_preserveOrder_2625_, lean_object* v_env_2626_, lean_object* v_x_2627_){
_start:
{
uint8_t v_preserveOrder_boxed_2628_; lean_object* v_res_2629_; 
v_preserveOrder_boxed_2628_ = lean_unbox(v_preserveOrder_2625_);
v_res_2629_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2624_, v_preserveOrder_boxed_2628_, v_env_2626_, v_x_2627_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2639_){
_start:
{
lean_object* v_snd_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2654_; 
v_snd_2640_ = lean_ctor_get(v_x_2639_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_x_2639_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_x_2639_, 0);
lean_dec(v_unused_2655_);
v___x_2642_ = v_x_2639_;
v_isShared_2643_ = v_isSharedCheck_2654_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snd_2640_);
lean_dec(v_x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2654_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___y_2646_; 
v___x_2644_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2640_) == 0)
{
lean_object* v_size_2652_; 
v_size_2652_ = lean_ctor_get(v_snd_2640_, 0);
lean_inc(v_size_2652_);
lean_dec_ref_known(v_snd_2640_, 5);
v___y_2646_ = v_size_2652_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___y_2646_ = v___x_2653_;
goto v___jp_2645_;
}
v___jp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = l_Nat_reprFast(v___y_2646_);
v___x_2648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 5);
lean_ctor_set(v___x_2642_, 1, v___x_2648_);
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2650_ = v___x_2642_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2658_);
lean_dec_ref(v_x_2658_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2666_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2671_, v_x_2672_, v___y_2673_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_x_2672_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2686_, uint8_t v_preserveOrder_2687_, lean_object* v_filterExport_2688_){
_start:
{
lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___f_2690_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2691_ = lean_box(v_preserveOrder_2687_);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2692_, 0, v_filterExport_2688_);
lean_closure_set(v___f_2692_, 1, v___x_2691_);
v___f_2693_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2697_ = lean_box(2);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2699_, 0, v_ref_2686_);
lean_ctor_set(v___x_2699_, 1, v___f_2695_);
lean_ctor_set(v___x_2699_, 2, v___f_2696_);
lean_ctor_set(v___x_2699_, 3, v___f_2690_);
lean_ctor_set(v___x_2699_, 4, v___f_2692_);
lean_ctor_set(v___x_2699_, 5, v___f_2693_);
lean_ctor_set(v___x_2699_, 6, v___x_2697_);
lean_ctor_set(v___x_2699_, 7, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___f_2694_);
v___x_2701_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2702_, lean_object* v_preserveOrder_2703_, lean_object* v_filterExport_2704_, lean_object* v_a_2705_){
_start:
{
uint8_t v_preserveOrder_boxed_2706_; lean_object* v_res_2707_; 
v_preserveOrder_boxed_2706_ = lean_unbox(v_preserveOrder_2703_);
v_res_2707_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2702_, v_preserveOrder_boxed_2706_, v_filterExport_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2708_, lean_object* v_ref_2709_, uint8_t v_preserveOrder_2710_, lean_object* v_filterExport_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2709_, v_preserveOrder_2710_, v_filterExport_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_ref_2715_, lean_object* v_preserveOrder_2716_, lean_object* v_filterExport_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_preserveOrder_boxed_2719_; lean_object* v_res_2720_; 
v_preserveOrder_boxed_2719_ = lean_unbox(v_preserveOrder_2716_);
v_res_2720_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2714_, v_ref_2715_, v_preserveOrder_boxed_2719_, v_filterExport_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_filterExport_2722_, lean_object* v_env_2723_, lean_object* v_as_2724_, size_t v_i_2725_, size_t v_stop_2726_, lean_object* v_b_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2722_, v_env_2723_, v_as_2724_, v_i_2725_, v_stop_2726_, v_b_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_filterExport_2730_, lean_object* v_env_2731_, lean_object* v_as_2732_, lean_object* v_i_2733_, lean_object* v_stop_2734_, lean_object* v_b_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; lean_object* v_res_2738_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2734_);
lean_dec(v_stop_2734_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2729_, v_filterExport_2730_, v_env_2731_, v_as_2732_, v_i_boxed_2736_, v_stop_boxed_2737_, v_b_2735_);
lean_dec_ref(v_as_2732_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2739_, lean_object* v_t_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2739_, v_t_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2742_, lean_object* v_t_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2742_, v_t_2743_);
lean_dec(v_t_2743_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2745_, lean_object* v_init_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2746_, v_t_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2749_, lean_object* v_init_2750_, lean_object* v_t_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2749_, v_init_2750_, v_t_2751_);
lean_dec(v_t_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2753_, lean_object* v_n_2754_, lean_object* v_as_2755_, lean_object* v_lo_2756_, lean_object* v_hi_2757_, lean_object* v_w_2758_, lean_object* v_hlo_2759_, lean_object* v_hhi_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2754_, v_as_2755_, v_lo_2756_, v_hi_2757_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_n_2763_, lean_object* v_as_2764_, lean_object* v_lo_2765_, lean_object* v_hi_2766_, lean_object* v_w_2767_, lean_object* v_hlo_2768_, lean_object* v_hhi_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2762_, v_n_2763_, v_as_2764_, v_lo_2765_, v_hi_2766_, v_w_2767_, v_hlo_2768_, v_hhi_2769_);
lean_dec(v_hi_2766_);
lean_dec(v_n_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2771_, lean_object* v_snd_2772_, lean_object* v_as_2773_, lean_object* v_start_2774_, lean_object* v_stop_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2772_, v_as_2773_, v_start_2774_, v_stop_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_snd_2778_, lean_object* v_as_2779_, lean_object* v_start_2780_, lean_object* v_stop_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2777_, v_snd_2778_, v_as_2779_, v_start_2780_, v_stop_2781_);
lean_dec(v_stop_2781_);
lean_dec(v_start_2780_);
lean_dec_ref(v_as_2779_);
lean_dec(v_snd_2778_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2783_, lean_object* v_init_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_init_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2787_, v_init_2788_, v_x_2789_);
lean_dec(v_x_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2791_, lean_object* v_n_2792_, lean_object* v_lo_2793_, lean_object* v_hi_2794_, lean_object* v_hhi_2795_, lean_object* v_pivot_2796_, lean_object* v_as_2797_, lean_object* v_i_2798_, lean_object* v_k_2799_, lean_object* v_ilo_2800_, lean_object* v_ik_2801_, lean_object* v_w_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2794_, v_pivot_2796_, v_as_2797_, v_i_2798_, v_k_2799_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_lo_2806_, lean_object* v_hi_2807_, lean_object* v_hhi_2808_, lean_object* v_pivot_2809_, lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_k_2812_, lean_object* v_ilo_2813_, lean_object* v_ik_2814_, lean_object* v_w_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2804_, v_n_2805_, v_lo_2806_, v_hi_2807_, v_hhi_2808_, v_pivot_2809_, v_as_2810_, v_i_2811_, v_k_2812_, v_ilo_2813_, v_ik_2814_, v_w_2815_);
lean_dec_ref(v_pivot_2809_);
lean_dec(v_hi_2807_);
lean_dec(v_lo_2806_);
lean_dec(v_n_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2817_, lean_object* v_snd_2818_, lean_object* v_as_2819_, size_t v_i_2820_, size_t v_stop_2821_, lean_object* v_b_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2818_, v_as_2819_, v_i_2820_, v_stop_2821_, v_b_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_snd_2825_, lean_object* v_as_2826_, lean_object* v_i_2827_, lean_object* v_stop_2828_, lean_object* v_b_2829_){
_start:
{
size_t v_i_boxed_2830_; size_t v_stop_boxed_2831_; lean_object* v_res_2832_; 
v_i_boxed_2830_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_stop_boxed_2831_ = lean_unbox_usize(v_stop_2828_);
lean_dec(v_stop_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2824_, v_snd_2825_, v_as_2826_, v_i_boxed_2830_, v_stop_boxed_2831_, v_b_2829_);
lean_dec_ref(v_as_2826_);
lean_dec(v_snd_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v_nextMacroScope_2837_; lean_object* v_ngen_2838_; lean_object* v_auxDeclNGen_2839_; lean_object* v_traceState_2840_; lean_object* v_messages_2841_; lean_object* v_infoState_2842_; lean_object* v_snapshotTasks_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v___x_2836_ = lean_st_ref_take(v___y_2834_);
v_nextMacroScope_2837_ = lean_ctor_get(v___x_2836_, 1);
v_ngen_2838_ = lean_ctor_get(v___x_2836_, 2);
v_auxDeclNGen_2839_ = lean_ctor_get(v___x_2836_, 3);
v_traceState_2840_ = lean_ctor_get(v___x_2836_, 4);
v_messages_2841_ = lean_ctor_get(v___x_2836_, 6);
v_infoState_2842_ = lean_ctor_get(v___x_2836_, 7);
v_snapshotTasks_2843_ = lean_ctor_get(v___x_2836_, 8);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2855_ = lean_ctor_get(v___x_2836_, 5);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2856_);
v___x_2845_ = v___x_2836_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_snapshotTasks_2843_);
lean_inc(v_infoState_2842_);
lean_inc(v_messages_2841_);
lean_inc(v_traceState_2840_);
lean_inc(v_auxDeclNGen_2839_);
lean_inc(v_ngen_2838_);
lean_inc(v_nextMacroScope_2837_);
lean_dec(v___x_2836_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 5, v___x_2847_);
lean_ctor_set(v___x_2845_, 0, v_env_2833_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_env_2833_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_nextMacroScope_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_ngen_2838_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_auxDeclNGen_2839_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_traceState_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 5, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 6, v_messages_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 7, v_infoState_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 8, v_snapshotTasks_2843_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_st_ref_set(v___y_2834_, v___x_2849_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2857_, v___y_2858_);
lean_dec(v___y_2858_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2861_, v___y_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2871_, lean_object* v_ext_2872_, lean_object* v_afterSet_2873_, lean_object* v_toAttributeImplCore_2874_, lean_object* v_decl_2875_, lean_object* v_stx_2876_, uint8_t v_kind_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 0;
v___x_2936_ = l_Lean_instBEqAttributeKind_beq(v_kind_2877_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v_name_2937_; lean_object* v___x_2938_; 
lean_dec(v_stx_2876_);
lean_dec(v_decl_2875_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
lean_dec_ref(v_getParam_2871_);
v_name_2937_ = lean_ctor_get(v_toAttributeImplCore_2874_, 1);
lean_inc(v_name_2937_);
lean_dec_ref(v_toAttributeImplCore_2874_);
v___x_2938_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2937_, v_kind_2877_, v___y_2878_, v___y_2879_);
return v___x_2938_;
}
else
{
goto v___jp_2929_;
}
v___jp_2881_:
{
if (v___y_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec_ref(v___y_2883_);
v___x_2887_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2884_, v___y_2882_);
return v___x_2887_;
}
else
{
lean_dec_ref(v___y_2884_);
return v___y_2883_;
}
}
v___jp_2888_:
{
lean_object* v___x_2892_; 
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v_decl_2875_);
v___x_2892_ = lean_apply_5(v_getParam_2871_, v_decl_2875_, v_stx_2876_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v_toEnvExtension_2895_; lean_object* v_env_2896_; lean_object* v_nextMacroScope_2897_; lean_object* v_ngen_2898_; lean_object* v_auxDeclNGen_2899_; lean_object* v_traceState_2900_; lean_object* v_messages_2901_; lean_object* v_infoState_2902_; lean_object* v_snapshotTasks_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2919_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = lean_st_ref_take(v___y_2891_);
v_toEnvExtension_2895_ = lean_ctor_get(v_ext_2872_, 0);
v_env_2896_ = lean_ctor_get(v___x_2894_, 0);
v_nextMacroScope_2897_ = lean_ctor_get(v___x_2894_, 1);
v_ngen_2898_ = lean_ctor_get(v___x_2894_, 2);
v_auxDeclNGen_2899_ = lean_ctor_get(v___x_2894_, 3);
v_traceState_2900_ = lean_ctor_get(v___x_2894_, 4);
v_messages_2901_ = lean_ctor_get(v___x_2894_, 6);
v_infoState_2902_ = lean_ctor_get(v___x_2894_, 7);
v_snapshotTasks_2903_ = lean_ctor_get(v___x_2894_, 8);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2894_, 5);
lean_dec(v_unused_2920_);
v___x_2905_ = v___x_2894_;
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snapshotTasks_2903_);
lean_inc(v_infoState_2902_);
lean_inc(v_messages_2901_);
lean_inc(v_traceState_2900_);
lean_inc(v_auxDeclNGen_2899_);
lean_inc(v_ngen_2898_);
lean_inc(v_nextMacroScope_2897_);
lean_inc(v_env_2896_);
lean_dec(v___x_2894_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_asyncMode_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_asyncMode_2907_ = lean_ctor_get(v_toEnvExtension_2895_, 2);
lean_inc(v_asyncMode_2907_);
lean_inc(v_a_2893_);
lean_inc_n(v_decl_2875_, 2);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_decl_2875_);
lean_ctor_set(v___x_2908_, 1, v_a_2893_);
v___x_2909_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2872_, v_env_2896_, v___x_2908_, v_asyncMode_2907_, v_decl_2875_);
lean_dec(v_asyncMode_2907_);
v___x_2910_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 5, v___x_2910_);
lean_ctor_set(v___x_2905_, 0, v___x_2909_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_nextMacroScope_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_ngen_2898_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_auxDeclNGen_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_traceState_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v_messages_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_infoState_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_snapshotTasks_2903_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_st_ref_set(v___y_2891_, v___x_2912_);
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
v___x_2914_ = lean_apply_5(v_afterSet_2873_, v_decl_2875_, v_a_2893_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref(v___y_2889_);
return v___x_2914_;
}
else
{
lean_object* v_a_2915_; uint8_t v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
v___x_2916_ = l_Lean_Exception_isInterrupt(v_a_2915_);
if (v___x_2916_ == 0)
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_Exception_isRuntime(v_a_2915_);
v___y_2882_ = v___y_2891_;
v___y_2883_ = v___x_2914_;
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___x_2917_;
goto v___jp_2881_;
}
else
{
lean_dec(v_a_2915_);
v___y_2882_ = v___y_2891_;
v___y_2883_ = v___x_2914_;
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___x_2916_;
goto v___jp_2881_;
}
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v___y_2889_);
lean_dec(v_decl_2875_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
v_a_2921_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2892_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2892_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2929_:
{
lean_object* v___x_2930_; lean_object* v_env_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_st_ref_get(v___y_2879_);
v_env_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2930_);
v___x_2932_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2931_, v_decl_2875_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2874_);
v___y_2889_ = v_env_2931_;
v___y_2890_ = v___y_2878_;
v___y_2891_ = v___y_2879_;
goto v___jp_2888_;
}
else
{
lean_object* v_name_2933_; lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2932_, 1);
lean_dec_ref(v_env_2931_);
lean_dec(v_stx_2876_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
lean_dec_ref(v_getParam_2871_);
v_name_2933_ = lean_ctor_get(v_toAttributeImplCore_2874_, 1);
lean_inc(v_name_2933_);
lean_dec_ref(v_toAttributeImplCore_2874_);
v___x_2934_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2933_, v_decl_2875_, v___y_2878_, v___y_2879_);
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2939_, lean_object* v_ext_2940_, lean_object* v_afterSet_2941_, lean_object* v_toAttributeImplCore_2942_, lean_object* v_decl_2943_, lean_object* v_stx_2944_, lean_object* v_kind_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_kind_boxed_2949_; lean_object* v_res_2950_; 
v_kind_boxed_2949_ = lean_unbox(v_kind_2945_);
v_res_2950_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2939_, v_ext_2940_, v_afterSet_2941_, v_toAttributeImplCore_2942_, v_decl_2943_, v_stx_2944_, v_kind_boxed_2949_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2951_, lean_object* v_decl_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_name_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_name_2956_ = lean_ctor_get(v_toAttributeImplCore_2951_, 1);
lean_inc(v_name_2956_);
lean_dec_ref(v_toAttributeImplCore_2951_);
v___x_2957_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2958_ = l_Lean_MessageData_ofName(v_name_2956_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2961_, v___y_2953_, v___y_2954_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2963_, lean_object* v_decl_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2963_, v_decl_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_decl_2964_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2969_, lean_object* v_ext_2970_){
_start:
{
lean_object* v_toAttributeImplCore_2972_; lean_object* v_getParam_2973_; lean_object* v_afterSet_2974_; uint8_t v_preserveOrder_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v_attrImpl_2978_; lean_object* v___x_2979_; 
v_toAttributeImplCore_2972_ = lean_ctor_get(v_impl_2969_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2972_, 3);
v_getParam_2973_ = lean_ctor_get(v_impl_2969_, 1);
lean_inc_ref(v_getParam_2973_);
v_afterSet_2974_ = lean_ctor_get(v_impl_2969_, 2);
lean_inc_ref(v_afterSet_2974_);
v_preserveOrder_2975_ = lean_ctor_get_uint8(v_impl_2969_, sizeof(void*)*4);
lean_dec_ref(v_impl_2969_);
lean_inc_ref(v_ext_2970_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2976_, 0, v_getParam_2973_);
lean_closure_set(v___f_2976_, 1, v_ext_2970_);
lean_closure_set(v___f_2976_, 2, v_afterSet_2974_);
lean_closure_set(v___f_2976_, 3, v_toAttributeImplCore_2972_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2977_, 0, v_toAttributeImplCore_2972_);
v_attrImpl_2978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2978_, 0, v_toAttributeImplCore_2972_);
lean_ctor_set(v_attrImpl_2978_, 1, v___f_2976_);
lean_ctor_set(v_attrImpl_2978_, 2, v___f_2977_);
lean_inc_ref(v_attrImpl_2978_);
v___x_2979_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_2988_);
v___x_2981_ = v___x_2979_;
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v___x_2979_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2983_, 0, v_attrImpl_2978_);
lean_ctor_set(v___x_2983_, 1, v_ext_2970_);
lean_ctor_set_uint8(v___x_2983_, sizeof(void*)*2, v_preserveOrder_2975_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref_known(v_attrImpl_2978_, 3);
lean_dec_ref(v_ext_2970_);
v_a_2989_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2979_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2979_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2997_, lean_object* v_ext_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2997_, v_ext_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3001_, lean_object* v_impl_3002_, lean_object* v_ext_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3002_, v_ext_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_impl_3007_, lean_object* v_ext_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3006_, v_impl_3007_, v_ext_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3011_){
_start:
{
lean_object* v_toAttributeImplCore_3013_; uint8_t v_preserveOrder_3014_; lean_object* v_filterExport_3015_; lean_object* v_ref_3016_; lean_object* v___x_3017_; 
v_toAttributeImplCore_3013_ = lean_ctor_get(v_impl_3011_, 0);
v_preserveOrder_3014_ = lean_ctor_get_uint8(v_impl_3011_, sizeof(void*)*4);
v_filterExport_3015_ = lean_ctor_get(v_impl_3011_, 3);
v_ref_3016_ = lean_ctor_get(v_toAttributeImplCore_3013_, 0);
lean_inc_ref(v_filterExport_3015_);
lean_inc(v_ref_3016_);
v___x_3017_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3016_, v_preserveOrder_3014_, v_filterExport_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3011_, v_a_3018_);
return v___x_3019_;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec_ref(v_impl_3011_);
v_a_3020_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3017_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3017_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_registerParametricAttribute___redArg(v_impl_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3031_, lean_object* v_impl_3032_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_registerParametricAttribute___redArg(v_impl_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_impl_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_registerParametricAttribute(v_00_u03b1_3035_, v_impl_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3039_, lean_object* v___x_3040_, lean_object* v___x_3041_, lean_object* v_a_3042_, lean_object* v_x_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_fst_3045_; uint8_t v___x_3046_; 
v_fst_3045_ = lean_ctor_get(v_a_3042_, 0);
v___x_3046_ = lean_name_eq(v_fst_3045_, v_decl_3039_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_dec_ref(v_a_3042_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3040_);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref(v___x_3040_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3042_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3041_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3052_, lean_object* v___x_3053_, lean_object* v___x_3054_, lean_object* v_a_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3052_, v___x_3053_, v___x_3054_, v_a_3055_, v_x_3056_, v___y_3057_);
lean_dec_ref(v___y_3057_);
lean_dec(v_decl_3052_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3086_, lean_object* v_ext_3087_, uint8_t v_preserveOrder_3088_, lean_object* v_env_3089_, lean_object* v_decl_3090_){
_start:
{
lean_object* v___y_3092_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3104_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3089_, v_decl_3090_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_toEnvExtension_3105_; lean_object* v_asyncMode_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_snd_3109_; lean_object* v___x_3110_; 
lean_dec(v_inst_3086_);
v_toEnvExtension_3105_ = lean_ctor_get(v_ext_3087_, 0);
v_asyncMode_3106_ = lean_ctor_get(v_toEnvExtension_3105_, 2);
v___x_3107_ = lean_box(0);
v___x_3108_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_asyncMode_3106_, v___x_3107_);
v_snd_3109_ = lean_ctor_get(v___x_3108_, 1);
lean_inc(v_snd_3109_);
lean_dec(v___x_3108_);
v___x_3110_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3109_, v_decl_3090_);
lean_dec(v_decl_3090_);
lean_dec(v_snd_3109_);
return v___x_3110_;
}
else
{
if (v_preserveOrder_3088_ == 0)
{
lean_object* v_val_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_val_3111_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3112_ = 0;
v___x_3113_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_val_3111_, v___x_3112_);
lean_dec(v_val_3111_);
lean_dec_ref(v_env_3089_);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_array_get_size(v___x_3113_);
v___x_3116_ = lean_nat_dec_lt(v___x_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_dec_ref(v___x_3113_);
lean_dec(v_decl_3090_);
lean_dec(v_inst_3086_);
v___x_3117_ = lean_box(0);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_sub(v___x_3115_, v___x_3118_);
v___x_3120_ = lean_nat_dec_le(v___x_3114_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3113_);
lean_dec(v_decl_3090_);
lean_dec(v_inst_3086_);
v___x_3121_ = lean_box(0);
return v___x_3121_;
}
else
{
lean_object* v___f_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___f_3122_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_decl_3090_);
lean_ctor_set(v___x_3123_, 1, v_inst_3086_);
v___x_3124_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3125_ = l_Array_binSearchAux___redArg(v___f_3122_, v___x_3124_, v___x_3113_, v___x_3123_, v___x_3114_, v___x_3119_);
lean_dec_ref(v___x_3113_);
v___y_3092_ = v___x_3125_;
goto v___jp_3091_;
}
}
}
else
{
lean_object* v_val_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; size_t v_sz_3134_; size_t v___x_3135_; lean_object* v___x_3136_; lean_object* v_fst_3137_; 
lean_dec(v_inst_3086_);
v_val_3126_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_val_3126_, v___x_3127_);
lean_dec(v_val_3126_);
lean_dec_ref(v_env_3089_);
v___x_3129_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_box(0);
v___x_3132_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3133_, 0, v_decl_3090_);
lean_closure_set(v___f_3133_, 1, v___x_3132_);
lean_closure_set(v___f_3133_, 2, v___x_3131_);
v_sz_3134_ = lean_array_size(v___x_3128_);
v___x_3135_ = ((size_t)0ULL);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3129_, v___x_3128_, v___f_3133_, v_sz_3134_, v___x_3135_, v___x_3132_);
v_fst_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_fst_3137_);
lean_dec(v___x_3136_);
if (lean_obj_tag(v_fst_3137_) == 0)
{
return v___x_3130_;
}
else
{
lean_object* v_val_3138_; 
v_val_3138_ = lean_ctor_get(v_fst_3137_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_fst_3137_, 1);
v___y_3092_ = v_val_3138_;
goto v___jp_3091_;
}
}
}
v___jp_3091_:
{
if (lean_obj_tag(v___y_3092_) == 0)
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_box(0);
return v___x_3093_;
}
else
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_val_3094_ = lean_ctor_get(v___y_3092_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___y_3092_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v___y_3092_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v___y_3092_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_snd_3098_; lean_object* v___x_3100_; 
v_snd_3098_ = lean_ctor_get(v_val_3094_, 1);
lean_inc(v_snd_3098_);
lean_dec(v_val_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_snd_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_snd_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3139_, lean_object* v_ext_3140_, lean_object* v_preserveOrder_3141_, lean_object* v_env_3142_, lean_object* v_decl_3143_){
_start:
{
uint8_t v_preserveOrder_boxed_3144_; lean_object* v_res_3145_; 
v_preserveOrder_boxed_3144_ = lean_unbox(v_preserveOrder_3141_);
v_res_3145_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3139_, v_ext_3140_, v_preserveOrder_boxed_3144_, v_env_3142_, v_decl_3143_);
lean_dec_ref(v_ext_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3146_, lean_object* v_inst_3147_, lean_object* v_ext_3148_, uint8_t v_preserveOrder_3149_, lean_object* v_env_3150_, lean_object* v_decl_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3147_, v_ext_3148_, v_preserveOrder_3149_, v_env_3150_, v_decl_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3153_, lean_object* v_inst_3154_, lean_object* v_ext_3155_, lean_object* v_preserveOrder_3156_, lean_object* v_env_3157_, lean_object* v_decl_3158_){
_start:
{
uint8_t v_preserveOrder_boxed_3159_; lean_object* v_res_3160_; 
v_preserveOrder_boxed_3159_ = lean_unbox(v_preserveOrder_3156_);
v_res_3160_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3153_, v_inst_3154_, v_ext_3155_, v_preserveOrder_boxed_3159_, v_env_3157_, v_decl_3158_);
lean_dec_ref(v_ext_3155_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3161_, lean_object* v_attr_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
lean_object* v_ext_3165_; uint8_t v_preserveOrder_3166_; lean_object* v___x_3167_; 
v_ext_3165_ = lean_ctor_get(v_attr_3162_, 1);
v_preserveOrder_3166_ = lean_ctor_get_uint8(v_attr_3162_, sizeof(void*)*2);
v___x_3167_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3161_, v_ext_3165_, v_preserveOrder_3166_, v_env_3163_, v_decl_3164_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3168_, lean_object* v_attr_3169_, lean_object* v_env_3170_, lean_object* v_decl_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3168_, v_attr_3169_, v_env_3170_, v_decl_3171_);
lean_dec_ref(v_attr_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3173_, lean_object* v_inst_3174_, lean_object* v_attr_3175_, lean_object* v_env_3176_, lean_object* v_decl_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3174_, v_attr_3175_, v_env_3176_, v_decl_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_inst_3180_, lean_object* v_attr_3181_, lean_object* v_env_3182_, lean_object* v_decl_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3179_, v_inst_3180_, v_attr_3181_, v_env_3182_, v_decl_3183_);
lean_dec_ref(v_attr_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3189_, lean_object* v_attr_3190_, lean_object* v_env_3191_, lean_object* v_decl_3192_, lean_object* v_param_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3191_, v_decl_3192_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_toEnvExtension_3195_; lean_object* v_asyncMode_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_snd_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3230_; 
v_toEnvExtension_3195_ = lean_ctor_get(v_ext_3189_, 0);
v_asyncMode_3196_ = lean_ctor_get(v_toEnvExtension_3195_, 2);
lean_inc(v_asyncMode_3196_);
v___x_3197_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3198_ = lean_box(0);
lean_inc_ref(v_env_3191_);
v___x_3199_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3197_, v_ext_3189_, v_env_3191_, v_asyncMode_3196_, v___x_3198_);
v_snd_3200_ = lean_ctor_get(v___x_3199_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3231_);
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snd_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3200_, v_decl_3192_);
lean_dec(v_snd_3200_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v_attr_3190_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v_param_3193_);
lean_ctor_set(v___x_3202_, 0, v_decl_3192_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_decl_3192_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_param_3193_);
v___x_3206_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3189_, v_env_3191_, v___x_3206_, v_asyncMode_3196_, v___x_3198_);
lean_dec(v_asyncMode_3196_);
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
}
else
{
lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3202_);
lean_dec(v_asyncMode_3196_);
lean_dec(v_param_3193_);
lean_dec_ref(v_env_3191_);
lean_dec_ref(v_ext_3189_);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3204_, 0);
lean_dec(v_unused_3229_);
v___x_3211_ = v___x_3204_;
v_isShared_3212_ = v_isSharedCheck_3228_;
goto v_resetjp_3210_;
}
else
{
lean_dec(v___x_3204_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3228_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_toAttributeImplCore_3213_; lean_object* v_name_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v_toAttributeImplCore_3213_ = lean_ctor_get(v_attr_3190_, 0);
lean_inc_ref(v_toAttributeImplCore_3213_);
lean_dec_ref(v_attr_3190_);
v_name_3214_ = lean_ctor_get(v_toAttributeImplCore_3213_, 1);
lean_inc(v_name_3214_);
lean_dec_ref(v_toAttributeImplCore_3213_);
v___x_3215_ = 1;
v___x_3216_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3214_, v___x_3215_);
v___x_3218_ = lean_string_append(v___x_3216_, v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3220_ = lean_string_append(v___x_3218_, v___x_3219_);
v___x_3221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3192_, v___x_3215_);
v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
lean_dec_ref(v___x_3221_);
v___x_3223_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3224_);
v___x_3226_ = v___x_3211_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_param_3193_);
lean_dec_ref(v_env_3191_);
lean_dec_ref(v_ext_3189_);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3194_, 0);
lean_dec(v_unused_3251_);
v___x_3233_ = v___x_3194_;
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3194_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_toAttributeImplCore_3235_; lean_object* v_name_3236_; uint8_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v_toAttributeImplCore_3235_ = lean_ctor_get(v_attr_3190_, 0);
lean_inc_ref(v_toAttributeImplCore_3235_);
lean_dec_ref(v_attr_3190_);
v_name_3236_ = lean_ctor_get(v_toAttributeImplCore_3235_, 1);
lean_inc(v_name_3236_);
lean_dec_ref(v_toAttributeImplCore_3235_);
v___x_3237_ = 1;
v___x_3238_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3239_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3236_, v___x_3237_);
v___x_3240_ = lean_string_append(v___x_3238_, v___x_3239_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
v___x_3243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3192_, v___x_3237_);
v___x_3244_ = lean_string_append(v___x_3242_, v___x_3243_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3246_);
v___x_3248_ = v___x_3233_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3252_, lean_object* v_ext_3253_, lean_object* v_attr_3254_, lean_object* v_env_3255_, lean_object* v_decl_3256_, lean_object* v_param_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3253_, v_attr_3254_, v_env_3255_, v_decl_3256_, v_param_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3259_, lean_object* v_env_3260_, lean_object* v_decl_3261_, lean_object* v_param_3262_){
_start:
{
lean_object* v_attr_3263_; lean_object* v_ext_3264_; lean_object* v___x_3265_; 
v_attr_3263_ = lean_ctor_get(v_attr_3259_, 0);
lean_inc_ref(v_attr_3263_);
v_ext_3264_ = lean_ctor_get(v_attr_3259_, 1);
lean_inc_ref(v_ext_3264_);
lean_dec_ref(v_attr_3259_);
v___x_3265_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3264_, v_attr_3263_, v_env_3260_, v_decl_3261_, v_param_3262_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3266_, lean_object* v_attr_3267_, lean_object* v_env_3268_, lean_object* v_decl_3269_, lean_object* v_param_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3267_, v_env_3268_, v_decl_3269_, v_param_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3277_, v___y_3278_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_x_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3281_, lean_object* v_x_3282_){
_start:
{
lean_inc(v_s_3281_);
return v_s_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3283_, v_x_3284_);
lean_dec_ref(v_x_3284_);
lean_dec(v_s_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3289_, v_x_3290_);
lean_dec(v_x_3290_);
lean_dec_ref(v_x_3289_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___f_3296_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3299_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3300_);
lean_ctor_set(v___x_3302_, 2, v___f_3299_);
lean_ctor_set(v___x_3302_, 3, v___f_3298_);
lean_ctor_set(v___x_3302_, 4, v___f_3297_);
lean_ctor_set(v___x_3302_, 5, v___f_3296_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3314_);
lean_dec(v_x_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_){
_start:
{
if (lean_obj_tag(v_x_3318_) == 0)
{
return v_x_3317_;
}
else
{
lean_object* v_head_3319_; lean_object* v_tail_3320_; lean_object* v___x_3321_; 
v_head_3319_ = lean_ctor_get(v_x_3318_, 0);
lean_inc(v_head_3319_);
v_tail_3320_ = lean_ctor_get(v_x_3318_, 1);
lean_inc(v_tail_3320_);
lean_dec_ref_known(v_x_3318_, 2);
v___x_3321_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3316_, v_head_3319_);
if (lean_obj_tag(v___x_3321_) == 1)
{
lean_object* v_val_3322_; lean_object* v___x_3323_; 
v_val_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v___x_3323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3319_, v_val_3322_, v_x_3317_);
v_x_3317_ = v___x_3323_;
v_x_3318_ = v_tail_3320_;
goto _start;
}
else
{
lean_dec(v___x_3321_);
lean_dec(v_head_3319_);
v_x_3318_ = v_tail_3320_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3326_, v_x_3327_, v_x_3328_);
lean_dec(v_newState_3326_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3330_, lean_object* v_newState_3331_, lean_object* v_consts_3332_, lean_object* v_st_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3331_, v_st_3333_, v_consts_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3335_, lean_object* v_newState_3336_, lean_object* v_consts_3337_, lean_object* v_st_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3335_, v_newState_3336_, v_consts_3337_, v_st_3338_);
lean_dec(v_newState_3336_);
lean_dec(v_x_3335_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3349_){
_start:
{
lean_object* v___x_3350_; lean_object* v___y_3352_; 
v___x_3350_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3349_) == 0)
{
lean_object* v_size_3356_; 
v_size_3356_ = lean_ctor_get(v_s_3349_, 0);
lean_inc(v_size_3356_);
lean_dec_ref_known(v_s_3349_, 5);
v___y_3352_ = v_size_3356_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___y_3352_ = v___x_3357_;
goto v___jp_3351_;
}
v___jp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = l_Nat_reprFast(v___y_3352_);
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3350_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3358_, lean_object* v_as_3359_, size_t v_i_3360_, size_t v_stop_3361_, lean_object* v_b_3362_){
_start:
{
lean_object* v___y_3364_; uint8_t v___x_3368_; 
v___x_3368_ = lean_usize_dec_eq(v_i_3360_, v_stop_3361_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v_fst_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3369_ = lean_array_uget_borrowed(v_as_3359_, v_i_3360_);
v_fst_3370_ = lean_ctor_get(v___x_3369_, 0);
v___x_3371_ = 1;
lean_inc_ref(v_env_3358_);
v___x_3372_ = l_Lean_Environment_setExporting(v_env_3358_, v___x_3371_);
lean_inc(v_fst_3370_);
v___x_3373_ = l_Lean_Environment_contains(v___x_3372_, v_fst_3370_, v___x_3368_);
if (v___x_3373_ == 0)
{
v___y_3364_ = v_b_3362_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3374_; 
lean_inc(v___x_3369_);
v___x_3374_ = lean_array_push(v_b_3362_, v___x_3369_);
v___y_3364_ = v___x_3374_;
goto v___jp_3363_;
}
}
else
{
lean_dec_ref(v_env_3358_);
return v_b_3362_;
}
v___jp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3360_, v___x_3365_);
v_i_3360_ = v___x_3366_;
v_b_3362_ = v___y_3364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3375_, lean_object* v_as_3376_, lean_object* v_i_3377_, lean_object* v_stop_3378_, lean_object* v_b_3379_){
_start:
{
size_t v_i_boxed_3380_; size_t v_stop_boxed_3381_; lean_object* v_res_3382_; 
v_i_boxed_3380_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_stop_boxed_3381_ = lean_unbox_usize(v_stop_3378_);
lean_dec(v_stop_3378_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3375_, v_as_3376_, v_i_boxed_3380_, v_stop_boxed_3381_, v_b_3379_);
lean_dec_ref(v_as_3376_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3383_, lean_object* v_m_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___y_3388_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___x_3408_; 
v___x_3385_ = lean_unsigned_to_nat(0u);
v___x_3386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3386_, v_m_3384_);
v___x_3403_ = lean_array_get_size(v___x_3402_);
v___x_3408_ = lean_nat_dec_eq(v___x_3403_, v___x_3385_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3412_; uint8_t v___x_3414_; 
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_nat_sub(v___x_3403_, v___x_3409_);
v___x_3414_ = lean_nat_dec_le(v___x_3385_, v___x_3410_);
if (v___x_3414_ == 0)
{
lean_inc(v___x_3410_);
v___y_3412_ = v___x_3410_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v___x_3385_;
goto v___jp_3411_;
}
v___jp_3411_:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_nat_dec_le(v___y_3412_, v___x_3410_);
if (v___x_3413_ == 0)
{
lean_dec(v___x_3410_);
lean_inc(v___y_3412_);
v___y_3405_ = v___y_3412_;
v___y_3406_ = v___y_3412_;
goto v___jp_3404_;
}
else
{
v___y_3405_ = v___y_3412_;
v___y_3406_ = v___x_3410_;
goto v___jp_3404_;
}
}
}
else
{
v___y_3388_ = v___x_3402_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = lean_array_get_size(v___y_3388_);
v___x_3390_ = lean_nat_dec_lt(v___x_3385_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref(v_env_3383_);
v___x_3391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3386_);
lean_ctor_set(v___x_3391_, 1, v___x_3386_);
lean_ctor_set(v___x_3391_, 2, v___y_3388_);
return v___x_3391_;
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_nat_dec_le(v___x_3389_, v___x_3389_);
if (v___x_3392_ == 0)
{
if (v___x_3390_ == 0)
{
lean_object* v___x_3393_; 
lean_dec_ref(v_env_3383_);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3386_);
lean_ctor_set(v___x_3393_, 1, v___x_3386_);
lean_ctor_set(v___x_3393_, 2, v___y_3388_);
return v___x_3393_;
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = lean_usize_of_nat(v___x_3389_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3383_, v___y_3388_, v___x_3394_, v___x_3395_, v___x_3386_);
lean_inc_ref(v___x_3396_);
v___x_3397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
lean_ctor_set(v___x_3397_, 2, v___y_3388_);
return v___x_3397_;
}
}
else
{
size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = ((size_t)0ULL);
v___x_3399_ = lean_usize_of_nat(v___x_3389_);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3383_, v___y_3388_, v___x_3398_, v___x_3399_, v___x_3386_);
lean_inc_ref(v___x_3400_);
v___x_3401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
lean_ctor_set(v___x_3401_, 2, v___y_3388_);
return v___x_3401_;
}
}
}
v___jp_3404_:
{
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3403_, v___x_3402_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
v___y_3388_ = v___x_3407_;
goto v___jp_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3415_, lean_object* v_m_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3415_, v_m_3416_);
lean_dec(v_m_3416_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3418_, lean_object* v_p_3419_){
_start:
{
lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3422_; 
v_fst_3420_ = lean_ctor_get(v_p_3419_, 0);
lean_inc(v_fst_3420_);
v_snd_3421_ = lean_ctor_get(v_p_3419_, 1);
lean_inc(v_snd_3421_);
lean_dec_ref(v_p_3419_);
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3420_, v_snd_3421_, v_s_3418_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3423_, lean_object* v_x_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3423_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3428_, v_x_3429_, v_x_3430_);
lean_dec_ref(v_x_3430_);
lean_dec_ref(v_x_3429_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3433_){
_start:
{
if (lean_obj_tag(v_as_3433_) == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
else
{
lean_object* v_head_3437_; lean_object* v_tail_3438_; lean_object* v___x_3439_; 
v_head_3437_ = lean_ctor_get(v_as_3433_, 0);
lean_inc(v_head_3437_);
v_tail_3438_ = lean_ctor_get(v_as_3433_, 1);
lean_inc(v_tail_3438_);
lean_dec_ref_known(v_as_3433_, 2);
v___x_3439_ = l_Lean_registerBuiltinAttribute(v_head_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref_known(v___x_3439_, 1);
v_as_3433_ = v_tail_3438_;
goto _start;
}
else
{
lean_dec(v_tail_3438_);
return v___x_3439_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3444_, lean_object* v_snd_3445_, lean_object* v_a_3446_, lean_object* v_fst_3447_, lean_object* v_decl_3448_, lean_object* v_stx_3449_, uint8_t v_kind_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3449_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3497_) == 0)
{
uint8_t v___x_3498_; uint8_t v___x_3499_; 
lean_dec_ref_known(v___x_3497_, 1);
v___x_3498_ = 0;
v___x_3499_ = l_Lean_instBEqAttributeKind_beq(v_kind_3450_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v_decl_3448_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
v___x_3500_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3447_, v_kind_3450_, v___y_3451_, v___y_3452_);
return v___x_3500_;
}
else
{
v___y_3491_ = v___y_3451_;
v___y_3492_ = v___y_3452_;
goto v___jp_3490_;
}
}
else
{
lean_dec(v_decl_3448_);
lean_dec(v_fst_3447_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
return v___x_3497_;
}
v___jp_3454_:
{
lean_object* v___x_3457_; 
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
lean_inc(v_snd_3445_);
lean_inc(v_decl_3448_);
v___x_3457_ = lean_apply_5(v_validate_3444_, v_decl_3448_, v_snd_3445_, v___y_3455_, v___y_3456_, lean_box(0));
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3488_; 
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3457_, 0);
lean_dec(v_unused_3489_);
v___x_3459_ = v___x_3457_;
v_isShared_3460_ = v_isSharedCheck_3488_;
goto v_resetjp_3458_;
}
else
{
lean_dec(v___x_3457_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3488_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v_toEnvExtension_3462_; lean_object* v_env_3463_; lean_object* v_nextMacroScope_3464_; lean_object* v_ngen_3465_; lean_object* v_auxDeclNGen_3466_; lean_object* v_traceState_3467_; lean_object* v_messages_3468_; lean_object* v_infoState_3469_; lean_object* v_snapshotTasks_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3486_; 
v___x_3461_ = lean_st_ref_take(v___y_3456_);
v_toEnvExtension_3462_ = lean_ctor_get(v_a_3446_, 0);
v_env_3463_ = lean_ctor_get(v___x_3461_, 0);
v_nextMacroScope_3464_ = lean_ctor_get(v___x_3461_, 1);
v_ngen_3465_ = lean_ctor_get(v___x_3461_, 2);
v_auxDeclNGen_3466_ = lean_ctor_get(v___x_3461_, 3);
v_traceState_3467_ = lean_ctor_get(v___x_3461_, 4);
v_messages_3468_ = lean_ctor_get(v___x_3461_, 6);
v_infoState_3469_ = lean_ctor_get(v___x_3461_, 7);
v_snapshotTasks_3470_ = lean_ctor_get(v___x_3461_, 8);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v___x_3461_, 5);
lean_dec(v_unused_3487_);
v___x_3472_ = v___x_3461_;
v_isShared_3473_ = v_isSharedCheck_3486_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_snapshotTasks_3470_);
lean_inc(v_infoState_3469_);
lean_inc(v_messages_3468_);
lean_inc(v_traceState_3467_);
lean_inc(v_auxDeclNGen_3466_);
lean_inc(v_ngen_3465_);
lean_inc(v_nextMacroScope_3464_);
lean_inc(v_env_3463_);
lean_dec(v___x_3461_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3486_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_asyncMode_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v_asyncMode_3474_ = lean_ctor_get(v_toEnvExtension_3462_, 2);
lean_inc(v_asyncMode_3474_);
lean_inc(v_decl_3448_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v_decl_3448_);
lean_ctor_set(v___x_3475_, 1, v_snd_3445_);
v___x_3476_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3446_, v_env_3463_, v___x_3475_, v_asyncMode_3474_, v_decl_3448_);
lean_dec(v_asyncMode_3474_);
v___x_3477_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 5, v___x_3477_);
lean_ctor_set(v___x_3472_, 0, v___x_3476_);
v___x_3479_ = v___x_3472_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_nextMacroScope_3464_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_ngen_3465_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_auxDeclNGen_3466_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_traceState_3467_);
lean_ctor_set(v_reuseFailAlloc_3485_, 5, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3485_, 6, v_messages_3468_);
lean_ctor_set(v_reuseFailAlloc_3485_, 7, v_infoState_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 8, v_snapshotTasks_3470_);
v___x_3479_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3480_ = lean_st_ref_set(v___y_3456_, v___x_3479_);
v___x_3481_ = lean_box(0);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3481_);
v___x_3483_ = v___x_3459_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
else
{
lean_dec(v_decl_3448_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
return v___x_3457_;
}
}
v___jp_3490_:
{
lean_object* v___x_3493_; lean_object* v_env_3494_; lean_object* v___x_3495_; 
v___x_3493_ = lean_st_ref_get(v___y_3492_);
v_env_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc_ref(v_env_3494_);
lean_dec(v___x_3493_);
v___x_3495_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3494_, v_decl_3448_);
lean_dec_ref(v_env_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_dec(v_fst_3447_);
v___y_3455_ = v___y_3491_;
v___y_3456_ = v___y_3492_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3496_; 
lean_dec_ref_known(v___x_3495_, 1);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
v___x_3496_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3447_, v_decl_3448_, v___y_3491_, v___y_3492_);
return v___x_3496_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3501_, lean_object* v_snd_3502_, lean_object* v_a_3503_, lean_object* v_fst_3504_, lean_object* v_decl_3505_, lean_object* v_stx_3506_, lean_object* v_kind_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v_kind_boxed_3511_; lean_object* v_res_3512_; 
v_kind_boxed_3511_ = lean_unbox(v_kind_3507_);
v_res_3512_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3501_, v_snd_3502_, v_a_3503_, v_fst_3504_, v_decl_3505_, v_stx_3506_, v_kind_boxed_3511_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3513_, lean_object* v_decl_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3518_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3519_ = l_Lean_MessageData_ofName(v_fst_3513_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3522_, v___y_3515_, v___y_3516_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3524_, lean_object* v_decl_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3524_, v_decl_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v_decl_3525_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3530_, lean_object* v_a_3531_, lean_object* v_ref_3532_, uint8_t v_applicationTime_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
if (lean_obj_tag(v_a_3534_) == 0)
{
lean_object* v___x_3536_; 
lean_dec(v_ref_3532_);
lean_dec_ref(v_a_3531_);
lean_dec_ref(v_validate_3530_);
v___x_3536_ = l_List_reverse___redArg(v_a_3535_);
return v___x_3536_;
}
else
{
lean_object* v_head_3537_; lean_object* v_snd_3538_; lean_object* v_tail_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3554_; 
v_head_3537_ = lean_ctor_get(v_a_3534_, 0);
lean_inc(v_head_3537_);
v_snd_3538_ = lean_ctor_get(v_head_3537_, 1);
lean_inc(v_snd_3538_);
v_tail_3539_ = lean_ctor_get(v_a_3534_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_a_3534_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; 
v_unused_3555_ = lean_ctor_get(v_a_3534_, 0);
lean_dec(v_unused_3555_);
v___x_3541_ = v_a_3534_;
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_tail_3539_);
lean_dec(v_a_3534_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_fst_3543_; lean_object* v_fst_3544_; lean_object* v_snd_3545_; lean_object* v___f_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v_fst_3543_ = lean_ctor_get(v_head_3537_, 0);
lean_inc_n(v_fst_3543_, 3);
lean_dec(v_head_3537_);
v_fst_3544_ = lean_ctor_get(v_snd_3538_, 0);
lean_inc(v_fst_3544_);
v_snd_3545_ = lean_ctor_get(v_snd_3538_, 1);
lean_inc(v_snd_3545_);
lean_dec(v_snd_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3546_, 0, v_fst_3543_);
lean_inc_ref(v_a_3531_);
lean_inc_ref(v_validate_3530_);
v___f_3547_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3547_, 0, v_validate_3530_);
lean_closure_set(v___f_3547_, 1, v_snd_3545_);
lean_closure_set(v___f_3547_, 2, v_a_3531_);
lean_closure_set(v___f_3547_, 3, v_fst_3543_);
lean_inc(v_ref_3532_);
v___x_3548_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3548_, 0, v_ref_3532_);
lean_ctor_set(v___x_3548_, 1, v_fst_3543_);
lean_ctor_set(v___x_3548_, 2, v_fst_3544_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*3, v_applicationTime_3533_);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___f_3547_);
lean_ctor_set(v___x_3549_, 2, v___f_3546_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v_a_3535_);
lean_ctor_set(v___x_3541_, 0, v___x_3549_);
v___x_3551_ = v___x_3541_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_a_3535_);
v___x_3551_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
v_a_3534_ = v_tail_3539_;
v_a_3535_ = v___x_3551_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3556_, lean_object* v_a_3557_, lean_object* v_ref_3558_, lean_object* v_applicationTime_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
uint8_t v_applicationTime_boxed_3562_; lean_object* v_res_3563_; 
v_applicationTime_boxed_3562_ = lean_unbox(v_applicationTime_3559_);
v_res_3563_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3556_, v_a_3557_, v_ref_3558_, v_applicationTime_boxed_3562_, v_a_3560_, v_a_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3577_, lean_object* v_validate_3578_, uint8_t v_applicationTime_3579_, lean_object* v_ref_3580_){
_start:
{
lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___f_3582_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3583_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3584_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3585_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3586_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3587_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3580_);
v___x_3590_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3590_, 0, v_ref_3580_);
lean_ctor_set(v___x_3590_, 1, v___f_3586_);
lean_ctor_set(v___x_3590_, 2, v___f_3587_);
lean_ctor_set(v___x_3590_, 3, v___f_3585_);
lean_ctor_set(v___x_3590_, 4, v___f_3584_);
lean_ctor_set(v___x_3590_, 5, v___f_3583_);
lean_ctor_set(v___x_3590_, 6, v___x_3588_);
lean_ctor_set(v___x_3590_, 7, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v___f_3582_);
v___x_3592_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc_n(v_a_3593_, 2);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = lean_box(0);
v___x_3595_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3578_, v_a_3593_, v_ref_3580_, v_applicationTime_3579_, v_attrDescrs_3577_, v___x_3594_);
lean_inc(v___x_3595_);
v___x_3596_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3595_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3604_ == 0)
{
lean_object* v_unused_3605_; 
v_unused_3605_ = lean_ctor_get(v___x_3596_, 0);
lean_dec(v_unused_3605_);
v___x_3598_ = v___x_3596_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v___x_3596_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3595_);
lean_ctor_set(v___x_3600_, 1, v_a_3593_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___x_3595_);
lean_dec(v_a_3593_);
v_a_3606_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3596_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3596_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_ref_3580_);
lean_dec_ref(v_validate_3578_);
lean_dec(v_attrDescrs_3577_);
v_a_3614_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3592_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3592_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3622_, lean_object* v_validate_3623_, lean_object* v_applicationTime_3624_, lean_object* v_ref_3625_, lean_object* v_a_3626_){
_start:
{
uint8_t v_applicationTime_boxed_3627_; lean_object* v_res_3628_; 
v_applicationTime_boxed_3627_ = lean_unbox(v_applicationTime_3624_);
v_res_3628_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3622_, v_validate_3623_, v_applicationTime_boxed_3627_, v_ref_3625_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3629_, lean_object* v_attrDescrs_3630_, lean_object* v_validate_3631_, uint8_t v_applicationTime_3632_, lean_object* v_ref_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3630_, v_validate_3631_, v_applicationTime_3632_, v_ref_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3636_, lean_object* v_attrDescrs_3637_, lean_object* v_validate_3638_, lean_object* v_applicationTime_3639_, lean_object* v_ref_3640_, lean_object* v_a_3641_){
_start:
{
uint8_t v_applicationTime_boxed_3642_; lean_object* v_res_3643_; 
v_applicationTime_boxed_3642_ = lean_unbox(v_applicationTime_3639_);
v_res_3643_ = l_Lean_registerEnumAttributes(v_00_u03b1_3636_, v_attrDescrs_3637_, v_validate_3638_, v_applicationTime_boxed_3642_, v_ref_3640_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3644_, lean_object* v_env_3645_, lean_object* v_as_3646_, size_t v_i_3647_, size_t v_stop_3648_, lean_object* v_b_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3645_, v_as_3646_, v_i_3647_, v_stop_3648_, v_b_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3651_, lean_object* v_env_3652_, lean_object* v_as_3653_, lean_object* v_i_3654_, lean_object* v_stop_3655_, lean_object* v_b_3656_){
_start:
{
size_t v_i_boxed_3657_; size_t v_stop_boxed_3658_; lean_object* v_res_3659_; 
v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_stop_boxed_3658_ = lean_unbox_usize(v_stop_3655_);
lean_dec(v_stop_3655_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3651_, v_env_3652_, v_as_3653_, v_i_boxed_3657_, v_stop_boxed_3658_, v_b_3656_);
lean_dec_ref(v_as_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3660_, lean_object* v_newState_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3661_, v_x_3662_, v_x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3665_, lean_object* v_newState_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3665_, v_newState_3666_, v_x_3667_, v_x_3668_);
lean_dec(v_newState_3666_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3670_, lean_object* v_validate_3671_, lean_object* v_a_3672_, lean_object* v_ref_3673_, uint8_t v_applicationTime_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3671_, v_a_3672_, v_ref_3673_, v_applicationTime_3674_, v_a_3675_, v_a_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3678_, lean_object* v_validate_3679_, lean_object* v_a_3680_, lean_object* v_ref_3681_, lean_object* v_applicationTime_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
uint8_t v_applicationTime_boxed_3685_; lean_object* v_res_3686_; 
v_applicationTime_boxed_3685_ = lean_unbox(v_applicationTime_3682_);
v_res_3686_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3678_, v_validate_3679_, v_a_3680_, v_ref_3681_, v_applicationTime_boxed_3685_, v_a_3683_, v_a_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3687_, lean_object* v_attr_3688_, lean_object* v_env_3689_, lean_object* v_decl_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_box(1);
v___x_3692_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3689_, v_decl_3690_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_ext_3693_; lean_object* v_toEnvExtension_3694_; lean_object* v_asyncMode_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_inst_3687_);
v_ext_3693_ = lean_ctor_get(v_attr_3688_, 1);
lean_inc_ref(v_ext_3693_);
lean_dec_ref(v_attr_3688_);
v_toEnvExtension_3694_ = lean_ctor_get(v_ext_3693_, 0);
v_asyncMode_3695_ = lean_ctor_get(v_toEnvExtension_3694_, 2);
lean_inc(v_asyncMode_3695_);
lean_inc(v_decl_3690_);
v___x_3696_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3691_, v_ext_3693_, v_env_3689_, v_asyncMode_3695_, v_decl_3690_);
lean_dec(v_asyncMode_3695_);
lean_dec_ref(v_ext_3693_);
v___x_3697_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3696_, v_decl_3690_);
lean_dec(v_decl_3690_);
lean_dec(v___x_3696_);
return v___x_3697_;
}
else
{
lean_object* v_val_3698_; lean_object* v_ext_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3729_; 
v_val_3698_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v___x_3692_, 1);
v_ext_3699_ = lean_ctor_get(v_attr_3688_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_attr_3688_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_attr_3688_, 0);
lean_dec(v_unused_3730_);
v___x_3701_ = v_attr_3688_;
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_ext_3699_);
lean_dec(v_attr_3688_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint8_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___x_3703_ = 0;
v___x_3704_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3691_, v_ext_3699_, v_env_3689_, v_val_3698_, v___x_3703_);
lean_dec(v_val_3698_);
lean_dec_ref(v_env_3689_);
lean_dec_ref(v_ext_3699_);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_array_get_size(v___x_3704_);
v___x_3707_ = lean_nat_dec_lt(v___x_3705_, v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v___x_3704_);
lean_del_object(v___x_3701_);
lean_dec(v_decl_3690_);
lean_dec(v_inst_3687_);
v___x_3708_ = lean_box(0);
return v___x_3708_;
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_nat_sub(v___x_3706_, v___x_3709_);
v___x_3711_ = lean_nat_dec_le(v___x_3705_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; 
lean_dec(v___x_3710_);
lean_dec_ref(v___x_3704_);
lean_del_object(v___x_3701_);
lean_dec(v_decl_3690_);
lean_dec(v_inst_3687_);
v___x_3712_ = lean_box(0);
return v___x_3712_;
}
else
{
lean_object* v___f_3713_; lean_object* v___x_3715_; 
v___f_3713_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v_inst_3687_);
lean_ctor_set(v___x_3701_, 0, v_decl_3690_);
v___x_3715_ = v___x_3701_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_decl_3690_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_inst_3687_);
v___x_3715_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3717_ = l_Array_binSearchAux___redArg(v___f_3713_, v___x_3716_, v___x_3704_, v___x_3715_, v___x_3705_, v___x_3710_);
lean_dec_ref(v___x_3704_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_box(0);
return v___x_3718_;
}
else
{
lean_object* v_val_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3727_; 
v_val_3719_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3721_ = v___x_3717_;
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_val_3719_);
lean_dec(v___x_3717_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v_snd_3723_; lean_object* v___x_3725_; 
v_snd_3723_ = lean_ctor_get(v_val_3719_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_val_3719_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v_snd_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_snd_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3731_, lean_object* v_inst_3732_, lean_object* v_attr_3733_, lean_object* v_env_3734_, lean_object* v_decl_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3732_, v_attr_3733_, v_env_3734_, v_decl_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3745_, lean_object* v_env_3746_, lean_object* v_decl_3747_, lean_object* v_val_3748_){
_start:
{
lean_object* v_ext_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3813_; 
v_ext_3749_ = lean_ctor_get(v_attrs_3745_, 1);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_attrs_3745_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v_attrs_3745_, 0);
lean_dec(v_unused_3814_);
v___x_3751_ = v_attrs_3745_;
v_isShared_3752_ = v_isSharedCheck_3813_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_ext_3749_);
lean_dec(v_attrs_3745_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3813_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v_toEnvExtension_3753_; lean_object* v_name_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v_pfx_3764_; lean_object* v___x_3765_; 
v_toEnvExtension_3753_ = lean_ctor_get(v_ext_3749_, 0);
v_name_3754_ = lean_ctor_get(v_ext_3749_, 1);
v___x_3755_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3756_ = 1;
lean_inc(v_name_3754_);
v___x_3757_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3754_, v___x_3756_);
v___x_3758_ = lean_string_append(v___x_3755_, v___x_3757_);
lean_dec_ref(v___x_3757_);
v___x_3759_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3760_ = lean_string_append(v___x_3758_, v___x_3759_);
lean_inc(v_decl_3747_);
v___x_3761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3747_, v___x_3756_);
v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3764_ = lean_string_append(v___x_3762_, v___x_3763_);
v___x_3765_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3746_, v_decl_3747_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_asyncMode_3766_; uint8_t v___x_3773_; 
v_asyncMode_3766_ = lean_ctor_get(v_toEnvExtension_3753_, 2);
lean_inc(v_asyncMode_3766_);
lean_inc(v_decl_3747_);
lean_inc_ref(v_env_3746_);
v___x_3773_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3746_, v_decl_3747_, v_asyncMode_3766_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___y_3777_; lean_object* v___x_3781_; 
lean_dec(v_asyncMode_3766_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
v___x_3774_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3775_ = lean_string_append(v_pfx_3764_, v___x_3774_);
v___x_3781_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3746_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3782_; 
v___x_3782_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3777_ = v___x_3782_;
goto v___jp_3776_;
}
else
{
lean_object* v_val_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_val_3783_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3784_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3783_, v___x_3756_);
v___x_3786_ = l_addParenHeuristic(v___x_3785_);
v___x_3787_ = lean_string_append(v___x_3784_, v___x_3786_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3789_ = lean_string_append(v___x_3787_, v___x_3788_);
v___y_3777_ = v___x_3789_;
goto v___jp_3776_;
}
v___jp_3776_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_string_append(v___x_3775_, v___y_3777_);
lean_dec_ref(v___y_3777_);
v___x_3779_ = lean_string_append(v___x_3778_, v___x_3763_);
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_box(1);
lean_inc(v_decl_3747_);
lean_inc_ref(v_env_3746_);
v___x_3791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3790_, v_ext_3749_, v_env_3746_, v_asyncMode_3766_, v_decl_3747_);
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3791_, v_decl_3747_);
lean_dec(v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_dec_ref(v_pfx_3764_);
goto v___jp_3767_;
}
else
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3801_; 
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3802_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3801_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
if (v___x_3773_ == 0)
{
lean_del_object(v___x_3794_);
lean_dec_ref(v_pfx_3764_);
goto v___jp_3767_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3799_; 
lean_dec(v_asyncMode_3766_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
lean_dec_ref(v_env_3746_);
v___x_3796_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3797_ = lean_string_append(v_pfx_3764_, v___x_3796_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3797_);
v___x_3799_ = v___x_3794_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
v___jp_3767_:
{
lean_object* v___x_3769_; 
lean_inc(v_decl_3747_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v_val_3748_);
lean_ctor_set(v___x_3751_, 0, v_decl_3747_);
v___x_3769_ = v___x_3751_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_decl_3747_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_val_3748_);
v___x_3769_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3749_, v_env_3746_, v___x_3769_, v_asyncMode_3766_, v_decl_3747_);
lean_dec(v_asyncMode_3766_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
return v___x_3771_;
}
}
}
else
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3811_; 
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
lean_dec_ref(v_env_3746_);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v___x_3765_, 0);
lean_dec(v_unused_3812_);
v___x_3804_ = v___x_3765_;
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v___x_3765_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3811_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3806_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3807_ = lean_string_append(v_pfx_3764_, v___x_3806_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set_tag(v___x_3804_, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3807_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3815_, lean_object* v_attrs_3816_, lean_object* v_env_3817_, lean_object* v_decl_3818_, lean_object* v_val_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3816_, v_env_3817_, v_decl_3818_, v_val_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3823_ = lean_st_mk_ref(v___x_3822_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3829_, lean_object* v_builder_3830_){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; uint8_t v___x_3834_; 
v___x_3832_ = l_Lean_attributeImplBuilderTableRef;
v___x_3833_ = lean_st_ref_get(v___x_3832_);
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3833_, v_builderId_3829_);
lean_dec(v___x_3833_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3835_ = lean_st_ref_take(v___x_3832_);
v___x_3836_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3835_, v_builderId_3829_, v_builder_3830_);
v___x_3837_ = lean_st_ref_set(v___x_3832_, v___x_3836_);
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
else
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec_ref(v_builder_3830_);
v___x_3839_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3829_, v___x_3834_);
v___x_3841_ = lean_string_append(v___x_3839_, v___x_3840_);
lean_dec_ref(v___x_3840_);
v___x_3842_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3843_ = lean_string_append(v___x_3841_, v___x_3842_);
v___x_3844_ = lean_mk_io_user_error(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3846_, lean_object* v_builder_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_registerAttributeImplBuilder(v_builderId_3846_, v_builder_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3850_){
_start:
{
if (lean_obj_tag(v_e_3850_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3860_; 
v_a_3852_ = lean_ctor_get(v_e_3850_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_e_3850_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3854_ = v_e_3850_;
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v_e_3850_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3860_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_mk_io_user_error(v_a_3852_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set_tag(v___x_3854_, 1);
lean_ctor_set(v___x_3854_, 0, v___x_3856_);
v___x_3858_ = v___x_3854_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
v_a_3861_ = lean_ctor_get(v_e_3850_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_e_3850_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v_e_3850_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v_e_3850_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
lean_ctor_set_tag(v___x_3863_, 0);
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3872_, lean_object* v_e_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3873_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3876_, lean_object* v_e_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3876_, v_e_3877_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3880_, lean_object* v_x_3881_){
_start:
{
if (lean_obj_tag(v_x_3881_) == 0)
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_box(0);
return v___x_3882_;
}
else
{
lean_object* v_key_3883_; lean_object* v_value_3884_; lean_object* v_tail_3885_; uint8_t v___x_3886_; 
v_key_3883_ = lean_ctor_get(v_x_3881_, 0);
v_value_3884_ = lean_ctor_get(v_x_3881_, 1);
v_tail_3885_ = lean_ctor_get(v_x_3881_, 2);
v___x_3886_ = lean_name_eq(v_key_3883_, v_a_3880_);
if (v___x_3886_ == 0)
{
v_x_3881_ = v_tail_3885_;
goto _start;
}
else
{
lean_object* v___x_3888_; 
lean_inc(v_value_3884_);
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_value_3884_);
return v___x_3888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3889_, lean_object* v_x_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3889_, v_x_3890_);
lean_dec(v_x_3890_);
lean_dec(v_a_3889_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_buckets_3894_; lean_object* v___x_3895_; uint64_t v___y_3897_; 
v_buckets_3894_ = lean_ctor_get(v_m_3892_, 1);
v___x_3895_ = lean_array_get_size(v_buckets_3894_);
if (lean_obj_tag(v_a_3893_) == 0)
{
uint64_t v___x_3911_; 
v___x_3911_ = 1723ULL;
v___y_3897_ = v___x_3911_;
goto v___jp_3896_;
}
else
{
uint64_t v_hash_3912_; 
v_hash_3912_ = lean_ctor_get_uint64(v_a_3893_, sizeof(void*)*2);
v___y_3897_ = v_hash_3912_;
goto v___jp_3896_;
}
v___jp_3896_:
{
uint64_t v___x_3898_; uint64_t v___x_3899_; uint64_t v_fold_3900_; uint64_t v___x_3901_; uint64_t v___x_3902_; uint64_t v___x_3903_; size_t v___x_3904_; size_t v___x_3905_; size_t v___x_3906_; size_t v___x_3907_; size_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3898_ = 32ULL;
v___x_3899_ = lean_uint64_shift_right(v___y_3897_, v___x_3898_);
v_fold_3900_ = lean_uint64_xor(v___y_3897_, v___x_3899_);
v___x_3901_ = 16ULL;
v___x_3902_ = lean_uint64_shift_right(v_fold_3900_, v___x_3901_);
v___x_3903_ = lean_uint64_xor(v_fold_3900_, v___x_3902_);
v___x_3904_ = lean_uint64_to_usize(v___x_3903_);
v___x_3905_ = lean_usize_of_nat(v___x_3895_);
v___x_3906_ = ((size_t)1ULL);
v___x_3907_ = lean_usize_sub(v___x_3905_, v___x_3906_);
v___x_3908_ = lean_usize_land(v___x_3904_, v___x_3907_);
v___x_3909_ = lean_array_uget_borrowed(v_buckets_3894_, v___x_3908_);
v___x_3910_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3893_, v___x_3909_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3913_, v_a_3914_);
lean_dec(v_a_3914_);
lean_dec_ref(v_m_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v_builderId_3921_; lean_object* v_ref_3922_; lean_object* v_args_3923_; lean_object* v___x_3924_; 
v___x_3919_ = l_Lean_attributeImplBuilderTableRef;
v___x_3920_ = lean_st_ref_get(v___x_3919_);
v_builderId_3921_ = lean_ctor_get(v_e_3917_, 0);
lean_inc(v_builderId_3921_);
v_ref_3922_ = lean_ctor_get(v_e_3917_, 1);
lean_inc(v_ref_3922_);
v_args_3923_ = lean_ctor_get(v_e_3917_, 2);
lean_inc(v_args_3923_);
lean_dec_ref(v_e_3917_);
v___x_3924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3920_, v_builderId_3921_);
lean_dec(v___x_3920_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v___x_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec(v_args_3923_);
lean_dec(v_ref_3922_);
v___x_3925_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3926_ = 1;
v___x_3927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3921_, v___x_3926_);
v___x_3928_ = lean_string_append(v___x_3925_, v___x_3927_);
lean_dec_ref(v___x_3927_);
v___x_3929_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3930_ = lean_string_append(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_mk_io_user_error(v___x_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
return v___x_3932_;
}
else
{
lean_object* v_val_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
lean_dec(v_builderId_3921_);
v_val_3933_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3934_ = lean_apply_2(v_val_3933_, v_ref_3922_, v_args_3923_);
v___x_3935_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3934_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_mkAttributeImplOfEntry(v_e_3936_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3939_, lean_object* v_m_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3940_, v_a_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3943_, lean_object* v_m_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3943_, v_m_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_m_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3947_, lean_object* v_a_3948_, lean_object* v_x_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3948_, v_x_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3951_, lean_object* v_a_3952_, lean_object* v_x_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3951_, v_a_3952_, v_x_3953_);
lean_dec(v_x_3953_);
lean_dec(v_a_3952_);
return v_res_3954_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3956_ = lean_box(0);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v___x_3955_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3958_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = l_Lean_attributeMapRef;
v___x_3962_ = lean_st_ref_get(v___x_3961_);
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3962_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3973_, lean_object* v_opts_3974_, lean_object* v_declName_3975_){
_start:
{
uint8_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = 0;
lean_inc(v_declName_3975_);
lean_inc_ref(v_env_3973_);
v___x_3979_ = l_Lean_Environment_find_x3f(v_env_3973_, v_declName_3975_, v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; uint8_t v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_dec_ref(v_env_3973_);
v___x_3980_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3981_ = 1;
v___x_3982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3975_, v___x_3981_);
v___x_3983_ = lean_string_append(v___x_3980_, v___x_3982_);
lean_dec_ref(v___x_3982_);
v___x_3984_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3985_ = lean_string_append(v___x_3983_, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
return v___x_3986_;
}
else
{
lean_object* v_val_3987_; lean_object* v___x_3988_; 
v_val_3987_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3987_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3988_ = l_Lean_ConstantInfo_type(v_val_3987_);
lean_dec(v_val_3987_);
if (lean_obj_tag(v___x_3988_) == 4)
{
lean_object* v_declName_3989_; 
v_declName_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_declName_3989_);
lean_dec_ref_known(v___x_3988_, 2);
if (lean_obj_tag(v_declName_3989_) == 1)
{
lean_object* v_pre_3990_; 
v_pre_3990_ = lean_ctor_get(v_declName_3989_, 0);
lean_inc(v_pre_3990_);
if (lean_obj_tag(v_pre_3990_) == 1)
{
lean_object* v_pre_3991_; 
v_pre_3991_ = lean_ctor_get(v_pre_3990_, 0);
if (lean_obj_tag(v_pre_3991_) == 0)
{
lean_object* v_str_3992_; lean_object* v_str_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v_str_3992_ = lean_ctor_get(v_declName_3989_, 1);
lean_inc_ref(v_str_3992_);
lean_dec_ref_known(v_declName_3989_, 2);
v_str_3993_ = lean_ctor_get(v_pre_3990_, 1);
lean_inc_ref(v_str_3993_);
lean_dec_ref_known(v_pre_3990_, 2);
v___x_3994_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3995_ = lean_string_dec_eq(v_str_3993_, v___x_3994_);
lean_dec_ref(v_str_3993_);
if (v___x_3995_ == 0)
{
lean_dec_ref(v_str_3992_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
else
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3997_ = lean_string_dec_eq(v_str_3992_, v___x_3996_);
lean_dec_ref(v_str_3992_);
if (v___x_3997_ == 0)
{
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
else
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Environment_evalConst___redArg(v_env_3973_, v_opts_3974_, v_declName_3975_, v___x_3997_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
return v___x_3998_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3990_, 2);
lean_dec_ref_known(v_declName_3989_, 2);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec(v_pre_3990_);
lean_dec_ref_known(v_declName_3989_, 2);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec(v_declName_3989_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
else
{
lean_dec_ref(v___x_3988_);
lean_dec(v_declName_3975_);
lean_dec_ref(v_env_3973_);
goto v___jp_3976_;
}
}
v___jp_3976_:
{
lean_object* v___x_3977_; 
v___x_3977_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3999_, lean_object* v_opts_4000_, lean_object* v_declName_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3999_, v_opts_4000_, v_declName_4001_);
lean_dec_ref(v_opts_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4003_, size_t v_i_4004_, size_t v_stop_4005_, lean_object* v_b_4006_){
_start:
{
uint8_t v___x_4008_; 
v___x_4008_ = lean_usize_dec_eq(v_i_4004_, v_stop_4005_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_array_uget_borrowed(v_as_4003_, v_i_4004_);
lean_inc(v___x_4009_);
v___x_4010_ = l_Lean_mkAttributeImplOfEntry(v___x_4009_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v_toAttributeImplCore_4012_; lean_object* v_name_4013_; lean_object* v___x_4014_; size_t v___x_4015_; size_t v___x_4016_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v_toAttributeImplCore_4012_ = lean_ctor_get(v_a_4011_, 0);
v_name_4013_ = lean_ctor_get(v_toAttributeImplCore_4012_, 1);
lean_inc(v_name_4013_);
v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4006_, v_name_4013_, v_a_4011_);
v___x_4015_ = ((size_t)1ULL);
v___x_4016_ = lean_usize_add(v_i_4004_, v___x_4015_);
v_i_4004_ = v___x_4016_;
v_b_4006_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec_ref(v_b_4006_);
v_a_4018_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4010_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4010_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v_b_4006_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4027_, lean_object* v_i_4028_, lean_object* v_stop_4029_, lean_object* v_b_4030_, lean_object* v___y_4031_){
_start:
{
size_t v_i_boxed_4032_; size_t v_stop_boxed_4033_; lean_object* v_res_4034_; 
v_i_boxed_4032_ = lean_unbox_usize(v_i_4028_);
lean_dec(v_i_4028_);
v_stop_boxed_4033_ = lean_unbox_usize(v_stop_4029_);
lean_dec(v_stop_4029_);
v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4027_, v_i_boxed_4032_, v_stop_boxed_4033_, v_b_4030_);
lean_dec_ref(v_as_4027_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4035_, size_t v_i_4036_, size_t v_stop_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_a_4042_; lean_object* v___y_4047_; uint8_t v___x_4049_; 
v___x_4049_ = lean_usize_dec_eq(v_i_4036_, v_stop_4037_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4050_ = lean_array_uget_borrowed(v_as_4035_, v_i_4036_);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = lean_array_get_size(v___x_4050_);
v___x_4053_ = lean_nat_dec_lt(v___x_4051_, v___x_4052_);
if (v___x_4053_ == 0)
{
v_a_4042_ = v_b_4038_;
goto v___jp_4041_;
}
else
{
uint8_t v___x_4054_; 
v___x_4054_ = lean_nat_dec_le(v___x_4052_, v___x_4052_);
if (v___x_4054_ == 0)
{
if (v___x_4053_ == 0)
{
v_a_4042_ = v_b_4038_;
goto v___jp_4041_;
}
else
{
size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = ((size_t)0ULL);
v___x_4056_ = lean_usize_of_nat(v___x_4052_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4050_, v___x_4055_, v___x_4056_, v_b_4038_);
v___y_4047_ = v___x_4057_;
goto v___jp_4046_;
}
}
else
{
size_t v___x_4058_; size_t v___x_4059_; lean_object* v___x_4060_; 
v___x_4058_ = ((size_t)0ULL);
v___x_4059_ = lean_usize_of_nat(v___x_4052_);
v___x_4060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4050_, v___x_4058_, v___x_4059_, v_b_4038_);
v___y_4047_ = v___x_4060_;
goto v___jp_4046_;
}
}
}
else
{
lean_object* v___x_4061_; 
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v_b_4038_);
return v___x_4061_;
}
v___jp_4041_:
{
size_t v___x_4043_; size_t v___x_4044_; 
v___x_4043_ = ((size_t)1ULL);
v___x_4044_ = lean_usize_add(v_i_4036_, v___x_4043_);
v_i_4036_ = v___x_4044_;
v_b_4038_ = v_a_4042_;
goto _start;
}
v___jp_4046_:
{
if (lean_obj_tag(v___y_4047_) == 0)
{
lean_object* v_a_4048_; 
v_a_4048_ = lean_ctor_get(v___y_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___y_4047_, 1);
v_a_4042_ = v_a_4048_;
goto v___jp_4041_;
}
else
{
return v___y_4047_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4062_, lean_object* v_i_4063_, lean_object* v_stop_4064_, lean_object* v_b_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
size_t v_i_boxed_4068_; size_t v_stop_boxed_4069_; lean_object* v_res_4070_; 
v_i_boxed_4068_ = lean_unbox_usize(v_i_4063_);
lean_dec(v_i_4063_);
v_stop_boxed_4069_ = lean_unbox_usize(v_stop_4064_);
lean_dec(v_stop_4064_);
v_res_4070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4062_, v_i_boxed_4068_, v_stop_boxed_4069_, v_b_4065_, v___y_4066_);
lean_dec_ref(v___y_4066_);
lean_dec_ref(v_as_4062_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_a_4075_; lean_object* v___y_4080_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v___x_4090_ = l_Lean_attributeMapRef;
v___x_4091_ = lean_st_ref_get(v___x_4090_);
v___x_4092_ = lean_unsigned_to_nat(0u);
v___x_4093_ = lean_array_get_size(v_es_4071_);
v___x_4094_ = lean_nat_dec_lt(v___x_4092_, v___x_4093_);
if (v___x_4094_ == 0)
{
v_a_4075_ = v___x_4091_;
goto v___jp_4074_;
}
else
{
uint8_t v___x_4095_; 
v___x_4095_ = lean_nat_dec_le(v___x_4093_, v___x_4093_);
if (v___x_4095_ == 0)
{
if (v___x_4094_ == 0)
{
v_a_4075_ = v___x_4091_;
goto v___jp_4074_;
}
else
{
size_t v___x_4096_; size_t v___x_4097_; lean_object* v___x_4098_; 
v___x_4096_ = ((size_t)0ULL);
v___x_4097_ = lean_usize_of_nat(v___x_4093_);
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4071_, v___x_4096_, v___x_4097_, v___x_4091_, v_a_4072_);
v___y_4080_ = v___x_4098_;
goto v___jp_4079_;
}
}
else
{
size_t v___x_4099_; size_t v___x_4100_; lean_object* v___x_4101_; 
v___x_4099_ = ((size_t)0ULL);
v___x_4100_ = lean_usize_of_nat(v___x_4093_);
v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4071_, v___x_4099_, v___x_4100_, v___x_4091_, v_a_4072_);
v___y_4080_ = v___x_4101_;
goto v___jp_4079_;
}
}
v___jp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = lean_box(0);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
lean_ctor_set(v___x_4077_, 1, v_a_4075_);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
v___jp_4079_:
{
if (lean_obj_tag(v___y_4080_) == 0)
{
lean_object* v_a_4081_; 
v_a_4081_ = lean_ctor_get(v___y_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___y_4080_, 1);
v_a_4075_ = v_a_4081_;
goto v___jp_4074_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
v_a_4082_ = lean_ctor_get(v___y_4080_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___y_4080_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___y_4080_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___y_4080_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4102_, v_a_4103_);
lean_dec_ref(v_a_4103_);
lean_dec_ref(v_es_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4106_, size_t v_i_4107_, size_t v_stop_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v___x_4112_; 
v___x_4112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4106_, v_i_4107_, v_stop_4108_, v_b_4109_);
return v___x_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4113_, lean_object* v_i_4114_, lean_object* v_stop_4115_, lean_object* v_b_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
size_t v_i_boxed_4119_; size_t v_stop_boxed_4120_; lean_object* v_res_4121_; 
v_i_boxed_4119_ = lean_unbox_usize(v_i_4114_);
lean_dec(v_i_4114_);
v_stop_boxed_4120_ = lean_unbox_usize(v_stop_4115_);
lean_dec(v_stop_4115_);
v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4113_, v_i_boxed_4119_, v_stop_boxed_4120_, v_b_4116_, v___y_4117_);
lean_dec_ref(v___y_4117_);
lean_dec_ref(v_as_4113_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4122_, lean_object* v_e_4123_){
_start:
{
lean_object* v_snd_4124_; lean_object* v_toAttributeImplCore_4125_; lean_object* v_fst_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4144_; 
v_snd_4124_ = lean_ctor_get(v_e_4123_, 1);
lean_inc(v_snd_4124_);
v_toAttributeImplCore_4125_ = lean_ctor_get(v_snd_4124_, 0);
v_fst_4126_ = lean_ctor_get(v_e_4123_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_e_4123_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_e_4123_, 1);
lean_dec(v_unused_4145_);
v___x_4128_ = v_e_4123_;
v_isShared_4129_ = v_isSharedCheck_4144_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_fst_4126_);
lean_dec(v_e_4123_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4144_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_newEntries_4130_; lean_object* v_map_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4143_; 
v_newEntries_4130_ = lean_ctor_get(v_s_4122_, 0);
v_map_4131_ = lean_ctor_get(v_s_4122_, 1);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_s_4122_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4133_ = v_s_4122_;
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_map_4131_);
lean_inc(v_newEntries_4130_);
lean_dec(v_s_4122_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_name_4135_; lean_object* v___x_4137_; 
v_name_4135_ = lean_ctor_get(v_toAttributeImplCore_4125_, 1);
lean_inc(v_name_4135_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 1);
lean_ctor_set(v___x_4128_, 1, v_newEntries_4130_);
v___x_4137_ = v___x_4128_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_fst_4126_);
lean_ctor_set(v_reuseFailAlloc_4142_, 1, v_newEntries_4130_);
v___x_4137_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4131_, v_name_4135_, v_snd_4124_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 1, v___x_4138_);
lean_ctor_set(v___x_4133_, 0, v___x_4137_);
v___x_4140_ = v___x_4133_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4146_, lean_object* v_s_4147_){
_start:
{
lean_object* v_newEntries_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_newEntries_4148_ = lean_ctor_get(v_s_4147_, 0);
lean_inc(v_newEntries_4148_);
lean_dec_ref(v_s_4147_);
v___x_4149_ = l_List_reverse___redArg(v_newEntries_4148_);
v___x_4150_ = lean_array_mk(v___x_4149_);
lean_inc_ref_n(v___x_4150_, 2);
v___x_4151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
lean_ctor_set(v___x_4151_, 2, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4152_, lean_object* v_s_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4152_, v_s_4153_);
lean_dec_ref(v_x_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4155_){
_start:
{
lean_object* v_newEntries_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4167_; 
v_newEntries_4156_ = lean_ctor_get(v_s_4155_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_s_4155_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; 
v_unused_4168_ = lean_ctor_get(v_s_4155_, 1);
lean_dec(v_unused_4168_);
v___x_4158_ = v_s_4155_;
v_isShared_4159_ = v_isSharedCheck_4167_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_newEntries_4156_);
lean_dec(v_s_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4167_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4160_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4161_ = l_List_lengthTR___redArg(v_newEntries_4156_);
lean_dec(v_newEntries_4156_);
v___x_4162_ = l_Nat_reprFast(v___x_4161_);
v___x_4163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set_tag(v___x_4158_, 5);
lean_ctor_set(v___x_4158_, 1, v___x_4163_);
lean_ctor_set(v___x_4158_, 0, v___x_4160_);
v___x_4165_ = v___x_4158_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4169_){
_start:
{
lean_object* v_newEntries_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_newEntries_4170_ = lean_ctor_get(v_s_4169_, 0);
lean_inc(v_newEntries_4170_);
lean_dec_ref(v_s_4169_);
v___x_4171_ = l_List_reverse___redArg(v_newEntries_4170_);
v___x_4172_ = lean_array_mk(v___x_4171_);
return v___x_4172_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___f_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4182_ = lean_box(0);
v___x_4183_ = lean_box(2);
v___f_4184_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4185_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4186_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4187_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4188_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4190_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
lean_ctor_set(v___x_4190_, 2, v___x_4187_);
lean_ctor_set(v___x_4190_, 3, v___x_4186_);
lean_ctor_set(v___x_4190_, 4, v___f_4185_);
lean_ctor_set(v___x_4190_, 5, v___f_4184_);
lean_ctor_set(v___x_4190_, 6, v___x_4183_);
lean_ctor_set(v___x_4190_, 7, v___x_4182_);
return v___x_4190_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___f_4191_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4192_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___f_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4196_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4201_ = l_Lean_attributeMapRef;
v___x_4202_ = lean_st_ref_get(v___x_4201_);
v___x_4203_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4202_, v_n_4199_);
lean_dec(v___x_4202_);
v___x_4204_ = lean_box(v___x_4203_);
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_isBuiltinAttribute(v_n_4206_);
lean_dec(v_n_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4209_, lean_object* v_x_4210_){
_start:
{
if (lean_obj_tag(v_x_4210_) == 0)
{
return v_x_4209_;
}
else
{
lean_object* v_key_4211_; lean_object* v_tail_4212_; lean_object* v___x_4213_; 
v_key_4211_ = lean_ctor_get(v_x_4210_, 0);
v_tail_4212_ = lean_ctor_get(v_x_4210_, 2);
lean_inc(v_key_4211_);
v___x_4213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4213_, 0, v_key_4211_);
lean_ctor_set(v___x_4213_, 1, v_x_4209_);
v_x_4209_ = v___x_4213_;
v_x_4210_ = v_tail_4212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4215_, lean_object* v_x_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4215_, v_x_4216_);
lean_dec(v_x_4216_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4218_, size_t v_i_4219_, size_t v_stop_4220_, lean_object* v_b_4221_){
_start:
{
uint8_t v___x_4222_; 
v___x_4222_ = lean_usize_dec_eq(v_i_4219_, v_stop_4220_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; size_t v___x_4225_; size_t v___x_4226_; 
v___x_4223_ = lean_array_uget_borrowed(v_as_4218_, v_i_4219_);
v___x_4224_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4221_, v___x_4223_);
v___x_4225_ = ((size_t)1ULL);
v___x_4226_ = lean_usize_add(v_i_4219_, v___x_4225_);
v_i_4219_ = v___x_4226_;
v_b_4221_ = v___x_4224_;
goto _start;
}
else
{
return v_b_4221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_stop_4230_, lean_object* v_b_4231_){
_start:
{
size_t v_i_boxed_4232_; size_t v_stop_boxed_4233_; lean_object* v_res_4234_; 
v_i_boxed_4232_ = lean_unbox_usize(v_i_4229_);
lean_dec(v_i_4229_);
v_stop_boxed_4233_ = lean_unbox_usize(v_stop_4230_);
lean_dec(v_stop_4230_);
v_res_4234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4228_, v_i_boxed_4232_, v_stop_boxed_4233_, v_b_4231_);
lean_dec_ref(v_as_4228_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_buckets_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4236_ = l_Lean_attributeMapRef;
v___x_4237_ = lean_st_ref_get(v___x_4236_);
v_buckets_4238_ = lean_ctor_get(v___x_4237_, 1);
lean_inc_ref(v_buckets_4238_);
lean_dec(v___x_4237_);
v___x_4239_ = lean_box(0);
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_array_get_size(v_buckets_4238_);
v___x_4242_ = lean_nat_dec_lt(v___x_4240_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
lean_dec_ref(v_buckets_4238_);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4239_);
return v___x_4243_;
}
else
{
uint8_t v___x_4244_; 
v___x_4244_ = lean_nat_dec_le(v___x_4241_, v___x_4241_);
if (v___x_4244_ == 0)
{
if (v___x_4242_ == 0)
{
lean_object* v___x_4245_; 
lean_dec_ref(v_buckets_4238_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4239_);
return v___x_4245_;
}
else
{
size_t v___x_4246_; size_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4246_ = ((size_t)0ULL);
v___x_4247_ = lean_usize_of_nat(v___x_4241_);
v___x_4248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4238_, v___x_4246_, v___x_4247_, v___x_4239_);
lean_dec_ref(v_buckets_4238_);
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4248_);
return v___x_4249_;
}
}
else
{
size_t v___x_4250_; size_t v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4250_ = ((size_t)0ULL);
v___x_4251_ = lean_usize_of_nat(v___x_4241_);
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4238_, v___x_4250_, v___x_4251_, v___x_4239_);
lean_dec_ref(v_buckets_4238_);
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
return v___x_4253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_getBuiltinAttributeNames();
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4257_){
_start:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = l_Lean_attributeMapRef;
v___x_4260_ = lean_st_ref_get(v___x_4259_);
v___x_4261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4260_, v_attrName_4257_);
lean_dec(v___x_4260_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v___x_4262_; uint8_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4262_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4263_ = 1;
v___x_4264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4257_, v___x_4263_);
v___x_4265_ = lean_string_append(v___x_4262_, v___x_4264_);
lean_dec_ref(v___x_4264_);
v___x_4266_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4267_ = lean_string_append(v___x_4265_, v___x_4266_);
v___x_4268_ = lean_mk_io_user_error(v___x_4267_);
v___x_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
else
{
lean_object* v_val_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_attrName_4257_);
v_val_4270_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4261_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_val_4270_);
lean_dec(v___x_4261_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set_tag(v___x_4272_, 0);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_val_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4278_);
return v_res_4280_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4281_, lean_object* v_attrName_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v_toEnvExtension_4284_; lean_object* v_asyncMode_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v_map_4289_; uint8_t v___x_4290_; 
v___x_4283_ = l_Lean_attributeExtension;
v_toEnvExtension_4284_ = lean_ctor_get(v___x_4283_, 0);
v_asyncMode_4285_ = lean_ctor_get(v_toEnvExtension_4284_, 2);
v___x_4286_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4287_ = lean_box(0);
v___x_4288_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4286_, v___x_4283_, v_env_4281_, v_asyncMode_4285_, v___x_4287_);
v_map_4289_ = lean_ctor_get(v___x_4288_, 1);
lean_inc_ref(v_map_4289_);
lean_dec(v___x_4288_);
v___x_4290_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4289_, v_attrName_4282_);
lean_dec_ref(v_map_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4291_, lean_object* v_attrName_4292_){
_start:
{
uint8_t v_res_4293_; lean_object* v_r_4294_; 
v_res_4293_ = l_Lean_isAttribute(v_env_4291_, v_attrName_4292_);
lean_dec(v_attrName_4292_);
v_r_4294_ = lean_box(v_res_4293_);
return v_r_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4295_){
_start:
{
lean_object* v___x_4296_; lean_object* v_toEnvExtension_4297_; lean_object* v_asyncMode_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v_map_4302_; lean_object* v_buckets_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4296_ = l_Lean_attributeExtension;
v_toEnvExtension_4297_ = lean_ctor_get(v___x_4296_, 0);
v_asyncMode_4298_ = lean_ctor_get(v_toEnvExtension_4297_, 2);
v___x_4299_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4300_ = lean_box(0);
v___x_4301_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4299_, v___x_4296_, v_env_4295_, v_asyncMode_4298_, v___x_4300_);
v_map_4302_ = lean_ctor_get(v___x_4301_, 1);
lean_inc_ref(v_map_4302_);
lean_dec(v___x_4301_);
v_buckets_4303_ = lean_ctor_get(v_map_4302_, 1);
lean_inc_ref(v_buckets_4303_);
lean_dec_ref(v_map_4302_);
v___x_4304_ = lean_box(0);
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = lean_array_get_size(v_buckets_4303_);
v___x_4307_ = lean_nat_dec_lt(v___x_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_dec_ref(v_buckets_4303_);
return v___x_4304_;
}
else
{
uint8_t v___x_4308_; 
v___x_4308_ = lean_nat_dec_le(v___x_4306_, v___x_4306_);
if (v___x_4308_ == 0)
{
if (v___x_4307_ == 0)
{
lean_dec_ref(v_buckets_4303_);
return v___x_4304_;
}
else
{
size_t v___x_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v___x_4309_ = ((size_t)0ULL);
v___x_4310_ = lean_usize_of_nat(v___x_4306_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4303_, v___x_4309_, v___x_4310_, v___x_4304_);
lean_dec_ref(v_buckets_4303_);
return v___x_4311_;
}
}
else
{
size_t v___x_4312_; size_t v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = ((size_t)0ULL);
v___x_4313_ = lean_usize_of_nat(v___x_4306_);
v___x_4314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4303_, v___x_4312_, v___x_4313_, v___x_4304_);
lean_dec_ref(v_buckets_4303_);
return v___x_4314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4315_, lean_object* v_attrName_4316_){
_start:
{
lean_object* v___x_4317_; lean_object* v_toEnvExtension_4318_; lean_object* v_asyncMode_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v_map_4323_; lean_object* v___x_4324_; 
v___x_4317_ = l_Lean_attributeExtension;
v_toEnvExtension_4318_ = lean_ctor_get(v___x_4317_, 0);
v_asyncMode_4319_ = lean_ctor_get(v_toEnvExtension_4318_, 2);
v___x_4320_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4321_ = lean_box(0);
v___x_4322_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4320_, v___x_4317_, v_env_4315_, v_asyncMode_4319_, v___x_4321_);
v_map_4323_ = lean_ctor_get(v___x_4322_, 1);
lean_inc_ref(v_map_4323_);
lean_dec(v___x_4322_);
v___x_4324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4323_, v_attrName_4316_);
lean_dec_ref(v_map_4323_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v___x_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4325_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4326_ = 1;
v___x_4327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4316_, v___x_4326_);
v___x_4328_ = lean_string_append(v___x_4325_, v___x_4327_);
lean_dec_ref(v___x_4327_);
v___x_4329_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4330_ = lean_string_append(v___x_4328_, v___x_4329_);
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec(v_attrName_4316_);
v_val_4332_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4324_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_val_4332_);
lean_dec(v___x_4324_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_val_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4340_, lean_object* v_builderId_4341_, lean_object* v_ref_4342_, lean_object* v_args_4343_){
_start:
{
lean_object* v_entry_4345_; lean_object* v___x_4346_; 
v_entry_4345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4345_, 0, v_builderId_4341_);
lean_ctor_set(v_entry_4345_, 1, v_ref_4342_);
lean_ctor_set(v_entry_4345_, 2, v_args_4343_);
lean_inc_ref(v_entry_4345_);
v___x_4346_ = l_Lean_mkAttributeImplOfEntry(v_entry_4345_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4372_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4349_ = v___x_4346_;
v_isShared_4350_ = v_isSharedCheck_4372_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4372_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v_toAttributeImplCore_4351_; lean_object* v_name_4352_; uint8_t v___x_4353_; 
v_toAttributeImplCore_4351_ = lean_ctor_get(v_a_4347_, 0);
v_name_4352_ = lean_ctor_get(v_toAttributeImplCore_4351_, 1);
lean_inc_ref(v_env_4340_);
v___x_4353_ = l_Lean_isAttribute(v_env_4340_, v_name_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; lean_object* v_toEnvExtension_4355_; lean_object* v_asyncMode_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4361_; 
v___x_4354_ = l_Lean_attributeExtension;
v_toEnvExtension_4355_ = lean_ctor_get(v___x_4354_, 0);
v_asyncMode_4356_ = lean_ctor_get(v_toEnvExtension_4355_, 2);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v_entry_4345_);
lean_ctor_set(v___x_4357_, 1, v_a_4347_);
v___x_4358_ = lean_box(0);
v___x_4359_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4354_, v_env_4340_, v___x_4357_, v_asyncMode_4356_, v___x_4358_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v___x_4359_);
v___x_4361_ = v___x_4349_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
else
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4370_; 
lean_inc(v_name_4352_);
lean_dec(v_a_4347_);
lean_dec_ref_known(v_entry_4345_, 3);
lean_dec_ref(v_env_4340_);
v___x_4363_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4364_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4352_, v___x_4353_);
v___x_4365_ = lean_string_append(v___x_4363_, v___x_4364_);
lean_dec_ref(v___x_4364_);
v___x_4366_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4367_ = lean_string_append(v___x_4365_, v___x_4366_);
v___x_4368_ = lean_mk_io_user_error(v___x_4367_);
if (v_isShared_4350_ == 0)
{
lean_ctor_set_tag(v___x_4349_, 1);
lean_ctor_set(v___x_4349_, 0, v___x_4368_);
v___x_4370_ = v___x_4349_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec_ref_known(v_entry_4345_, 3);
lean_dec_ref(v_env_4340_);
v_a_4373_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4346_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4346_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4381_, lean_object* v_builderId_4382_, lean_object* v_ref_4383_, lean_object* v_args_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_registerAttributeOfBuilder(v_env_4381_, v_builderId_4382_, v_ref_4383_, v_args_4384_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
if (lean_obj_tag(v_x_4387_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_a_4391_ = lean_ctor_get(v_x_4387_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v_x_4387_, 1);
v___x_4392_ = l_Lean_stringToMessageData(v_a_4391_);
v___x_4393_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4392_, v___y_4388_, v___y_4389_);
return v___x_4393_;
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v_x_4387_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_x_4387_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v_x_4387_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v_x_4387_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
lean_ctor_set_tag(v___x_4396_, 0);
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4407_, lean_object* v_attrName_4408_, lean_object* v_stx_4409_, uint8_t v_kind_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
lean_object* v___x_4414_; lean_object* v_env_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4414_ = lean_st_ref_get(v_a_4412_);
v_env_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc_ref(v_env_4415_);
lean_dec(v___x_4414_);
v___x_4416_ = l_Lean_getAttributeImpl(v_env_4415_, v_attrName_4408_);
v___x_4417_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4416_, v_a_4411_, v_a_4412_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v_add_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v_add_4419_ = lean_ctor_get(v_a_4418_, 1);
lean_inc_ref(v_add_4419_);
lean_dec(v_a_4418_);
v___x_4420_ = lean_box(v_kind_4410_);
lean_inc(v_a_4412_);
lean_inc_ref(v_a_4411_);
v___x_4421_ = lean_apply_6(v_add_4419_, v_declName_4407_, v_stx_4409_, v___x_4420_, v_a_4411_, v_a_4412_, lean_box(0));
return v___x_4421_;
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_stx_4409_);
lean_dec(v_declName_4407_);
v_a_4422_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4417_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4417_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4430_, lean_object* v_attrName_4431_, lean_object* v_stx_4432_, lean_object* v_kind_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
uint8_t v_kind_boxed_4437_; lean_object* v_res_4438_; 
v_kind_boxed_4437_ = lean_unbox(v_kind_4433_);
v_res_4438_ = l_Lean_Attribute_add(v_declName_4430_, v_attrName_4431_, v_stx_4432_, v_kind_boxed_4437_, v_a_4434_, v_a_4435_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4439_, lean_object* v_x_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4440_, v___y_4441_, v___y_4442_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4445_, lean_object* v_x_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4445_, v_x_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4451_, lean_object* v_attrName_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v___x_4456_; lean_object* v_env_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4456_ = lean_st_ref_get(v_a_4454_);
v_env_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc_ref(v_env_4457_);
lean_dec(v___x_4456_);
v___x_4458_ = l_Lean_getAttributeImpl(v_env_4457_, v_attrName_4452_);
v___x_4459_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4458_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v_erase_4461_; lean_object* v___x_4462_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v_erase_4461_ = lean_ctor_get(v_a_4460_, 2);
lean_inc_ref(v_erase_4461_);
lean_dec(v_a_4460_);
lean_inc(v_a_4454_);
lean_inc_ref(v_a_4453_);
v___x_4462_ = lean_apply_4(v_erase_4461_, v_declName_4451_, v_a_4453_, v_a_4454_, lean_box(0));
return v___x_4462_;
}
else
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4470_; 
lean_dec(v_declName_4451_);
v_a_4463_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4465_ = v___x_4459_;
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v___x_4459_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4470_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4471_, lean_object* v_attrName_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Lean_Attribute_erase(v_declName_4471_, v_attrName_4472_, v_a_4473_, v_a_4474_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4477_, lean_object* v_x_4478_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
return v_x_4477_;
}
else
{
lean_object* v_key_4479_; lean_object* v_value_4480_; lean_object* v_tail_4481_; lean_object* v_newEntries_4482_; lean_object* v_map_4483_; uint8_t v___x_4484_; 
v_key_4479_ = lean_ctor_get(v_x_4478_, 0);
lean_inc(v_key_4479_);
v_value_4480_ = lean_ctor_get(v_x_4478_, 1);
lean_inc(v_value_4480_);
v_tail_4481_ = lean_ctor_get(v_x_4478_, 2);
lean_inc(v_tail_4481_);
lean_dec_ref_known(v_x_4478_, 3);
v_newEntries_4482_ = lean_ctor_get(v_x_4477_, 0);
v_map_4483_ = lean_ctor_get(v_x_4477_, 1);
v___x_4484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4483_, v_key_4479_);
if (v___x_4484_ == 0)
{
lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4493_; 
lean_inc_ref(v_map_4483_);
lean_inc(v_newEntries_4482_);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_x_4477_);
if (v_isSharedCheck_4493_ == 0)
{
lean_object* v_unused_4494_; lean_object* v_unused_4495_; 
v_unused_4494_ = lean_ctor_get(v_x_4477_, 1);
lean_dec(v_unused_4494_);
v_unused_4495_ = lean_ctor_get(v_x_4477_, 0);
lean_dec(v_unused_4495_);
v___x_4486_ = v_x_4477_;
v_isShared_4487_ = v_isSharedCheck_4493_;
goto v_resetjp_4485_;
}
else
{
lean_dec(v_x_4477_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4493_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; lean_object* v___x_4490_; 
v___x_4488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4483_, v_key_4479_, v_value_4480_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 1, v___x_4488_);
v___x_4490_ = v___x_4486_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_newEntries_4482_);
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v___x_4488_);
v___x_4490_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
v_x_4477_ = v___x_4490_;
v_x_4478_ = v_tail_4481_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4480_);
lean_dec(v_key_4479_);
v_x_4478_ = v_tail_4481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4497_, size_t v_i_4498_, size_t v_stop_4499_, lean_object* v_b_4500_){
_start:
{
uint8_t v___x_4501_; 
v___x_4501_ = lean_usize_dec_eq(v_i_4498_, v_stop_4499_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v___x_4503_; size_t v___x_4504_; size_t v___x_4505_; 
v___x_4502_ = lean_array_uget_borrowed(v_as_4497_, v_i_4498_);
lean_inc(v___x_4502_);
v___x_4503_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4500_, v___x_4502_);
v___x_4504_ = ((size_t)1ULL);
v___x_4505_ = lean_usize_add(v_i_4498_, v___x_4504_);
v_i_4498_ = v___x_4505_;
v_b_4500_ = v___x_4503_;
goto _start;
}
else
{
return v_b_4500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4507_, lean_object* v_i_4508_, lean_object* v_stop_4509_, lean_object* v_b_4510_){
_start:
{
size_t v_i_boxed_4511_; size_t v_stop_boxed_4512_; lean_object* v_res_4513_; 
v_i_boxed_4511_ = lean_unbox_usize(v_i_4508_);
lean_dec(v_i_4508_);
v_stop_boxed_4512_ = lean_unbox_usize(v_stop_4509_);
lean_dec(v_stop_4509_);
v_res_4513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4507_, v_i_boxed_4511_, v_stop_boxed_4512_, v_b_4510_);
lean_dec_ref(v_as_4507_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___y_4520_; lean_object* v_toEnvExtension_4523_; lean_object* v_asyncMode_4524_; lean_object* v_buckets_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; uint8_t v___x_4531_; 
v___x_4516_ = l_Lean_attributeMapRef;
v___x_4517_ = lean_st_ref_get(v___x_4516_);
v___x_4518_ = l_Lean_attributeExtension;
v_toEnvExtension_4523_ = lean_ctor_get(v___x_4518_, 0);
v_asyncMode_4524_ = lean_ctor_get(v_toEnvExtension_4523_, 2);
v_buckets_4525_ = lean_ctor_get(v___x_4517_, 1);
lean_inc_ref(v_buckets_4525_);
lean_dec(v___x_4517_);
v___x_4526_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4527_ = lean_box(0);
lean_inc_ref(v_env_4514_);
v___x_4528_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4526_, v___x_4518_, v_env_4514_, v_asyncMode_4524_, v___x_4527_);
v___x_4529_ = lean_unsigned_to_nat(0u);
v___x_4530_ = lean_array_get_size(v_buckets_4525_);
v___x_4531_ = lean_nat_dec_lt(v___x_4529_, v___x_4530_);
if (v___x_4531_ == 0)
{
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4528_;
goto v___jp_4519_;
}
else
{
uint8_t v___x_4532_; 
v___x_4532_ = lean_nat_dec_le(v___x_4530_, v___x_4530_);
if (v___x_4532_ == 0)
{
if (v___x_4531_ == 0)
{
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4528_;
goto v___jp_4519_;
}
else
{
size_t v___x_4533_; size_t v___x_4534_; lean_object* v___x_4535_; 
v___x_4533_ = ((size_t)0ULL);
v___x_4534_ = lean_usize_of_nat(v___x_4530_);
v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4525_, v___x_4533_, v___x_4534_, v___x_4528_);
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4535_;
goto v___jp_4519_;
}
}
else
{
size_t v___x_4536_; size_t v___x_4537_; lean_object* v___x_4538_; 
v___x_4536_ = ((size_t)0ULL);
v___x_4537_ = lean_usize_of_nat(v___x_4530_);
v___x_4538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4525_, v___x_4536_, v___x_4537_, v___x_4528_);
lean_dec_ref(v_buckets_4525_);
v___y_4520_ = v___x_4538_;
goto v___jp_4519_;
}
}
v___jp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4518_, v_env_4514_, v___y_4520_);
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = lean_update_env_attributes(v_env_4539_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v_size_4545_; lean_object* v___x_4546_; 
v___x_4543_ = l_Lean_attributeMapRef;
v___x_4544_ = lean_st_ref_get(v___x_4543_);
v_size_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_size_4545_);
lean_dec(v___x_4544_);
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v_size_4545_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = lean_get_num_attributes();
return v_res_4548_;
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
