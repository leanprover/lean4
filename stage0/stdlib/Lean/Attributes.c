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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_21__boxed_71_; uint8_t v_y_22__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_21__boxed_71_ = lean_unbox(v_x_69_);
v_y_22__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_21__boxed_71_, v_y_22__boxed_72_);
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
v_options_84_ = lean_ctor_get(v___y_79_, 1);
v_ref_85_ = lean_ctor_get(v___y_79_, 4);
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
uint8_t v_x_21__boxed_275_; uint8_t v_y_22__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_21__boxed_275_ = lean_unbox(v_x_273_);
v_y_22__boxed_276_ = lean_unbox(v_y_274_);
v_res_277_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_275_, v_y_22__boxed_276_);
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
uint8_t v___y_1008__boxed_312_; lean_object* v_res_313_; 
v___y_1008__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_1008__boxed_312_, v___y_309_, v___y_310_);
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
v___x_319_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_319_, 10, v___x_317_);
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
v_options_339_ = lean_ctor_get(v___y_334_, 1);
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
v_ref_354_ = lean_ctor_get(v___y_351_, 4);
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
v___x_600_ = lean_st_ref_put(v___x_590_, v___x_599_);
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
lean_object* v_toCold_657_; lean_object* v_options_658_; lean_object* v_currRecDepth_659_; lean_object* v_maxRecDepth_660_; lean_object* v_ref_661_; lean_object* v_currNamespace_662_; lean_object* v_openDecls_663_; lean_object* v_initHeartbeats_664_; lean_object* v_maxHeartbeats_665_; lean_object* v_currMacroScope_666_; uint8_t v_diag_667_; uint8_t v_suppressElabErrors_668_; lean_object* v_ref_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_toCold_657_ = lean_ctor_get(v___y_654_, 0);
v_options_658_ = lean_ctor_get(v___y_654_, 1);
v_currRecDepth_659_ = lean_ctor_get(v___y_654_, 2);
v_maxRecDepth_660_ = lean_ctor_get(v___y_654_, 3);
v_ref_661_ = lean_ctor_get(v___y_654_, 4);
v_currNamespace_662_ = lean_ctor_get(v___y_654_, 5);
v_openDecls_663_ = lean_ctor_get(v___y_654_, 6);
v_initHeartbeats_664_ = lean_ctor_get(v___y_654_, 7);
v_maxHeartbeats_665_ = lean_ctor_get(v___y_654_, 8);
v_currMacroScope_666_ = lean_ctor_get(v___y_654_, 9);
v_diag_667_ = lean_ctor_get_uint8(v___y_654_, sizeof(void*)*10);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_654_, sizeof(void*)*10 + 1);
v_ref_669_ = l_Lean_replaceRef(v_ref_652_, v_ref_661_);
lean_inc(v_currMacroScope_666_);
lean_inc(v_maxHeartbeats_665_);
lean_inc(v_initHeartbeats_664_);
lean_inc(v_openDecls_663_);
lean_inc(v_currNamespace_662_);
lean_inc(v_maxRecDepth_660_);
lean_inc(v_currRecDepth_659_);
lean_inc_ref(v_options_658_);
lean_inc_ref(v_toCold_657_);
v___x_670_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_670_, 0, v_toCold_657_);
lean_ctor_set(v___x_670_, 1, v_options_658_);
lean_ctor_set(v___x_670_, 2, v_currRecDepth_659_);
lean_ctor_set(v___x_670_, 3, v_maxRecDepth_660_);
lean_ctor_set(v___x_670_, 4, v_ref_669_);
lean_ctor_set(v___x_670_, 5, v_currNamespace_662_);
lean_ctor_set(v___x_670_, 6, v_openDecls_663_);
lean_ctor_set(v___x_670_, 7, v_initHeartbeats_664_);
lean_ctor_set(v___x_670_, 8, v_maxHeartbeats_665_);
lean_ctor_set(v___x_670_, 9, v_currMacroScope_666_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*10, v_diag_667_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*10 + 1, v_suppressElabErrors_668_);
v___x_671_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_653_, v___x_670_, v___y_655_);
lean_dec_ref_known(v___x_670_, 10);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_672_, lean_object* v_msg_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_672_, v_msg_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v_ref_672_);
return v_res_677_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v___x_698_; uint8_t v___y_709_; lean_object* v___x_715_; uint8_t v___x_716_; 
lean_inc(v_stx_694_);
v___x_698_ = l_Lean_Syntax_getKind(v_stx_694_);
v___x_715_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_716_ = lean_name_eq(v___x_698_, v___x_715_);
if (v___x_716_ == 0)
{
v___y_709_ = v___x_716_;
goto v___jp_708_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_717_);
v___x_719_ = l_Lean_Syntax_isNone(v___x_718_);
lean_dec(v___x_718_);
v___y_709_ = v___x_719_;
goto v___jp_708_;
}
v___jp_699_:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_701_ = lean_name_eq(v___x_698_, v___x_700_);
lean_dec(v___x_698_);
if (v___x_701_ == 0)
{
if (lean_obj_tag(v_stx_694_) == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_705_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_694_, v___x_704_, v_a_695_, v_a_696_);
lean_dec(v_stx_694_);
return v___x_705_;
}
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_dec(v_stx_694_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
v___jp_708_:
{
if (v___y_709_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_unsigned_to_nat(2u);
v___x_711_ = l_Lean_Syntax_getArg(v_stx_694_, v___x_710_);
v___x_712_ = l_Lean_Syntax_isNone(v___x_711_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
goto v___jp_699_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v___x_698_);
lean_dec(v_stx_694_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_725_, lean_object* v_ref_726_, lean_object* v_msg_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_726_, v_msg_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_732_, lean_object* v_ref_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_732_, v_ref_733_, v_msg_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v_ref_733_);
return v_res_738_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
lean_inc(v_stx_754_);
v___x_766_ = l_Lean_Syntax_getKind(v_stx_754_);
v___x_767_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_768_ = lean_name_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_770_ = lean_name_eq(v___x_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_772_ = lean_name_eq(v___x_766_, v___x_771_);
lean_dec(v___x_766_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_774_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_754_, v___x_773_, v_a_755_, v_a_756_);
lean_dec(v_stx_754_);
return v___x_774_;
}
else
{
goto v___jp_758_;
}
}
else
{
lean_dec(v___x_766_);
goto v___jp_758_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
lean_dec(v___x_766_);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = l_Lean_Syntax_getArg(v_stx_754_, v___x_775_);
lean_dec(v_stx_754_);
v___x_777_ = l_Lean_Syntax_isNone(v___x_776_);
if (v___x_777_ == 0)
{
if (v___x_768_ == 0)
{
lean_dec(v___x_776_);
goto v___jp_763_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Lean_Syntax_getArg(v___x_776_, v___x_778_);
lean_dec(v___x_776_);
v___x_780_ = l_Lean_Syntax_isIdent(v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v___x_779_);
goto v___jp_763_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
else
{
lean_dec(v___x_776_);
goto v___jp_763_;
}
}
v___jp_758_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = l_Lean_Syntax_getArg(v_stx_754_, v___x_759_);
lean_dec(v_stx_754_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_787_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
lean_inc(v_stx_791_);
v___x_795_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_791_, v_a_792_, v_a_793_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_809_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_809_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_809_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
if (lean_obj_tag(v_a_796_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_798_);
v___x_800_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_791_);
v___x_801_ = l_Lean_MessageData_ofSyntax(v_stx_791_);
v___x_802_ = l_Lean_indentD(v___x_801_);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_791_, v___x_803_, v_a_792_, v_a_793_);
lean_dec(v_stx_791_);
return v___x_804_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; 
lean_dec(v_stx_791_);
v_val_805_ = lean_ctor_get(v_a_796_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_796_, 1);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_val_805_);
v___x_807_ = v___x_798_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_val_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_stx_791_);
v_a_810_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_795_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_795_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Attribute_Builtin_getIdent(v_stx_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_848_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_848_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_848_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_box(0);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_847_; 
v_val_836_ = lean_ctor_get(v_a_828_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_847_ == 0)
{
v___x_838_ = v_a_828_;
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v_a_828_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = l_Lean_Syntax_getId(v_val_836_);
lean_dec(v_val_836_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_842_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_827_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_827_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Attribute_Builtin_getIdent(v_stx_862_, v_a_863_, v_a_864_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_875_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_875_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_875_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_Syntax_getId(v_a_867_);
lean_dec(v_a_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_866_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_866_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_Attribute_Builtin_getId(v_stx_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
return v_res_888_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = l_Lean_Syntax_isNone(v_optPrioStx_892_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = l_Lean_Syntax_getArg(v_optPrioStx_892_, v___x_897_);
v___x_899_ = l_Lean_Syntax_isNatLit_x3f(v___x_898_);
lean_dec(v___x_898_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_900_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_892_);
v___x_901_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_892_);
v___x_902_ = l_Lean_indentD(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_900_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_892_, v___x_903_, v_a_893_, v_a_894_);
lean_dec(v_optPrioStx_892_);
return v___x_904_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v_optPrioStx_892_);
v_val_905_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_899_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_899_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 0);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_optPrioStx_892_);
v___x_913_ = lean_unsigned_to_nat(1000u);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
return v_res_919_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
lean_inc(v_stx_923_);
v___x_927_ = l_Lean_Syntax_getKind(v_stx_923_);
v___x_928_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_929_ = lean_name_eq(v___x_927_, v___x_928_);
lean_dec(v___x_927_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_923_);
v___x_931_ = l_Lean_MessageData_ofSyntax(v_stx_923_);
v___x_932_ = l_Lean_indentD(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_923_, v___x_933_, v_a_924_, v_a_925_);
lean_dec(v_stx_923_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = l_Lean_Syntax_getArg(v_stx_923_, v___x_935_);
lean_dec(v_stx_923_);
v___x_937_ = l_Lean_getAttrParamOptPrio(v___x_936_, v_a_924_, v_a_925_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Attribute_Builtin_getPrio(v_stx_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
return v_res_942_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_name_954_, uint8_t v_kind_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; 
v___x_956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_957_ = l_Lean_MessageData_ofName(v_name_954_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
switch(v_kind_955_)
{
case 0:
{
lean_object* v___x_969_; 
v___x_969_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_962_ = v___x_969_;
goto v___jp_961_;
}
case 1:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_962_ = v___x_970_;
goto v___jp_961_;
}
default: 
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_962_ = v___x_971_;
goto v___jp_961_;
}
}
v___jp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc_ref(v___y_962_);
v___x_963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_963_, 0, v___y_962_);
v___x_964_ = l_Lean_MessageData_ofFormat(v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwError___redArg(v_inst_952_, v_inst_953_, v___x_967_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_name_974_, lean_object* v_kind_975_){
_start:
{
uint8_t v_kind_boxed_976_; lean_object* v_res_977_; 
v_kind_boxed_976_ = lean_unbox(v_kind_975_);
v_res_977_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_972_, v_inst_973_, v_name_974_, v_kind_boxed_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_00_u03b1_981_, lean_object* v_name_982_, uint8_t v_kind_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_979_, v_inst_980_, v_name_982_, v_kind_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_00_u03b1_988_, lean_object* v_name_989_, lean_object* v_kind_990_){
_start:
{
uint8_t v_kind_boxed_991_; lean_object* v_res_992_; 
v_kind_boxed_991_ = lean_unbox(v_kind_990_);
v_res_992_ = l_Lean_throwAttrMustBeGlobal(v_m_985_, v_inst_986_, v_inst_987_, v_00_u03b1_988_, v_name_989_, v_kind_boxed_991_);
return v_res_992_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_attrName_1004_, lean_object* v_declName_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1006_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1007_ = l_Lean_MessageData_ofName(v_attrName_1004_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = 0;
v___x_1012_ = l_Lean_MessageData_ofConstName(v_declName_1005_, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_throwError___redArg(v_inst_1002_, v_inst_1003_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_00_u03b1_1020_, lean_object* v_attrName_1021_, lean_object* v_declName_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1018_, v_inst_1019_, v_attrName_1021_, v_declName_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_attrName_1032_, lean_object* v_declName_1033_, lean_object* v_asyncPrefix_x3f_1034_){
_start:
{
lean_object* v___y_1036_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1034_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_MessageData_nil;
v___y_1036_ = v___x_1049_;
goto v___jp_1035_;
}
else
{
lean_object* v_val_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_val_1050_ = lean_ctor_get(v_asyncPrefix_x3f_1034_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v_asyncPrefix_x3f_1034_, 1);
v___x_1051_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1052_ = l_Lean_MessageData_ofName(v_val_1050_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___y_1036_ = v___x_1055_;
goto v___jp_1035_;
}
v___jp_1035_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1037_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1038_ = l_Lean_MessageData_ofName(v_attrName_1032_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = 0;
v___x_1043_ = l_Lean_MessageData_ofConstName(v_declName_1033_, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1041_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___y_1036_);
v___x_1048_ = l_Lean_throwError___redArg(v_inst_1030_, v_inst_1031_, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_00_u03b1_1059_, lean_object* v_attrName_1060_, lean_object* v_declName_1061_, lean_object* v_asyncPrefix_x3f_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1057_, v_inst_1058_, v_attrName_1060_, v_declName_1061_, v_asyncPrefix_x3f_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_attrName_1078_, lean_object* v_declName_1079_, lean_object* v_givenType_1080_, lean_object* v_expectedType_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1082_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1083_ = l_Lean_MessageData_ofName(v_attrName_1078_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = 0;
v___x_1088_ = l_Lean_MessageData_ofConstName(v_declName_1079_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_indentExpr(v_givenType_1080_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v___x_1083_);
v___x_1097_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_indentExpr(v_expectedType_1081_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_throwError___redArg(v_inst_1076_, v_inst_1077_, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1102_, lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_00_u03b1_1105_, lean_object* v_attrName_1106_, lean_object* v_declName_1107_, lean_object* v_givenType_1108_, lean_object* v_expectedType_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1103_, v_inst_1104_, v_attrName_1106_, v_declName_1107_, v_givenType_1108_, v_expectedType_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1111_, uint8_t v_skipRealize_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = l_Lean_Environment_contains(v_env_1116_, v_constName_1111_, v_skipRealize_1112_);
v___x_1118_ = lean_box(v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1120_, lean_object* v_skipRealize_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_skipRealize_boxed_1124_; lean_object* v_res_1125_; 
v_skipRealize_boxed_1124_ = lean_unbox(v_skipRealize_1121_);
v_res_1125_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1120_, v_skipRealize_boxed_1124_, v___y_1122_);
lean_dec(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1126_, uint8_t v_skipRealize_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1126_, v_skipRealize_1127_, v___y_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1132_, lean_object* v_skipRealize_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_skipRealize_boxed_1137_; lean_object* v_res_1138_; 
v_skipRealize_boxed_1137_ = lean_unbox(v_skipRealize_1133_);
v_res_1138_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1132_, v_skipRealize_boxed_1137_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1139_, uint8_t v_isExporting_1140_, lean_object* v___x_1141_, lean_object* v_a_x3f_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v_nextMacroScope_1146_; lean_object* v_ngen_1147_; lean_object* v_auxDeclNGen_1148_; lean_object* v_traceState_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1163_; 
v___x_1144_ = lean_st_ref_take(v___y_1139_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
v_nextMacroScope_1146_ = lean_ctor_get(v___x_1144_, 1);
v_ngen_1147_ = lean_ctor_get(v___x_1144_, 2);
v_auxDeclNGen_1148_ = lean_ctor_get(v___x_1144_, 3);
v_traceState_1149_ = lean_ctor_get(v___x_1144_, 4);
v_messages_1150_ = lean_ctor_get(v___x_1144_, 6);
v_infoState_1151_ = lean_ctor_get(v___x_1144_, 7);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1144_, 8);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v___x_1144_, 5);
lean_dec(v_unused_1164_);
v___x_1154_ = v___x_1144_;
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_traceState_1149_);
lean_inc(v_auxDeclNGen_1148_);
lean_inc(v_ngen_1147_);
lean_inc(v_nextMacroScope_1146_);
lean_inc(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = l_Lean_Environment_setExporting(v_env_1145_, v_isExporting_1140_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 5, v___x_1141_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_nextMacroScope_1146_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_ngen_1147_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_auxDeclNGen_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_traceState_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_messages_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_snapshotTasks_1152_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = lean_st_ref_put(v___y_1139_, v___x_1158_);
v___x_1160_ = lean_box(0);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1165_, lean_object* v_isExporting_1166_, lean_object* v___x_1167_, lean_object* v_a_x3f_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_isExporting_boxed_1170_; lean_object* v_res_1171_; 
v_isExporting_boxed_1170_ = lean_unbox(v_isExporting_1166_);
v_res_1171_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1165_, v_isExporting_boxed_1170_, v___x_1167_, v_a_x3f_1168_);
lean_dec(v_a_x3f_1168_);
lean_dec(v___y_1165_);
return v_res_1171_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1177_, uint8_t v_isExporting_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_env_1183_; lean_object* v___x_1184_; uint8_t v_isModule_1185_; 
v___x_1182_ = lean_st_ref_get(v___y_1180_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc_ref(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1184_ = l_Lean_Environment_header(v_env_1183_);
v_isModule_1185_ = lean_ctor_get_uint8(v___x_1184_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1184_);
if (v_isModule_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_env_1183_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1186_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1186_;
}
else
{
uint8_t v_isExporting_1187_; 
v_isExporting_1187_ = lean_ctor_get_uint8(v_env_1183_, sizeof(void*)*8);
lean_dec_ref(v_env_1183_);
if (v_isExporting_1178_ == 0)
{
if (v_isExporting_1187_ == 0)
{
lean_object* v___x_1238_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1238_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1238_;
}
else
{
goto v___jp_1188_;
}
}
else
{
if (v_isExporting_1187_ == 0)
{
goto v___jp_1188_;
}
else
{
lean_object* v___x_1239_; 
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v___x_1239_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
return v___x_1239_;
}
}
v___jp_1188_:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; lean_object* v_nextMacroScope_1191_; lean_object* v_ngen_1192_; lean_object* v_auxDeclNGen_1193_; lean_object* v_traceState_1194_; lean_object* v_messages_1195_; lean_object* v_infoState_1196_; lean_object* v_snapshotTasks_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1236_; 
v___x_1189_ = lean_st_ref_take(v___y_1180_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
v_nextMacroScope_1191_ = lean_ctor_get(v___x_1189_, 1);
v_ngen_1192_ = lean_ctor_get(v___x_1189_, 2);
v_auxDeclNGen_1193_ = lean_ctor_get(v___x_1189_, 3);
v_traceState_1194_ = lean_ctor_get(v___x_1189_, 4);
v_messages_1195_ = lean_ctor_get(v___x_1189_, 6);
v_infoState_1196_ = lean_ctor_get(v___x_1189_, 7);
v_snapshotTasks_1197_ = lean_ctor_get(v___x_1189_, 8);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1189_, 5);
lean_dec(v_unused_1237_);
v___x_1199_ = v___x_1189_;
v_isShared_1200_ = v_isSharedCheck_1236_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_snapshotTasks_1197_);
lean_inc(v_infoState_1196_);
lean_inc(v_messages_1195_);
lean_inc(v_traceState_1194_);
lean_inc(v_auxDeclNGen_1193_);
lean_inc(v_ngen_1192_);
lean_inc(v_nextMacroScope_1191_);
lean_inc(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1236_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = l_Lean_Environment_setExporting(v_env_1190_, v_isExporting_1178_);
v___x_1202_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 5, v___x_1202_);
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_nextMacroScope_1191_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_ngen_1192_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_auxDeclNGen_1193_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_traceState_1194_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_messages_1195_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_infoState_1196_);
lean_ctor_set(v_reuseFailAlloc_1235_, 8, v_snapshotTasks_1197_);
v___x_1204_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v_r_1206_; 
v___x_1205_ = lean_st_ref_put(v___y_1180_, v___x_1204_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
v_r_1206_ = lean_apply_3(v_x_1177_, v___y_1179_, v___y_1180_, lean_box(0));
if (lean_obj_tag(v_r_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1223_; 
v_a_1207_ = lean_ctor_get(v_r_1206_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_r_1206_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1209_ = v_r_1206_;
v_isShared_1210_ = v_isSharedCheck_1223_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v_r_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1223_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
lean_inc(v_a_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set_tag(v___x_1209_, 1);
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v___x_1213_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1180_, v_isExporting_1187_, v___x_1202_, v___x_1212_);
lean_dec_ref(v___x_1212_);
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
lean_ctor_set(v___x_1215_, 0, v_a_1207_);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1207_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1224_ = lean_ctor_get(v_r_1206_, 0);
lean_inc(v_a_1224_);
lean_dec_ref_known(v_r_1206_, 1);
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1180_, v_isExporting_1187_, v___x_1202_, v___x_1225_);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1234_);
v___x_1228_ = v___x_1226_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1226_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 1);
lean_ctor_set(v___x_1228_, 0, v_a_1224_);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1224_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1240_, lean_object* v_isExporting_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_isExporting_boxed_1245_; lean_object* v_res_1246_; 
v_isExporting_boxed_1245_ = lean_unbox(v_isExporting_1241_);
v_res_1246_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1240_, v_isExporting_boxed_1245_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1247_, lean_object* v_x_1248_, uint8_t v_isExporting_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1248_, v_isExporting_1249_, v___y_1250_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_x_1255_, lean_object* v_isExporting_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v_isExporting_boxed_1260_; lean_object* v_res_1261_; 
v_isExporting_boxed_1260_ = lean_unbox(v_isExporting_1256_);
v_res_1261_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1254_, v_x_1255_, v_isExporting_boxed_1260_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
return v_res_1261_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1262_, lean_object* v_opt_1263_){
_start:
{
lean_object* v_name_1264_; lean_object* v_defValue_1265_; lean_object* v_map_1266_; lean_object* v___x_1267_; 
v_name_1264_ = lean_ctor_get(v_opt_1263_, 0);
v_defValue_1265_ = lean_ctor_get(v_opt_1263_, 1);
v_map_1266_ = lean_ctor_get(v_opts_1262_, 0);
v___x_1267_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1266_, v_name_1264_);
if (lean_obj_tag(v___x_1267_) == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_unbox(v_defValue_1265_);
return v___x_1268_;
}
else
{
lean_object* v_val_1269_; 
v_val_1269_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v___x_1267_, 1);
if (lean_obj_tag(v_val_1269_) == 1)
{
uint8_t v_v_1270_; 
v_v_1270_ = lean_ctor_get_uint8(v_val_1269_, 0);
lean_dec_ref_known(v_val_1269_, 0);
return v_v_1270_;
}
else
{
uint8_t v___x_1271_; 
lean_dec(v_val_1269_);
v___x_1271_ = lean_unbox(v_defValue_1265_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1272_, lean_object* v_opt_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1272_, v_opt_1273_);
lean_dec_ref(v_opt_1273_);
lean_dec_ref(v_opts_1272_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1283_, uint8_t v___y_1284_, lean_object* v_x_1285_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 1)
{
lean_object* v_pre_1286_; 
v_pre_1286_ = lean_ctor_get(v_x_1285_, 0);
switch(lean_obj_tag(v_pre_1286_))
{
case 1:
{
lean_object* v_pre_1287_; 
v_pre_1287_ = lean_ctor_get(v_pre_1286_, 0);
switch(lean_obj_tag(v_pre_1287_))
{
case 0:
{
lean_object* v_str_1288_; lean_object* v_str_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_str_1288_ = lean_ctor_get(v_x_1285_, 1);
v_str_1289_ = lean_ctor_get(v_pre_1286_, 1);
v___x_1290_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1291_ = lean_string_dec_eq(v_str_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1293_ = lean_string_dec_eq(v_str_1289_, v___x_1292_);
if (v___x_1293_ == 0)
{
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1295_ = lean_string_dec_eq(v_str_1288_, v___x_1294_);
if (v___x_1295_ == 0)
{
return v___x_1295_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1297_ = lean_string_dec_eq(v_str_1288_, v___x_1296_);
if (v___x_1297_ == 0)
{
return v___x_1297_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
case 1:
{
lean_object* v_pre_1298_; 
v_pre_1298_ = lean_ctor_get(v_pre_1287_, 0);
if (lean_obj_tag(v_pre_1298_) == 0)
{
lean_object* v_str_1299_; lean_object* v_str_1300_; lean_object* v_str_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_str_1299_ = lean_ctor_get(v_x_1285_, 1);
v_str_1300_ = lean_ctor_get(v_pre_1286_, 1);
v_str_1301_ = lean_ctor_get(v_pre_1287_, 1);
v___x_1302_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1303_ = lean_string_dec_eq(v_str_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
return v___x_1303_;
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1305_ = lean_string_dec_eq(v_str_1300_, v___x_1304_);
if (v___x_1305_ == 0)
{
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1307_ = lean_string_dec_eq(v_str_1299_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
}
}
else
{
return v___y_1284_;
}
}
default: 
{
return v___y_1284_;
}
}
}
case 0:
{
lean_object* v_str_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_str_1308_ = lean_ctor_get(v_x_1285_, 1);
v___x_1309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1310_ = lean_string_dec_eq(v_str_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
return v___x_1310_;
}
else
{
return v_suppressElabErrors_1283_;
}
}
default: 
{
return v___y_1284_;
}
}
}
else
{
return v___y_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1311_, lean_object* v___y_1312_, lean_object* v_x_1313_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1314_; uint8_t v___y_4991__boxed_1315_; uint8_t v_res_1316_; lean_object* v_r_1317_; 
v_suppressElabErrors_boxed_1314_ = lean_unbox(v_suppressElabErrors_1311_);
v___y_4991__boxed_1315_ = lean_unbox(v___y_1312_);
v_res_1316_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1314_, v___y_4991__boxed_1315_, v_x_1313_);
lean_dec(v_x_1313_);
v_r_1317_ = lean_box(v_res_1316_);
return v_r_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1318_, lean_object* v_msgData_1319_, uint8_t v_severity_1320_, uint8_t v_isSilent_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1398_; uint8_t v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; uint8_t v___x_1408_; uint8_t v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1415_; uint8_t v___y_1417_; uint8_t v___x_1431_; 
v___x_1408_ = 2;
v___x_1431_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1320_, v___x_1408_);
if (v___x_1431_ == 0)
{
v___y_1417_ = v___x_1431_;
goto v___jp_1416_;
}
else
{
uint8_t v___x_1432_; 
lean_inc_ref(v_msgData_1319_);
v___x_1432_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1319_);
v___y_1417_ = v___x_1432_;
goto v___jp_1416_;
}
v___jp_1325_:
{
lean_object* v___x_1335_; lean_object* v_currNamespace_1336_; lean_object* v_openDecls_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_traceState_1342_; lean_object* v_cache_1343_; lean_object* v_messages_1344_; lean_object* v_infoState_1345_; lean_object* v_snapshotTasks_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1360_; 
v___x_1335_ = lean_st_ref_take(v___y_1334_);
v_currNamespace_1336_ = lean_ctor_get(v___y_1333_, 5);
v_openDecls_1337_ = lean_ctor_get(v___y_1333_, 6);
v_env_1338_ = lean_ctor_get(v___x_1335_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1335_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1335_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1335_, 3);
v_traceState_1342_ = lean_ctor_get(v___x_1335_, 4);
v_cache_1343_ = lean_ctor_get(v___x_1335_, 5);
v_messages_1344_ = lean_ctor_get(v___x_1335_, 6);
v_infoState_1345_ = lean_ctor_get(v___x_1335_, 7);
v_snapshotTasks_1346_ = lean_ctor_get(v___x_1335_, 8);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1348_ = v___x_1335_;
v_isShared_1349_ = v_isSharedCheck_1360_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snapshotTasks_1346_);
lean_inc(v_infoState_1345_);
lean_inc(v_messages_1344_);
lean_inc(v_cache_1343_);
lean_inc(v_traceState_1342_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1335_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1360_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_inc(v_openDecls_1337_);
lean_inc(v_currNamespace_1336_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_currNamespace_1336_);
lean_ctor_set(v___x_1350_, 1, v_openDecls_1337_);
v___x_1351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc_ref(v___y_1330_);
v___x_1352_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1352_, 0, v___y_1330_);
lean_ctor_set(v___x_1352_, 1, v___y_1329_);
lean_ctor_set(v___x_1352_, 2, v___y_1327_);
lean_ctor_set(v___x_1352_, 3, v___y_1331_);
lean_ctor_set(v___x_1352_, 4, v___x_1351_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*5, v___y_1328_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*5 + 1, v___y_1326_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*5 + 2, v_isSilent_1321_);
v___x_1353_ = l_Lean_MessageLog_add(v___x_1352_, v_messages_1344_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 6, v___x_1353_);
v___x_1355_ = v___x_1348_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_env_1338_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_traceState_1342_);
lean_ctor_set(v_reuseFailAlloc_1359_, 5, v_cache_1343_);
lean_ctor_set(v_reuseFailAlloc_1359_, 6, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1359_, 7, v_infoState_1345_);
lean_ctor_set(v_reuseFailAlloc_1359_, 8, v_snapshotTasks_1346_);
v___x_1355_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = lean_st_ref_put(v___y_1334_, v___x_1355_);
v___x_1357_ = lean_box(0);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
}
v___jp_1361_:
{
lean_object* v_fileName_1369_; lean_object* v_fileMap_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1386_; 
v_fileName_1369_ = lean_ctor_get(v___y_1366_, 0);
v_fileMap_1370_ = lean_ctor_get(v___y_1366_, 1);
v___x_1371_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1319_);
v___x_1372_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1371_, v___y_1322_, v___y_1323_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1386_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1386_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_inc_ref_n(v_fileMap_1370_, 2);
v___x_1377_ = l_Lean_FileMap_toPosition(v_fileMap_1370_, v___y_1367_);
lean_dec(v___y_1367_);
v___x_1378_ = l_Lean_FileMap_toPosition(v_fileMap_1370_, v___y_1368_);
lean_dec(v___y_1368_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
v___x_1380_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1363_ == 0)
{
lean_del_object(v___x_1375_);
lean_dec_ref(v___y_1362_);
v___y_1326_ = v___y_1364_;
v___y_1327_ = v___x_1379_;
v___y_1328_ = v___y_1365_;
v___y_1329_ = v___x_1377_;
v___y_1330_ = v_fileName_1369_;
v___y_1331_ = v___x_1380_;
v___y_1332_ = v_a_1373_;
v___y_1333_ = v___y_1322_;
v___y_1334_ = v___y_1323_;
goto v___jp_1325_;
}
else
{
uint8_t v___x_1381_; 
lean_inc(v_a_1373_);
v___x_1381_ = l_Lean_MessageData_hasTag(v___y_1362_, v_a_1373_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1379_, 1);
lean_dec_ref(v___x_1377_);
lean_dec(v_a_1373_);
v___x_1382_ = lean_box(0);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1382_);
v___x_1384_ = v___x_1375_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_del_object(v___x_1375_);
v___y_1326_ = v___y_1364_;
v___y_1327_ = v___x_1379_;
v___y_1328_ = v___y_1365_;
v___y_1329_ = v___x_1377_;
v___y_1330_ = v_fileName_1369_;
v___y_1331_ = v___x_1380_;
v___y_1332_ = v_a_1373_;
v___y_1333_ = v___y_1322_;
v___y_1334_ = v___y_1323_;
goto v___jp_1325_;
}
}
}
}
v___jp_1387_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Syntax_getTailPos_x3f(v___y_1391_, v___y_1392_);
lean_dec(v___y_1391_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_inc(v___y_1394_);
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1390_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1394_;
v___y_1368_ = v___y_1394_;
goto v___jp_1361_;
}
else
{
lean_object* v_val_1396_; 
v_val_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_val_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1390_;
v___y_1364_ = v___y_1389_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1393_;
v___y_1367_ = v___y_1394_;
v___y_1368_ = v_val_1396_;
goto v___jp_1361_;
}
}
v___jp_1397_:
{
lean_object* v_ref_1404_; lean_object* v___x_1405_; 
v_ref_1404_ = l_Lean_replaceRef(v_ref_1318_, v___y_1402_);
v___x_1405_ = l_Lean_Syntax_getPos_x3f(v_ref_1404_, v___y_1400_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___y_1388_ = v___y_1398_;
v___y_1389_ = v___y_1403_;
v___y_1390_ = v___y_1399_;
v___y_1391_ = v_ref_1404_;
v___y_1392_ = v___y_1400_;
v___y_1393_ = v___y_1401_;
v___y_1394_ = v___x_1406_;
goto v___jp_1387_;
}
else
{
lean_object* v_val_1407_; 
v_val_1407_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1407_);
lean_dec_ref_known(v___x_1405_, 1);
v___y_1388_ = v___y_1398_;
v___y_1389_ = v___y_1403_;
v___y_1390_ = v___y_1399_;
v___y_1391_ = v_ref_1404_;
v___y_1392_ = v___y_1400_;
v___y_1393_ = v___y_1401_;
v___y_1394_ = v_val_1407_;
goto v___jp_1387_;
}
}
v___jp_1409_:
{
if (v___y_1415_ == 0)
{
v___y_1398_ = v___y_1412_;
v___y_1399_ = v___y_1410_;
v___y_1400_ = v___y_1414_;
v___y_1401_ = v___y_1411_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v_severity_1320_;
goto v___jp_1397_;
}
else
{
v___y_1398_ = v___y_1412_;
v___y_1399_ = v___y_1410_;
v___y_1400_ = v___y_1414_;
v___y_1401_ = v___y_1411_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v___x_1408_;
goto v___jp_1397_;
}
}
v___jp_1416_:
{
if (v___y_1417_ == 0)
{
lean_object* v_toCold_1418_; lean_object* v_options_1419_; lean_object* v_ref_1420_; uint8_t v_suppressElabErrors_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; 
v_toCold_1418_ = lean_ctor_get(v___y_1322_, 0);
v_options_1419_ = lean_ctor_get(v___y_1322_, 1);
v_ref_1420_ = lean_ctor_get(v___y_1322_, 4);
v_suppressElabErrors_1421_ = lean_ctor_get_uint8(v___y_1322_, sizeof(void*)*10 + 1);
v___x_1422_ = lean_box(v_suppressElabErrors_1421_);
v___x_1423_ = lean_box(v___y_1417_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1424_, 0, v___x_1422_);
lean_closure_set(v___f_1424_, 1, v___x_1423_);
v___x_1425_ = 1;
v___x_1426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1320_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1410_ = v_suppressElabErrors_1421_;
v___y_1411_ = v_toCold_1418_;
v___y_1412_ = v___f_1424_;
v___y_1413_ = v_ref_1420_;
v___y_1414_ = v___y_1417_;
v___y_1415_ = v___x_1426_;
goto v___jp_1409_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = l_Lean_warningAsError;
v___x_1428_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1419_, v___x_1427_);
v___y_1410_ = v_suppressElabErrors_1421_;
v___y_1411_ = v_toCold_1418_;
v___y_1412_ = v___f_1424_;
v___y_1413_ = v_ref_1420_;
v___y_1414_ = v___y_1417_;
v___y_1415_ = v___x_1428_;
goto v___jp_1409_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_msgData_1319_);
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1433_, lean_object* v_msgData_1434_, lean_object* v_severity_1435_, lean_object* v_isSilent_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v_severity_boxed_1440_; uint8_t v_isSilent_boxed_1441_; lean_object* v_res_1442_; 
v_severity_boxed_1440_ = lean_unbox(v_severity_1435_);
v_isSilent_boxed_1441_ = lean_unbox(v_isSilent_1436_);
v_res_1442_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1433_, v_msgData_1434_, v_severity_boxed_1440_, v_isSilent_boxed_1441_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v_ref_1433_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1443_, uint8_t v_severity_1444_, uint8_t v_isSilent_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_ref_1449_; lean_object* v___x_1450_; 
v_ref_1449_ = lean_ctor_get(v___y_1446_, 4);
v___x_1450_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1449_, v_msgData_1443_, v_severity_1444_, v_isSilent_1445_, v___y_1446_, v___y_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1451_, lean_object* v_severity_1452_, lean_object* v_isSilent_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_severity_boxed_1457_; uint8_t v_isSilent_boxed_1458_; lean_object* v_res_1459_; 
v_severity_boxed_1457_ = lean_unbox(v_severity_1452_);
v_isSilent_boxed_1458_ = lean_unbox(v_isSilent_1453_);
v_res_1459_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1451_, v_severity_boxed_1457_, v_isSilent_boxed_1458_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = 1;
v___x_1465_ = 0;
v___x_1466_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1460_, v___x_1464_, v___x_1465_, v___y_1461_, v___y_1462_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_options_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_options_1475_ = lean_ctor_get(v___y_1473_, 1);
v___x_1476_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1475_, v_opt_1472_);
v___x_1477_ = lean_box(v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1479_, v___y_1480_);
lean_dec_ref(v___y_1480_);
lean_dec_ref(v_opt_1479_);
return v_res_1482_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v_env_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1516_; 
v___x_1493_ = lean_st_ref_get(v___y_1491_);
v_env_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc_ref(v_env_1494_);
lean_dec(v___x_1493_);
v___x_1495_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1496_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1495_, v___y_1490_);
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1516_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1516_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
uint8_t v_isExporting_1506_; 
v_isExporting_1506_ = lean_ctor_get_uint8(v_env_1494_, sizeof(void*)*8);
lean_dec_ref(v_env_1494_);
if (v_isExporting_1506_ == 0)
{
lean_dec(v_a_1497_);
lean_dec(v_id_1489_);
goto v___jp_1501_;
}
else
{
uint8_t v___x_1507_; 
v___x_1507_ = l_Lean_isPrivateName(v_id_1489_);
if (v___x_1507_ == 0)
{
lean_dec(v_a_1497_);
lean_dec(v_id_1489_);
goto v___jp_1501_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_unbox(v_a_1497_);
lean_dec(v_a_1497_);
if (v___x_1508_ == 0)
{
lean_dec(v_id_1489_);
goto v___jp_1501_;
}
else
{
lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_del_object(v___x_1499_);
v___x_1509_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1510_ = 0;
v___x_1511_ = l_Lean_MessageData_ofConstName(v_id_1489_, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1509_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1514_, v___y_1490_, v___y_1491_);
return v___x_1515_;
}
}
}
v___jp_1501_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1502_ = lean_box(0);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1521_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1524_ = l_Lean_stringToMessageData(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1525_, uint8_t v_isModule_1526_, lean_object* v_attrName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
lean_inc(v_declName_1525_);
v___x_1531_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1525_, v___y_1528_, v___y_1529_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref_known(v___x_1531_, 1);
lean_inc(v_declName_1525_);
v___x_1532_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1525_, v_isModule_1526_, v___y_1529_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1553_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1553_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_unbox(v_a_1533_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_del_object(v___x_1535_);
v___x_1538_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1539_ = l_Lean_MessageData_ofName(v_attrName_1527_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_unbox(v_a_1533_);
lean_dec(v_a_1533_);
v___x_1544_ = l_Lean_MessageData_ofConstName(v_declName_1525_, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1542_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1547_, v___y_1528_, v___y_1529_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_a_1533_);
lean_dec(v_attrName_1527_);
lean_dec(v_declName_1525_);
v___x_1549_ = lean_box(0);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1549_);
v___x_1551_ = v___x_1535_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_dec(v_attrName_1527_);
lean_dec(v_declName_1525_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1554_, lean_object* v_isModule_1555_, lean_object* v_attrName_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v_isModule_boxed_1560_; lean_object* v_res_1561_; 
v_isModule_boxed_1560_ = lean_unbox(v_isModule_1555_);
v_res_1561_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1554_, v_isModule_boxed_1560_, v_attrName_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1562_, lean_object* v_declName_1563_, uint8_t v_attrKind_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v_env_1572_; lean_object* v___x_1573_; uint8_t v_isModule_1574_; 
v___x_1568_ = lean_st_ref_get(v_a_1566_);
v_env_1572_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1572_);
lean_dec(v___x_1568_);
v___x_1573_ = l_Lean_Environment_header(v_env_1572_);
lean_dec_ref(v_env_1572_);
v_isModule_1574_ = lean_ctor_get_uint8(v___x_1573_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1573_);
if (v_isModule_1574_ == 0)
{
lean_dec(v_declName_1563_);
lean_dec(v_attrName_1562_);
goto v___jp_1569_;
}
else
{
uint8_t v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = 1;
v___x_1576_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1564_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(v_isModule_1574_);
v___f_1578_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1578_, 0, v_declName_1563_);
lean_closure_set(v___f_1578_, 1, v___x_1577_);
lean_closure_set(v___f_1578_, 2, v_attrName_1562_);
v___x_1579_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1578_, v_isModule_1574_, v_a_1565_, v_a_1566_);
return v___x_1579_;
}
else
{
lean_dec(v_declName_1563_);
lean_dec(v_attrName_1562_);
goto v___jp_1569_;
}
}
v___jp_1569_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1580_, lean_object* v_declName_1581_, lean_object* v_attrKind_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v_attrKind_boxed_1586_; lean_object* v_res_1587_; 
v_attrKind_boxed_1586_ = lean_unbox(v_attrKind_1582_);
v_res_1587_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1580_, v_declName_1581_, v_attrKind_boxed_1586_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1588_, v___y_1589_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v_opt_1593_);
return v_res_1597_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1600_ = l_Lean_stringToMessageData(v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1601_, lean_object* v_declName_1602_, uint8_t v_attrKind_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v___x_1610_; uint8_t v_isModule_1611_; 
v___x_1607_ = lean_st_ref_get(v_a_1605_);
v___x_1608_ = lean_st_ref_get(v_a_1605_);
v_env_1609_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1609_);
lean_dec(v___x_1607_);
v___x_1610_ = l_Lean_Environment_header(v_env_1609_);
lean_dec_ref(v_env_1609_);
v_isModule_1611_ = lean_ctor_get_uint8(v___x_1610_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1610_);
if (v_isModule_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_dec(v___x_1608_);
v___x_1612_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1601_, v_declName_1602_, v_attrKind_1603_, v_a_1604_, v_a_1605_);
return v___x_1612_;
}
else
{
lean_object* v_env_1613_; uint8_t v___x_1614_; 
v_env_1613_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_ref(v_env_1613_);
lean_dec(v___x_1608_);
lean_inc(v_declName_1602_);
v___x_1614_ = l_Lean_isMarkedMeta(v_env_1613_, v_declName_1602_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1615_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1616_ = l_Lean_MessageData_ofName(v_attrName_1601_);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_MessageData_ofConstName(v_declName_1602_, v___x_1614_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1623_, v_a_1604_, v_a_1605_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1601_, v_declName_1602_, v_attrKind_1603_, v_a_1604_, v_a_1605_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1626_, lean_object* v_declName_1627_, lean_object* v_attrKind_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
uint8_t v_attrKind_boxed_1632_; lean_object* v_res_1633_; 
v_attrKind_boxed_1632_ = lean_unbox(v_attrKind_1628_);
v_res_1633_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1626_, v_declName_1627_, v_attrKind_boxed_1632_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1642_, v___y_1643_);
lean_dec_ref(v___y_1643_);
lean_dec_ref(v_x_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1646_, lean_object* v_x_1647_){
_start:
{
lean_inc(v_s_1646_);
return v_s_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1648_, v_x_1649_);
lean_dec(v_x_1649_);
lean_dec(v_s_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1658_, v_x_1659_);
lean_dec(v_x_1659_);
lean_dec_ref(v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_box(0);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1663_);
lean_dec(v_x_1663_);
return v_res_1664_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1670_; lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___f_1670_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1671_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1672_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1673_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1676_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
lean_ctor_set(v___x_1676_, 2, v___f_1673_);
lean_ctor_set(v___x_1676_, 3, v___f_1672_);
lean_ctor_set(v___x_1676_, 4, v___f_1671_);
lean_ctor_set(v___x_1676_, 5, v___f_1670_);
return v___x_1676_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1678_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_registerTagAttribute___lam__0(v_x_1685_);
lean_dec(v_x_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
if (lean_obj_tag(v_x_1689_) == 0)
{
return v_x_1688_;
}
else
{
lean_object* v_head_1690_; lean_object* v_tail_1691_; uint8_t v___x_1692_; 
v_head_1690_ = lean_ctor_get(v_x_1689_, 0);
lean_inc(v_head_1690_);
v_tail_1691_ = lean_ctor_get(v_x_1689_, 1);
lean_inc(v_tail_1691_);
lean_dec_ref_known(v_x_1689_, 2);
v___x_1692_ = l_Lean_NameSet_contains(v_newState_1687_, v_head_1690_);
if (v___x_1692_ == 0)
{
lean_dec(v_head_1690_);
v_x_1689_ = v_tail_1691_;
goto _start;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_NameSet_insert(v_x_1688_, v_head_1690_);
v_x_1688_ = v___x_1694_;
v_x_1689_ = v_tail_1691_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1696_, v_x_1697_, v_x_1698_);
lean_dec(v_newState_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1700_, lean_object* v_newState_1701_, lean_object* v_newConsts_1702_, lean_object* v_s_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1701_, v_s_1703_, v_newConsts_1702_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1705_, lean_object* v_newState_1706_, lean_object* v_newConsts_1707_, lean_object* v_s_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_registerTagAttribute___lam__1(v_x_1705_, v_newState_1706_, v_newConsts_1707_, v_s_1708_);
lean_dec(v_newState_1706_);
lean_dec(v_x_1705_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___y_1725_; 
v___x_1723_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1722_) == 0)
{
lean_object* v_size_1729_; 
v_size_1729_ = lean_ctor_get(v_s_1722_, 0);
lean_inc(v_size_1729_);
lean_dec_ref_known(v_s_1722_, 5);
v___y_1725_ = v_size_1729_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_unsigned_to_nat(0u);
v___y_1725_ = v___x_1730_;
goto v___jp_1724_;
}
v___jp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Nat_reprFast(v___y_1725_);
v___x_1727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___x_1728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1723_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
return v___x_1728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1731_, lean_object* v_pivot_1732_, lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_k_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_lt(v_k_1735_, v_hi_1731_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_k_1735_);
v___x_1737_ = lean_array_fswap(v_as_1733_, v_i_1734_, v_hi_1731_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_i_1734_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_fget_borrowed(v_as_1733_, v_k_1735_);
v___x_1740_ = l_Lean_Name_quickLt(v___x_1739_, v_pivot_1732_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_nat_add(v_k_1735_, v___x_1741_);
lean_dec(v_k_1735_);
v_k_1735_ = v___x_1742_;
goto _start;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1744_ = lean_array_fswap(v_as_1733_, v_i_1734_, v_k_1735_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_add(v_i_1734_, v___x_1745_);
lean_dec(v_i_1734_);
v___x_1747_ = lean_nat_add(v_k_1735_, v___x_1745_);
lean_dec(v_k_1735_);
v_as_1733_ = v___x_1744_;
v_i_1734_ = v___x_1746_;
v_k_1735_ = v___x_1747_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1749_, lean_object* v_pivot_1750_, lean_object* v_as_1751_, lean_object* v_i_1752_, lean_object* v_k_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1749_, v_pivot_1750_, v_as_1751_, v_i_1752_, v_k_1753_);
lean_dec(v_pivot_1750_);
lean_dec(v_hi_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1755_, lean_object* v_as_1756_, lean_object* v_lo_1757_, lean_object* v_hi_1758_){
_start:
{
lean_object* v___y_1760_; uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_lt(v_lo_1757_, v_hi_1758_);
if (v___x_1770_ == 0)
{
lean_dec(v_lo_1757_);
return v_as_1756_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_mid_1773_; lean_object* v___y_1775_; lean_object* v___y_1781_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1771_ = lean_nat_add(v_lo_1757_, v_hi_1758_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v_mid_1773_ = lean_nat_shiftr(v___x_1771_, v___x_1772_);
lean_dec(v___x_1771_);
v___x_1786_ = lean_array_fget_borrowed(v_as_1756_, v_mid_1773_);
v___x_1787_ = lean_array_fget_borrowed(v_as_1756_, v_lo_1757_);
v___x_1788_ = l_Lean_Name_quickLt(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1781_ = v_as_1756_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_array_fswap(v_as_1756_, v_lo_1757_, v_mid_1773_);
v___y_1781_ = v___x_1789_;
goto v___jp_1780_;
}
v___jp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = lean_array_fget_borrowed(v___y_1775_, v_mid_1773_);
v___x_1777_ = lean_array_fget_borrowed(v___y_1775_, v_hi_1758_);
v___x_1778_ = l_Lean_Name_quickLt(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec(v_mid_1773_);
v___y_1760_ = v___y_1775_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_array_fswap(v___y_1775_, v_mid_1773_, v_hi_1758_);
lean_dec(v_mid_1773_);
v___y_1760_ = v___x_1779_;
goto v___jp_1759_;
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_array_fget_borrowed(v___y_1781_, v_hi_1758_);
v___x_1783_ = lean_array_fget_borrowed(v___y_1781_, v_lo_1757_);
v___x_1784_ = l_Lean_Name_quickLt(v___x_1782_, v___x_1783_);
if (v___x_1784_ == 0)
{
v___y_1775_ = v___y_1781_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_array_fswap(v___y_1781_, v_lo_1757_, v_hi_1758_);
v___y_1775_ = v___x_1785_;
goto v___jp_1774_;
}
}
}
v___jp_1759_:
{
lean_object* v_pivot_1761_; lean_object* v___x_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; uint8_t v___x_1765_; 
v_pivot_1761_ = lean_array_fget(v___y_1760_, v_hi_1758_);
lean_inc_n(v_lo_1757_, 2);
v___x_1762_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1758_, v_pivot_1761_, v___y_1760_, v_lo_1757_, v_lo_1757_);
lean_dec(v_pivot_1761_);
v_fst_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_fst_1763_);
v_snd_1764_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_snd_1764_);
lean_dec_ref(v___x_1762_);
v___x_1765_ = lean_nat_dec_le(v_hi_1758_, v_fst_1763_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1755_, v_snd_1764_, v_lo_1757_, v_fst_1763_);
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_nat_add(v_fst_1763_, v___x_1767_);
lean_dec(v_fst_1763_);
v_as_1756_ = v___x_1766_;
v_lo_1757_ = v___x_1768_;
goto _start;
}
else
{
lean_dec(v_fst_1763_);
lean_dec(v_lo_1757_);
return v_snd_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1790_, lean_object* v_as_1791_, lean_object* v_lo_1792_, lean_object* v_hi_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1790_, v_as_1791_, v_lo_1792_, v_hi_1793_);
lean_dec(v_hi_1793_);
lean_dec(v_n_1790_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1795_, lean_object* v_as_1796_, size_t v_i_1797_, size_t v_stop_1798_, lean_object* v_b_1799_){
_start:
{
lean_object* v___y_1801_; uint8_t v___x_1805_; 
v___x_1805_ = lean_usize_dec_eq(v_i_1797_, v_stop_1798_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = lean_array_uget_borrowed(v_as_1796_, v_i_1797_);
v___x_1807_ = 1;
lean_inc_ref(v_env_1795_);
v___x_1808_ = l_Lean_Environment_setExporting(v_env_1795_, v___x_1807_);
lean_inc(v___x_1806_);
v___x_1809_ = l_Lean_Environment_contains(v___x_1808_, v___x_1806_, v___x_1805_);
if (v___x_1809_ == 0)
{
v___y_1801_ = v_b_1799_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1810_; 
lean_inc(v___x_1806_);
v___x_1810_ = lean_array_push(v_b_1799_, v___x_1806_);
v___y_1801_ = v___x_1810_;
goto v___jp_1800_;
}
}
else
{
lean_dec_ref(v_env_1795_);
return v_b_1799_;
}
v___jp_1800_:
{
size_t v___x_1802_; size_t v___x_1803_; 
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_i_1797_, v___x_1802_);
v_i_1797_ = v___x_1803_;
v_b_1799_ = v___y_1801_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1811_, lean_object* v_as_1812_, lean_object* v_i_1813_, lean_object* v_stop_1814_, lean_object* v_b_1815_){
_start:
{
size_t v_i_boxed_1816_; size_t v_stop_boxed_1817_; lean_object* v_res_1818_; 
v_i_boxed_1816_ = lean_unbox_usize(v_i_1813_);
lean_dec(v_i_1813_);
v_stop_boxed_1817_ = lean_unbox_usize(v_stop_1814_);
lean_dec(v_stop_1814_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1811_, v_as_1812_, v_i_boxed_1816_, v_stop_boxed_1817_, v_b_1815_);
lean_dec_ref(v_as_1812_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1819_, lean_object* v_x_1820_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_k_1821_; lean_object* v_l_1822_; lean_object* v_r_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_k_1821_ = lean_ctor_get(v_x_1820_, 1);
lean_inc(v_k_1821_);
v_l_1822_ = lean_ctor_get(v_x_1820_, 3);
lean_inc(v_l_1822_);
v_r_1823_ = lean_ctor_get(v_x_1820_, 4);
lean_inc(v_r_1823_);
lean_dec_ref_known(v_x_1820_, 5);
v___x_1824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1819_, v_l_1822_);
v___x_1825_ = lean_array_push(v___x_1824_, v_k_1821_);
v_init_1819_ = v___x_1825_;
v_x_1820_ = v_r_1823_;
goto _start;
}
else
{
return v_init_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1827_, lean_object* v_es_1828_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___y_1832_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1849_; lean_object* v___y_1850_; uint8_t v___x_1852_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1846_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1830_, v_es_1828_);
v___x_1847_ = lean_array_get_size(v___x_1846_);
v___x_1852_ = lean_nat_dec_eq(v___x_1847_, v___x_1829_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___y_1856_; uint8_t v___x_1858_; 
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_sub(v___x_1847_, v___x_1853_);
v___x_1858_ = lean_nat_dec_le(v___x_1829_, v___x_1854_);
if (v___x_1858_ == 0)
{
lean_inc(v___x_1854_);
v___y_1856_ = v___x_1854_;
goto v___jp_1855_;
}
else
{
v___y_1856_ = v___x_1829_;
goto v___jp_1855_;
}
v___jp_1855_:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_le(v___y_1856_, v___x_1854_);
if (v___x_1857_ == 0)
{
lean_dec(v___x_1854_);
lean_inc(v___y_1856_);
v___y_1849_ = v___y_1856_;
v___y_1850_ = v___y_1856_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___y_1856_;
v___y_1850_ = v___x_1854_;
goto v___jp_1848_;
}
}
}
else
{
v___y_1832_ = v___x_1846_;
goto v___jp_1831_;
}
v___jp_1831_:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v___y_1832_);
v___x_1834_ = lean_nat_dec_lt(v___x_1829_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v_env_1827_);
v___x_1835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1830_);
lean_ctor_set(v___x_1835_, 1, v___x_1830_);
lean_ctor_set(v___x_1835_, 2, v___y_1832_);
return v___x_1835_;
}
else
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_nat_dec_le(v___x_1833_, v___x_1833_);
if (v___x_1836_ == 0)
{
if (v___x_1834_ == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref(v_env_1827_);
v___x_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1830_);
lean_ctor_set(v___x_1837_, 1, v___x_1830_);
lean_ctor_set(v___x_1837_, 2, v___y_1832_);
return v___x_1837_;
}
else
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = ((size_t)0ULL);
v___x_1839_ = lean_usize_of_nat(v___x_1833_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1827_, v___y_1832_, v___x_1838_, v___x_1839_, v___x_1830_);
lean_inc_ref(v___x_1840_);
v___x_1841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
lean_ctor_set(v___x_1841_, 2, v___y_1832_);
return v___x_1841_;
}
}
else
{
size_t v___x_1842_; size_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = ((size_t)0ULL);
v___x_1843_ = lean_usize_of_nat(v___x_1833_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1827_, v___y_1832_, v___x_1842_, v___x_1843_, v___x_1830_);
lean_inc_ref(v___x_1844_);
v___x_1845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_ctor_set(v___x_1845_, 2, v___y_1832_);
return v___x_1845_;
}
}
}
v___jp_1848_:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1847_, v___x_1846_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
v___y_1832_ = v___x_1851_;
goto v___jp_1831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1859_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_registerTagAttribute___lam__4(v___x_1864_, v_x_1865_, v_x_1866_);
lean_dec_ref(v_x_1866_);
lean_dec_ref(v_x_1865_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_registerTagAttribute___lam__5(v___x_1872_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1875_, lean_object* v_decl_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1880_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1881_ = l_Lean_MessageData_ofName(v_name_1875_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1884_, v___y_1877_, v___y_1878_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1886_, lean_object* v_decl_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_registerTagAttribute___lam__6(v_name_1886_, v_decl_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v_decl_1887_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1892_, lean_object* v_declName_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1897_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1898_ = l_Lean_MessageData_ofName(v_attrName_1892_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = l_Lean_MessageData_ofConstName(v_declName_1893_, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1906_, v___y_1894_, v___y_1895_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1908_, lean_object* v_declName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1908_, v_declName_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1914_, lean_object* v_declName_1915_, lean_object* v_asyncPrefix_x3f_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___y_1921_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1916_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_MessageData_nil;
v___y_1921_ = v___x_1934_;
goto v___jp_1920_;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_val_1935_ = lean_ctor_get(v_asyncPrefix_x3f_1916_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v_asyncPrefix_x3f_1916_, 1);
v___x_1936_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1937_ = l_Lean_MessageData_ofName(v_val_1935_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___y_1921_ = v___x_1940_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1922_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1923_ = l_Lean_MessageData_ofName(v_attrName_1914_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = 0;
v___x_1928_ = l_Lean_MessageData_ofConstName(v_declName_1915_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1926_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___y_1921_);
v___x_1933_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1932_, v___y_1917_, v___y_1918_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1941_, lean_object* v_declName_1942_, lean_object* v_asyncPrefix_x3f_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1941_, v_declName_1942_, v_asyncPrefix_x3f_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1948_, uint8_t v_kind_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___y_1959_; 
v___x_1953_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1954_ = l_Lean_MessageData_ofName(v_name_1948_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
switch(v_kind_1949_)
{
case 0:
{
lean_object* v___x_1966_; 
v___x_1966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1959_ = v___x_1966_;
goto v___jp_1958_;
}
case 1:
{
lean_object* v___x_1967_; 
v___x_1967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1959_ = v___x_1967_;
goto v___jp_1958_;
}
default: 
{
lean_object* v___x_1968_; 
v___x_1968_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1959_ = v___x_1968_;
goto v___jp_1958_;
}
}
v___jp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref(v___y_1959_);
v___x_1960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___y_1959_);
v___x_1961_ = l_Lean_MessageData_ofFormat(v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1957_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1964_, v___y_1950_, v___y_1951_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1969_, lean_object* v_kind_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v_kind_boxed_1974_; lean_object* v_res_1975_; 
v_kind_boxed_1974_ = lean_unbox(v_kind_1970_);
v_res_1975_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1969_, v_kind_boxed_1974_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1976_, lean_object* v_a_1977_, lean_object* v_name_1978_, lean_object* v_decl_1979_, lean_object* v_stx_1980_, uint8_t v_kind_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1980_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_2036_) == 0)
{
uint8_t v___x_2037_; uint8_t v___x_2038_; 
lean_dec_ref_known(v___x_2036_, 1);
v___x_2037_ = 0;
v___x_2038_ = l_Lean_instBEqAttributeKind_beq(v_kind_1981_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec(v_decl_1979_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_validate_1976_);
v___x_2039_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1978_, v_kind_1981_, v___y_1982_, v___y_1983_);
return v___x_2039_;
}
else
{
v___y_2030_ = v___y_1982_;
v___y_2031_ = v___y_1983_;
goto v___jp_2029_;
}
}
else
{
lean_dec(v_decl_1979_);
lean_dec(v_name_1978_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_validate_1976_);
return v___x_2036_;
}
v___jp_1985_:
{
lean_object* v___x_1988_; 
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v_decl_1979_);
v___x_1988_ = lean_apply_4(v_validate_1976_, v_decl_1979_, v___y_1986_, v___y_1987_, lean_box(0));
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2018_; 
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_1988_, 0);
lean_dec(v_unused_2019_);
v___x_1990_ = v___x_1988_;
v_isShared_1991_ = v_isSharedCheck_2018_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v___x_1988_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2018_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v_toEnvExtension_1993_; lean_object* v_env_1994_; lean_object* v_nextMacroScope_1995_; lean_object* v_ngen_1996_; lean_object* v_auxDeclNGen_1997_; lean_object* v_traceState_1998_; lean_object* v_messages_1999_; lean_object* v_infoState_2000_; lean_object* v_snapshotTasks_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2016_; 
v___x_1992_ = lean_st_ref_take(v___y_1987_);
v_toEnvExtension_1993_ = lean_ctor_get(v_a_1977_, 0);
v_env_1994_ = lean_ctor_get(v___x_1992_, 0);
v_nextMacroScope_1995_ = lean_ctor_get(v___x_1992_, 1);
v_ngen_1996_ = lean_ctor_get(v___x_1992_, 2);
v_auxDeclNGen_1997_ = lean_ctor_get(v___x_1992_, 3);
v_traceState_1998_ = lean_ctor_get(v___x_1992_, 4);
v_messages_1999_ = lean_ctor_get(v___x_1992_, 6);
v_infoState_2000_ = lean_ctor_get(v___x_1992_, 7);
v_snapshotTasks_2001_ = lean_ctor_get(v___x_1992_, 8);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_1992_, 5);
lean_dec(v_unused_2017_);
v___x_2003_ = v___x_1992_;
v_isShared_2004_ = v_isSharedCheck_2016_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_snapshotTasks_2001_);
lean_inc(v_infoState_2000_);
lean_inc(v_messages_1999_);
lean_inc(v_traceState_1998_);
lean_inc(v_auxDeclNGen_1997_);
lean_inc(v_ngen_1996_);
lean_inc(v_nextMacroScope_1995_);
lean_inc(v_env_1994_);
lean_dec(v___x_1992_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2016_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_asyncMode_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v_asyncMode_2005_ = lean_ctor_get(v_toEnvExtension_1993_, 2);
lean_inc(v_asyncMode_2005_);
lean_inc(v_decl_1979_);
v___x_2006_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1977_, v_env_1994_, v_decl_1979_, v_asyncMode_2005_, v_decl_1979_);
lean_dec(v_asyncMode_2005_);
v___x_2007_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 5, v___x_2007_);
lean_ctor_set(v___x_2003_, 0, v___x_2006_);
v___x_2009_ = v___x_2003_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_nextMacroScope_1995_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_ngen_1996_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_auxDeclNGen_1997_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_traceState_1998_);
lean_ctor_set(v_reuseFailAlloc_2015_, 5, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 6, v_messages_1999_);
lean_ctor_set(v_reuseFailAlloc_2015_, 7, v_infoState_2000_);
lean_ctor_set(v_reuseFailAlloc_2015_, 8, v_snapshotTasks_2001_);
v___x_2009_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_put(v___y_1987_, v___x_2009_);
v___x_2011_ = lean_box(0);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_2011_);
v___x_2013_ = v___x_1990_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_dec(v_decl_1979_);
lean_dec_ref(v_a_1977_);
return v___x_1988_;
}
}
v___jp_2020_:
{
lean_object* v_toEnvExtension_2024_; lean_object* v_asyncMode_2025_; uint8_t v___x_2026_; 
v_toEnvExtension_2024_ = lean_ctor_get(v_a_1977_, 0);
v_asyncMode_2025_ = lean_ctor_get(v_toEnvExtension_2024_, 2);
lean_inc(v_decl_1979_);
lean_inc_ref(v___y_2021_);
v___x_2026_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2021_, v_decl_1979_, v_asyncMode_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_validate_1976_);
v___x_2027_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2021_);
v___x_2028_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1978_, v_decl_1979_, v___x_2027_, v___y_2022_, v___y_2023_);
return v___x_2028_;
}
else
{
lean_dec_ref(v___y_2021_);
lean_dec(v_name_1978_);
v___y_1986_ = v___y_2022_;
v___y_1987_ = v___y_2023_;
goto v___jp_1985_;
}
}
v___jp_2029_:
{
lean_object* v___x_2032_; lean_object* v_env_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_st_ref_get(v___y_2031_);
v_env_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc_ref(v_env_2033_);
lean_dec(v___x_2032_);
v___x_2034_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2033_, v_decl_1979_);
if (lean_obj_tag(v___x_2034_) == 0)
{
v___y_2021_ = v_env_2033_;
v___y_2022_ = v___y_2030_;
v___y_2023_ = v___y_2031_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2035_; 
lean_dec_ref_known(v___x_2034_, 1);
lean_dec_ref(v_env_2033_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_validate_1976_);
v___x_2035_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1978_, v_decl_1979_, v___y_2030_, v___y_2031_);
return v___x_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2040_, lean_object* v_a_2041_, lean_object* v_name_2042_, lean_object* v_decl_2043_, lean_object* v_stx_2044_, lean_object* v_kind_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v_kind_boxed_2049_; lean_object* v_res_2050_; 
v_kind_boxed_2049_ = lean_unbox(v_kind_2045_);
v_res_2050_ = l_Lean_registerTagAttribute___lam__7(v_validate_2040_, v_a_2041_, v_name_2042_, v_decl_2043_, v_stx_2044_, v_kind_boxed_2049_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2050_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___f_2057_; 
v___x_2056_ = l_Lean_NameSet_empty;
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2057_, 0, v___x_2056_);
return v___f_2057_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___f_2059_; 
v___x_2058_ = l_Lean_NameSet_empty;
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2059_, 0, v___x_2058_);
return v___f_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2062_, lean_object* v_descr_2063_, lean_object* v_validate_2064_, lean_object* v_ref_2065_, uint8_t v_applicationTime_2066_, lean_object* v_asyncMode_2067_){
_start:
{
lean_object* v___f_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___f_2069_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2070_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2071_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2072_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2073_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2074_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2075_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2065_);
v___x_2076_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2076_, 0, v_ref_2065_);
lean_ctor_set(v___x_2076_, 1, v___f_2074_);
lean_ctor_set(v___x_2076_, 2, v___f_2073_);
lean_ctor_set(v___x_2076_, 3, v___f_2072_);
lean_ctor_set(v___x_2076_, 4, v___f_2071_);
lean_ctor_set(v___x_2076_, 5, v___f_2070_);
lean_ctor_set(v___x_2076_, 6, v_asyncMode_2067_);
lean_ctor_set(v___x_2076_, 7, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v___f_2069_);
v___x_2078_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2077_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc_n(v_a_2079_, 2);
lean_dec_ref_known(v___x_2078_, 1);
lean_inc_n(v_name_2062_, 2);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2080_, 0, v_name_2062_);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2081_, 0, v_validate_2064_);
lean_closure_set(v___f_2081_, 1, v_a_2079_);
lean_closure_set(v___f_2081_, 2, v_name_2062_);
v___x_2082_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2082_, 0, v_ref_2065_);
lean_ctor_set(v___x_2082_, 1, v_name_2062_);
lean_ctor_set(v___x_2082_, 2, v_descr_2063_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*3, v_applicationTime_2066_);
v___x_2083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___f_2081_);
lean_ctor_set(v___x_2083_, 2, v___f_2080_);
lean_inc_ref(v___x_2083_);
v___x_2084_ = l_Lean_registerBuiltinAttribute(v___x_2083_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2092_; 
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2093_);
v___x_2086_ = v___x_2084_;
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v___x_2084_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2092_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2083_);
lean_ctor_set(v___x_2088_, 1, v_a_2079_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2088_);
v___x_2090_ = v___x_2086_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref_known(v___x_2083_, 3);
lean_dec(v_a_2079_);
v_a_2094_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2084_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2084_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_ref_2065_);
lean_dec_ref(v_validate_2064_);
lean_dec_ref(v_descr_2063_);
lean_dec(v_name_2062_);
v_a_2102_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2078_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2078_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2110_, lean_object* v_descr_2111_, lean_object* v_validate_2112_, lean_object* v_ref_2113_, lean_object* v_applicationTime_2114_, lean_object* v_asyncMode_2115_, lean_object* v_a_2116_){
_start:
{
uint8_t v_applicationTime_boxed_2117_; lean_object* v_res_2118_; 
v_applicationTime_boxed_2117_ = lean_unbox(v_applicationTime_2114_);
v_res_2118_ = l_Lean_registerTagAttribute(v_name_2110_, v_descr_2111_, v_validate_2112_, v_ref_2113_, v_applicationTime_boxed_2117_, v_asyncMode_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2119_, lean_object* v_t_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2119_, v_t_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2122_, lean_object* v_as_2123_, lean_object* v_lo_2124_, lean_object* v_hi_2125_, lean_object* v_w_2126_, lean_object* v_hlo_2127_, lean_object* v_hhi_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2122_, v_as_2123_, v_lo_2124_, v_hi_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2130_, lean_object* v_as_2131_, lean_object* v_lo_2132_, lean_object* v_hi_2133_, lean_object* v_w_2134_, lean_object* v_hlo_2135_, lean_object* v_hhi_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2130_, v_as_2131_, v_lo_2132_, v_hi_2133_, v_w_2134_, v_hlo_2135_, v_hhi_2136_);
lean_dec(v_hi_2133_);
lean_dec(v_n_2130_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2138_, lean_object* v_attrName_2139_, lean_object* v_declName_2140_, lean_object* v_asyncPrefix_x3f_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2139_, v_declName_2140_, v_asyncPrefix_x3f_2141_, v___y_2142_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2146_, lean_object* v_attrName_2147_, lean_object* v_declName_2148_, lean_object* v_asyncPrefix_x3f_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2146_, v_attrName_2147_, v_declName_2148_, v_asyncPrefix_x3f_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2154_, lean_object* v_attrName_2155_, lean_object* v_declName_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2155_, v_declName_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_attrName_2162_, lean_object* v_declName_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2161_, v_attrName_2162_, v_declName_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2168_, lean_object* v_name_2169_, uint8_t v_kind_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2169_, v_kind_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, lean_object* v_kind_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v_kind_boxed_2181_; lean_object* v_res_2182_; 
v_kind_boxed_2181_ = lean_unbox(v_kind_2177_);
v_res_2182_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2175_, v_name_2176_, v_kind_boxed_2181_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2183_, lean_object* v_lo_2184_, lean_object* v_hi_2185_, lean_object* v_hhi_2186_, lean_object* v_pivot_2187_, lean_object* v_as_2188_, lean_object* v_i_2189_, lean_object* v_k_2190_, lean_object* v_ilo_2191_, lean_object* v_ik_2192_, lean_object* v_w_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2185_, v_pivot_2187_, v_as_2188_, v_i_2189_, v_k_2190_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2195_, lean_object* v_lo_2196_, lean_object* v_hi_2197_, lean_object* v_hhi_2198_, lean_object* v_pivot_2199_, lean_object* v_as_2200_, lean_object* v_i_2201_, lean_object* v_k_2202_, lean_object* v_ilo_2203_, lean_object* v_ik_2204_, lean_object* v_w_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2195_, v_lo_2196_, v_hi_2197_, v_hhi_2198_, v_pivot_2199_, v_as_2200_, v_i_2201_, v_k_2202_, v_ilo_2203_, v_ik_2204_, v_w_2205_);
lean_dec(v_pivot_2199_);
lean_dec(v_hi_2197_);
lean_dec(v_lo_2196_);
lean_dec(v_n_2195_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2207_, lean_object* v_decl_2208_, lean_object* v_env_2209_){
_start:
{
lean_object* v_ext_2210_; lean_object* v_toEnvExtension_2211_; lean_object* v_asyncMode_2212_; lean_object* v___x_2213_; 
v_ext_2210_ = lean_ctor_get(v_attr_2207_, 1);
lean_inc_ref(v_ext_2210_);
lean_dec_ref(v_attr_2207_);
v_toEnvExtension_2211_ = lean_ctor_get(v_ext_2210_, 0);
v_asyncMode_2212_ = lean_ctor_get(v_toEnvExtension_2211_, 2);
lean_inc(v_asyncMode_2212_);
lean_inc(v_decl_2208_);
v___x_2213_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2210_, v_env_2209_, v_decl_2208_, v_asyncMode_2212_, v_decl_2208_);
lean_dec(v_asyncMode_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2214_, lean_object* v___f_2215_, lean_object* v_____r_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_apply_1(v_modifyEnv_2214_, v___f_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2218_, lean_object* v_env_2219_, lean_object* v_decl_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_toBind_2223_, lean_object* v___f_2224_, lean_object* v_modifyEnv_2225_, lean_object* v___f_2226_, lean_object* v_____r_2227_){
_start:
{
lean_object* v_ext_2228_; lean_object* v_toEnvExtension_2229_; lean_object* v_attr_2230_; lean_object* v_asyncMode_2231_; uint8_t v___x_2232_; 
v_ext_2228_ = lean_ctor_get(v_attr_2218_, 1);
v_toEnvExtension_2229_ = lean_ctor_get(v_ext_2228_, 0);
lean_inc_ref(v_toEnvExtension_2229_);
v_attr_2230_ = lean_ctor_get(v_attr_2218_, 0);
lean_inc_ref(v_attr_2230_);
lean_dec_ref(v_attr_2218_);
v_asyncMode_2231_ = lean_ctor_get(v_toEnvExtension_2229_, 2);
lean_inc(v_asyncMode_2231_);
lean_dec_ref(v_toEnvExtension_2229_);
lean_inc(v_decl_2220_);
lean_inc_ref(v_env_2219_);
v___x_2232_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2219_, v_decl_2220_, v_asyncMode_2231_);
lean_dec(v_asyncMode_2231_);
if (v___x_2232_ == 0)
{
lean_object* v_toAttributeImplCore_2233_; lean_object* v_name_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v___f_2226_);
lean_dec(v_modifyEnv_2225_);
v_toAttributeImplCore_2233_ = lean_ctor_get(v_attr_2230_, 0);
lean_inc_ref(v_toAttributeImplCore_2233_);
lean_dec_ref(v_attr_2230_);
v_name_2234_ = lean_ctor_get(v_toAttributeImplCore_2233_, 1);
lean_inc(v_name_2234_);
lean_dec_ref(v_toAttributeImplCore_2233_);
v___x_2235_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2219_);
v___x_2236_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2221_, v_inst_2222_, v_name_2234_, v_decl_2220_, v___x_2235_);
v___x_2237_ = lean_apply_4(v_toBind_2223_, lean_box(0), lean_box(0), v___x_2236_, v___f_2224_);
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; 
lean_dec_ref(v_attr_2230_);
lean_dec(v___f_2224_);
lean_dec(v_toBind_2223_);
lean_dec_ref(v_inst_2222_);
lean_dec_ref(v_inst_2221_);
lean_dec(v_decl_2220_);
lean_dec_ref(v_env_2219_);
v___x_2238_ = lean_apply_1(v_modifyEnv_2225_, v___f_2226_);
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2239_, lean_object* v_____r_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_apply_1(v___f_2239_, v_____r_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2242_, lean_object* v_decl_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_toBind_2246_, lean_object* v___f_2247_, lean_object* v_modifyEnv_2248_, lean_object* v___f_2249_, lean_object* v_env_2250_){
_start:
{
lean_object* v___f_2251_; lean_object* v___x_2252_; 
lean_inc_ref(v___f_2249_);
lean_inc(v_modifyEnv_2248_);
lean_inc(v___f_2247_);
lean_inc(v_toBind_2246_);
lean_inc_ref(v_inst_2245_);
lean_inc_ref(v_inst_2244_);
lean_inc(v_decl_2243_);
lean_inc_ref(v_env_2250_);
lean_inc_ref(v_attr_2242_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2251_, 0, v_attr_2242_);
lean_closure_set(v___f_2251_, 1, v_env_2250_);
lean_closure_set(v___f_2251_, 2, v_decl_2243_);
lean_closure_set(v___f_2251_, 3, v_inst_2244_);
lean_closure_set(v___f_2251_, 4, v_inst_2245_);
lean_closure_set(v___f_2251_, 5, v_toBind_2246_);
lean_closure_set(v___f_2251_, 6, v___f_2247_);
lean_closure_set(v___f_2251_, 7, v_modifyEnv_2248_);
lean_closure_set(v___f_2251_, 8, v___f_2249_);
v___x_2252_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2250_, v_decl_2243_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec_ref(v___f_2251_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2242_, v_env_2250_, v_decl_2243_, v_inst_2244_, v_inst_2245_, v_toBind_2246_, v___f_2247_, v_modifyEnv_2248_, v___f_2249_, v___x_2253_);
return v___x_2254_;
}
else
{
lean_object* v_attr_2255_; lean_object* v_toAttributeImplCore_2256_; lean_object* v_name_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec_ref_known(v___x_2252_, 1);
lean_dec_ref(v_env_2250_);
lean_dec_ref(v___f_2249_);
lean_dec(v_modifyEnv_2248_);
lean_dec(v___f_2247_);
v_attr_2255_ = lean_ctor_get(v_attr_2242_, 0);
lean_inc_ref(v_attr_2255_);
lean_dec_ref(v_attr_2242_);
v_toAttributeImplCore_2256_ = lean_ctor_get(v_attr_2255_, 0);
lean_inc_ref(v_toAttributeImplCore_2256_);
lean_dec_ref(v_attr_2255_);
v_name_2257_ = lean_ctor_get(v_toAttributeImplCore_2256_, 1);
lean_inc(v_name_2257_);
lean_dec_ref(v_toAttributeImplCore_2256_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2258_, 0, v___f_2251_);
v___x_2259_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2244_, v_inst_2245_, v_name_2257_, v_decl_2243_);
v___x_2260_ = lean_apply_4(v_toBind_2246_, lean_box(0), lean_box(0), v___x_2259_, v___f_2258_);
return v___x_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_attr_2264_, lean_object* v_decl_2265_){
_start:
{
lean_object* v_toBind_2266_; lean_object* v_getEnv_2267_; lean_object* v_modifyEnv_2268_; lean_object* v___f_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; 
v_toBind_2266_ = lean_ctor_get(v_inst_2261_, 1);
lean_inc_n(v_toBind_2266_, 2);
v_getEnv_2267_ = lean_ctor_get(v_inst_2263_, 0);
lean_inc(v_getEnv_2267_);
v_modifyEnv_2268_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc_n(v_modifyEnv_2268_, 2);
lean_dec_ref(v_inst_2263_);
lean_inc(v_decl_2265_);
lean_inc_ref(v_attr_2264_);
v___f_2269_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2269_, 0, v_attr_2264_);
lean_closure_set(v___f_2269_, 1, v_decl_2265_);
lean_inc_ref(v___f_2269_);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2270_, 0, v_modifyEnv_2268_);
lean_closure_set(v___f_2270_, 1, v___f_2269_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2271_, 0, v_attr_2264_);
lean_closure_set(v___f_2271_, 1, v_decl_2265_);
lean_closure_set(v___f_2271_, 2, v_inst_2261_);
lean_closure_set(v___f_2271_, 3, v_inst_2262_);
lean_closure_set(v___f_2271_, 4, v_toBind_2266_);
lean_closure_set(v___f_2271_, 5, v___f_2270_);
lean_closure_set(v___f_2271_, 6, v_modifyEnv_2268_);
lean_closure_set(v___f_2271_, 7, v___f_2269_);
v___x_2272_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v_getEnv_2267_, v___f_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_attr_2277_, lean_object* v_decl_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2274_, v_inst_2275_, v_inst_2276_, v_attr_2277_, v_decl_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2280_, lean_object* v_as_2281_, lean_object* v_k_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_m_2287_; lean_object* v_a_2288_; uint8_t v___x_2289_; 
v___x_2285_ = lean_nat_add(v_x_2283_, v_x_2284_);
v___x_2286_ = lean_unsigned_to_nat(1u);
v_m_2287_ = lean_nat_shiftr(v___x_2285_, v___x_2286_);
lean_dec(v___x_2285_);
v_a_2288_ = lean_array_fget_borrowed(v_as_2281_, v_m_2287_);
v___x_2289_ = l_Lean_Name_quickLt(v_a_2288_, v_k_2282_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; uint8_t v___x_2291_; 
lean_dec(v_x_2284_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = l_Lean_Name_quickLt(v_k_2282_, v_a_2288_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; 
lean_dec(v_m_2287_);
lean_dec(v_x_2283_);
v___x_2292_ = lean_nat_dec_le(v___x_2290_, v___y_2280_);
return v___x_2292_;
}
else
{
uint8_t v___x_2293_; lean_object* v___x_2294_; uint8_t v___y_2296_; 
v___x_2293_ = lean_nat_dec_eq(v_m_2287_, v___x_2290_);
v___x_2294_ = lean_nat_sub(v_m_2287_, v___x_2286_);
lean_dec(v_m_2287_);
if (v___x_2293_ == 0)
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_nat_dec_lt(v___x_2294_, v_x_2283_);
v___y_2296_ = v___x_2298_;
goto v___jp_2295_;
}
else
{
v___y_2296_ = v___x_2293_;
goto v___jp_2295_;
}
v___jp_2295_:
{
if (v___y_2296_ == 0)
{
v_x_2284_ = v___x_2294_;
goto _start;
}
else
{
lean_dec(v___x_2294_);
lean_dec(v_x_2283_);
return v___x_2289_;
}
}
}
}
else
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
lean_dec(v_x_2283_);
v___x_2299_ = lean_nat_add(v_m_2287_, v___x_2286_);
lean_dec(v_m_2287_);
v___x_2300_ = lean_nat_dec_le(v___x_2299_, v_x_2284_);
if (v___x_2300_ == 0)
{
lean_dec(v___x_2299_);
lean_dec(v_x_2284_);
return v___x_2300_;
}
else
{
v_x_2283_ = v___x_2299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2302_, lean_object* v_as_2303_, lean_object* v_k_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_){
_start:
{
uint8_t v_res_2307_; lean_object* v_r_2308_; 
v_res_2307_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2302_, v_as_2303_, v_k_2304_, v_x_2305_, v_x_2306_);
lean_dec(v_k_2304_);
lean_dec_ref(v_as_2303_);
lean_dec(v___y_2302_);
v_r_2308_ = lean_box(v_res_2307_);
return v_r_2308_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2309_, lean_object* v_env_2310_, lean_object* v_decl_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_box(1);
v___x_2313_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2310_, v_decl_2311_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_ext_2314_; lean_object* v_toEnvExtension_2315_; lean_object* v_asyncMode_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_ext_2314_ = lean_ctor_get(v_attr_2309_, 1);
v_toEnvExtension_2315_ = lean_ctor_get(v_ext_2314_, 0);
v_asyncMode_2316_ = lean_ctor_get(v_toEnvExtension_2315_, 2);
lean_inc(v_decl_2311_);
v___x_2317_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2312_, v_ext_2314_, v_env_2310_, v_asyncMode_2316_, v_decl_2311_);
v___x_2318_ = l_Lean_NameSet_contains(v___x_2317_, v_decl_2311_);
lean_dec(v_decl_2311_);
lean_dec(v___x_2317_);
return v___x_2318_;
}
else
{
lean_object* v_val_2319_; lean_object* v_ext_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_val_2319_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_val_2319_);
lean_dec_ref_known(v___x_2313_, 1);
v_ext_2320_ = lean_ctor_get(v_attr_2309_, 1);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2312_, v_ext_2320_, v_env_2310_, v_val_2319_, v___x_2321_);
lean_dec(v_val_2319_);
lean_dec_ref(v_env_2310_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_array_get_size(v___x_2322_);
v___x_2325_ = lean_nat_dec_lt(v___x_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_dec_ref(v___x_2322_);
lean_dec(v_decl_2311_);
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_sub(v___x_2324_, v___x_2326_);
v___x_2328_ = lean_nat_dec_le(v___x_2323_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_dec(v___x_2327_);
lean_dec_ref(v___x_2322_);
lean_dec(v_decl_2311_);
return v___x_2328_;
}
else
{
uint8_t v___x_2329_; 
lean_inc(v___x_2327_);
v___x_2329_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2327_, v___x_2322_, v_decl_2311_, v___x_2323_, v___x_2327_);
lean_dec(v_decl_2311_);
lean_dec_ref(v___x_2322_);
lean_dec(v___x_2327_);
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2330_, lean_object* v_env_2331_, lean_object* v_decl_2332_){
_start:
{
uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_res_2333_ = l_Lean_TagAttribute_hasTag(v_attr_2330_, v_env_2331_, v_decl_2332_);
lean_dec_ref(v_attr_2330_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2335_, lean_object* v_as_2336_, lean_object* v_k_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2335_, v_as_2336_, v_k_2337_, v_x_2338_, v_x_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2342_, lean_object* v_as_2343_, lean_object* v_k_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_res_2348_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2342_, v_as_2343_, v_k_2344_, v_x_2345_, v_x_2346_, v_x_2347_);
lean_dec(v_k_2344_);
lean_dec_ref(v_as_2343_);
lean_dec(v___y_2342_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2355_, v___y_2356_);
lean_dec_ref(v___y_2356_);
lean_dec_ref(v_x_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2359_, lean_object* v_x_2360_){
_start:
{
lean_inc_ref(v_s_2359_);
return v_s_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2361_, lean_object* v_x_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2361_, v_x_2362_);
lean_dec_ref(v_x_2362_);
lean_dec_ref(v_s_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2368_, lean_object* v_x_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2371_, v_x_2372_);
lean_dec_ref(v_x_2372_);
lean_dec_ref(v_x_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_box(0);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2376_);
lean_dec_ref(v_x_2376_);
return v_res_2377_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2383_; lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___f_2383_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2384_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
lean_ctor_set(v___x_2389_, 2, v___f_2386_);
lean_ctor_set(v___x_2389_, 3, v___f_2385_);
lean_ctor_set(v___x_2389_, 4, v___f_2384_);
lean_ctor_set(v___x_2389_, 5, v___f_2383_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2390_ = 0;
v___x_2391_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2392_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2393_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v___x_2391_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*2, v___x_2390_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2399_, lean_object* v_p_2400_){
_start:
{
lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2419_; 
v_fst_2401_ = lean_ctor_get(v_x_2399_, 0);
v_snd_2402_ = lean_ctor_get(v_x_2399_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_x_2399_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2404_ = v_x_2399_;
v_isShared_2405_ = v_isSharedCheck_2419_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snd_2402_);
lean_inc(v_fst_2401_);
lean_dec(v_x_2399_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2419_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v_fst_2406_; lean_object* v_snd_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2418_; 
v_fst_2406_ = lean_ctor_get(v_p_2400_, 0);
v_snd_2407_ = lean_ctor_get(v_p_2400_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_p_2400_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2409_ = v_p_2400_;
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_snd_2407_);
lean_inc(v_fst_2406_);
lean_dec(v_p_2400_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2418_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
lean_inc(v_fst_2406_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 1);
lean_ctor_set(v___x_2404_, 1, v_fst_2401_);
lean_ctor_set(v___x_2404_, 0, v_fst_2406_);
v___x_2412_ = v___x_2404_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_fst_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_fst_2401_);
v___x_2412_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2406_, v_snd_2407_, v_snd_2402_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2413_);
lean_ctor_set(v___x_2409_, 0, v___x_2412_);
v___x_2415_ = v___x_2409_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_l_2424_; lean_object* v_r_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_k_2422_ = lean_ctor_get(v_x_2421_, 1);
v_v_2423_ = lean_ctor_get(v_x_2421_, 2);
v_l_2424_ = lean_ctor_get(v_x_2421_, 3);
v_r_2425_ = lean_ctor_get(v_x_2421_, 4);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2420_, v_l_2424_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_k_2422_);
lean_ctor_set(v___x_2427_, 1, v_v_2423_);
v___x_2428_ = lean_array_push(v___x_2426_, v___x_2427_);
v_init_2420_ = v___x_2428_;
v_x_2421_ = v_r_2425_;
goto _start;
}
else
{
return v_init_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2430_, lean_object* v_x_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2430_, v_x_2431_);
lean_dec(v_x_2431_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2433_, lean_object* v_as_2434_, size_t v_i_2435_, size_t v_stop_2436_, lean_object* v_b_2437_){
_start:
{
lean_object* v___y_2439_; uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_eq(v_i_2435_, v_stop_2436_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_array_uget_borrowed(v_as_2434_, v_i_2435_);
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2433_, v___x_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
v___y_2439_ = v_b_2437_;
goto v___jp_2438_;
}
else
{
lean_object* v_val_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_val_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2446_);
lean_dec_ref_known(v___x_2445_, 1);
lean_inc(v___x_2444_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2444_);
lean_ctor_set(v___x_2447_, 1, v_val_2446_);
v___x_2448_ = lean_array_push(v_b_2437_, v___x_2447_);
v___y_2439_ = v___x_2448_;
goto v___jp_2438_;
}
}
else
{
return v_b_2437_;
}
v___jp_2438_:
{
size_t v___x_2440_; size_t v___x_2441_; 
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_add(v_i_2435_, v___x_2440_);
v_i_2435_ = v___x_2441_;
v_b_2437_ = v___y_2439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2449_, lean_object* v_as_2450_, lean_object* v_i_2451_, lean_object* v_stop_2452_, lean_object* v_b_2453_){
_start:
{
size_t v_i_boxed_2454_; size_t v_stop_boxed_2455_; lean_object* v_res_2456_; 
v_i_boxed_2454_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_stop_boxed_2455_ = lean_unbox_usize(v_stop_2452_);
lean_dec(v_stop_2452_);
v_res_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2449_, v_as_2450_, v_i_boxed_2454_, v_stop_boxed_2455_, v_b_2453_);
lean_dec_ref(v_as_2450_);
lean_dec(v_snd_2449_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2457_, lean_object* v_as_2458_, lean_object* v_start_2459_, lean_object* v_stop_2460_){
_start:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2462_ = lean_nat_dec_lt(v_start_2459_, v_stop_2460_);
if (v___x_2462_ == 0)
{
return v___x_2461_;
}
else
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_array_get_size(v_as_2458_);
v___x_2464_ = lean_nat_dec_le(v_stop_2460_, v___x_2463_);
if (v___x_2464_ == 0)
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_nat_dec_lt(v_start_2459_, v___x_2463_);
if (v___x_2465_ == 0)
{
return v___x_2461_;
}
else
{
size_t v___x_2466_; size_t v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_usize_of_nat(v_start_2459_);
v___x_2467_ = lean_usize_of_nat(v___x_2463_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2457_, v_as_2458_, v___x_2466_, v___x_2467_, v___x_2461_);
return v___x_2468_;
}
}
else
{
size_t v___x_2469_; size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_usize_of_nat(v_start_2459_);
v___x_2470_ = lean_usize_of_nat(v_stop_2460_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2457_, v_as_2458_, v___x_2469_, v___x_2470_, v___x_2461_);
return v___x_2471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2472_, lean_object* v_as_2473_, lean_object* v_start_2474_, lean_object* v_stop_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2472_, v_as_2473_, v_start_2474_, v_stop_2475_);
lean_dec(v_stop_2475_);
lean_dec(v_start_2474_);
lean_dec_ref(v_as_2473_);
lean_dec(v_snd_2472_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2477_, lean_object* v_pivot_2478_, lean_object* v_as_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_nat_dec_lt(v_k_2481_, v_hi_2477_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
lean_dec(v_k_2481_);
v___x_2483_ = lean_array_fswap(v_as_2479_, v_i_2480_, v_hi_2477_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_i_2480_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; lean_object* v_fst_2486_; lean_object* v_fst_2487_; uint8_t v___x_2488_; 
v___x_2485_ = lean_array_fget_borrowed(v_as_2479_, v_k_2481_);
v_fst_2486_ = lean_ctor_get(v___x_2485_, 0);
v_fst_2487_ = lean_ctor_get(v_pivot_2478_, 0);
v___x_2488_ = l_Lean_Name_quickLt(v_fst_2486_, v_fst_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_unsigned_to_nat(1u);
v___x_2490_ = lean_nat_add(v_k_2481_, v___x_2489_);
lean_dec(v_k_2481_);
v_k_2481_ = v___x_2490_;
goto _start;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_array_fswap(v_as_2479_, v_i_2480_, v_k_2481_);
v___x_2493_ = lean_unsigned_to_nat(1u);
v___x_2494_ = lean_nat_add(v_i_2480_, v___x_2493_);
lean_dec(v_i_2480_);
v___x_2495_ = lean_nat_add(v_k_2481_, v___x_2493_);
lean_dec(v_k_2481_);
v_as_2479_ = v___x_2492_;
v_i_2480_ = v___x_2494_;
v_k_2481_ = v___x_2495_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2497_, lean_object* v_pivot_2498_, lean_object* v_as_2499_, lean_object* v_i_2500_, lean_object* v_k_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2497_, v_pivot_2498_, v_as_2499_, v_i_2500_, v_k_2501_);
lean_dec_ref(v_pivot_2498_);
lean_dec(v_hi_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v_fst_2505_; lean_object* v_fst_2506_; uint8_t v___x_2507_; 
v_fst_2505_ = lean_ctor_get(v_a_2503_, 0);
v_fst_2506_ = lean_ctor_get(v_b_2504_, 0);
v___x_2507_ = l_Lean_Name_quickLt(v_fst_2505_, v_fst_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2508_, lean_object* v_b_2509_){
_start:
{
uint8_t v_res_2510_; lean_object* v_r_2511_; 
v_res_2510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2508_, v_b_2509_);
lean_dec_ref(v_b_2509_);
lean_dec_ref(v_a_2508_);
v_r_2511_ = lean_box(v_res_2510_);
return v_r_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2512_, lean_object* v_as_2513_, lean_object* v_lo_2514_, lean_object* v_hi_2515_){
_start:
{
lean_object* v___y_2517_; uint8_t v___x_2527_; 
v___x_2527_ = lean_nat_dec_lt(v_lo_2514_, v_hi_2515_);
if (v___x_2527_ == 0)
{
lean_dec(v_lo_2514_);
return v_as_2513_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_mid_2530_; lean_object* v___y_2532_; lean_object* v___y_2538_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2528_ = lean_nat_add(v_lo_2514_, v_hi_2515_);
v___x_2529_ = lean_unsigned_to_nat(1u);
v_mid_2530_ = lean_nat_shiftr(v___x_2528_, v___x_2529_);
lean_dec(v___x_2528_);
v___x_2543_ = lean_array_fget_borrowed(v_as_2513_, v_mid_2530_);
v___x_2544_ = lean_array_fget_borrowed(v_as_2513_, v_lo_2514_);
v___x_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
v___y_2538_ = v_as_2513_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_array_fswap(v_as_2513_, v_lo_2514_, v_mid_2530_);
v___y_2538_ = v___x_2546_;
goto v___jp_2537_;
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = lean_array_fget_borrowed(v___y_2532_, v_mid_2530_);
v___x_2534_ = lean_array_fget_borrowed(v___y_2532_, v_hi_2515_);
v___x_2535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_dec(v_mid_2530_);
v___y_2517_ = v___y_2532_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_array_fswap(v___y_2532_, v_mid_2530_, v_hi_2515_);
lean_dec(v_mid_2530_);
v___y_2517_ = v___x_2536_;
goto v___jp_2516_;
}
}
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2539_ = lean_array_fget_borrowed(v___y_2538_, v_hi_2515_);
v___x_2540_ = lean_array_fget_borrowed(v___y_2538_, v_lo_2514_);
v___x_2541_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
v___y_2532_ = v___y_2538_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_array_fswap(v___y_2538_, v_lo_2514_, v_hi_2515_);
v___y_2532_ = v___x_2542_;
goto v___jp_2531_;
}
}
}
v___jp_2516_:
{
lean_object* v_pivot_2518_; lean_object* v___x_2519_; lean_object* v_fst_2520_; lean_object* v_snd_2521_; uint8_t v___x_2522_; 
v_pivot_2518_ = lean_array_fget(v___y_2517_, v_hi_2515_);
lean_inc_n(v_lo_2514_, 2);
v___x_2519_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2515_, v_pivot_2518_, v___y_2517_, v_lo_2514_, v_lo_2514_);
lean_dec(v_pivot_2518_);
v_fst_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_fst_2520_);
v_snd_2521_ = lean_ctor_get(v___x_2519_, 1);
lean_inc(v_snd_2521_);
lean_dec_ref(v___x_2519_);
v___x_2522_ = lean_nat_dec_le(v_hi_2515_, v_fst_2520_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2512_, v_snd_2521_, v_lo_2514_, v_fst_2520_);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_add(v_fst_2520_, v___x_2524_);
lean_dec(v_fst_2520_);
v_as_2513_ = v___x_2523_;
v_lo_2514_ = v___x_2525_;
goto _start;
}
else
{
lean_dec(v_fst_2520_);
lean_dec(v_lo_2514_);
return v_snd_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2547_, lean_object* v_as_2548_, lean_object* v_lo_2549_, lean_object* v_hi_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2547_, v_as_2548_, v_lo_2549_, v_hi_2550_);
lean_dec(v_hi_2550_);
lean_dec(v_n_2547_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2552_, lean_object* v_env_2553_, lean_object* v_as_2554_, size_t v_i_2555_, size_t v_stop_2556_, lean_object* v_b_2557_){
_start:
{
lean_object* v___y_2559_; uint8_t v___x_2563_; 
v___x_2563_ = lean_usize_dec_eq(v_i_2555_, v_stop_2556_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2564_ = lean_array_uget_borrowed(v_as_2554_, v_i_2555_);
v_fst_2565_ = lean_ctor_get(v___x_2564_, 0);
v_snd_2566_ = lean_ctor_get(v___x_2564_, 1);
lean_inc_ref(v_filterExport_2552_);
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_inc_ref(v_env_2553_);
v___x_2567_ = lean_apply_3(v_filterExport_2552_, v_env_2553_, v_fst_2565_, v_snd_2566_);
v___x_2568_ = lean_unbox(v___x_2567_);
if (v___x_2568_ == 0)
{
v___y_2559_ = v_b_2557_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2569_; 
lean_inc(v___x_2564_);
v___x_2569_ = lean_array_push(v_b_2557_, v___x_2564_);
v___y_2559_ = v___x_2569_;
goto v___jp_2558_;
}
}
else
{
lean_dec_ref(v_env_2553_);
lean_dec_ref(v_filterExport_2552_);
return v_b_2557_;
}
v___jp_2558_:
{
size_t v___x_2560_; size_t v___x_2561_; 
v___x_2560_ = ((size_t)1ULL);
v___x_2561_ = lean_usize_add(v_i_2555_, v___x_2560_);
v_i_2555_ = v___x_2561_;
v_b_2557_ = v___y_2559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2570_, lean_object* v_env_2571_, lean_object* v_as_2572_, lean_object* v_i_2573_, lean_object* v_stop_2574_, lean_object* v_b_2575_){
_start:
{
size_t v_i_boxed_2576_; size_t v_stop_boxed_2577_; lean_object* v_res_2578_; 
v_i_boxed_2576_ = lean_unbox_usize(v_i_2573_);
lean_dec(v_i_2573_);
v_stop_boxed_2577_ = lean_unbox_usize(v_stop_2574_);
lean_dec(v_stop_2574_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2570_, v_env_2571_, v_as_2572_, v_i_boxed_2576_, v_stop_boxed_2577_, v_b_2575_);
lean_dec_ref(v_as_2572_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2579_, uint8_t v_preserveOrder_2580_, lean_object* v_env_2581_, lean_object* v_x_2582_){
_start:
{
lean_object* v___y_2584_; 
if (v_preserveOrder_2580_ == 0)
{
lean_object* v_snd_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_r_2603_; lean_object* v___x_2604_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___x_2609_; 
v_snd_2600_ = lean_ctor_get(v_x_2582_, 1);
lean_inc(v_snd_2600_);
lean_dec_ref(v_x_2582_);
v___x_2601_ = lean_unsigned_to_nat(0u);
v___x_2602_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2603_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2602_, v_snd_2600_);
lean_dec(v_snd_2600_);
v___x_2604_ = lean_array_get_size(v_r_2603_);
v___x_2609_ = lean_nat_dec_eq(v___x_2604_, v___x_2601_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___y_2613_; uint8_t v___x_2615_; 
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_sub(v___x_2604_, v___x_2610_);
v___x_2615_ = lean_nat_dec_le(v___x_2601_, v___x_2611_);
if (v___x_2615_ == 0)
{
lean_inc(v___x_2611_);
v___y_2613_ = v___x_2611_;
goto v___jp_2612_;
}
else
{
v___y_2613_ = v___x_2601_;
goto v___jp_2612_;
}
v___jp_2612_:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_nat_dec_le(v___y_2613_, v___x_2611_);
if (v___x_2614_ == 0)
{
lean_dec(v___x_2611_);
lean_inc(v___y_2613_);
v___y_2606_ = v___y_2613_;
v___y_2607_ = v___y_2613_;
goto v___jp_2605_;
}
else
{
v___y_2606_ = v___y_2613_;
v___y_2607_ = v___x_2611_;
goto v___jp_2605_;
}
}
}
else
{
v___y_2584_ = v_r_2603_;
goto v___jp_2583_;
}
v___jp_2605_:
{
lean_object* v___x_2608_; 
v___x_2608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2604_, v_r_2603_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
v___y_2584_ = v___x_2608_;
goto v___jp_2583_;
}
}
else
{
lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_fst_2616_ = lean_ctor_get(v_x_2582_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v_x_2582_, 1);
lean_inc(v_snd_2617_);
lean_dec_ref(v_x_2582_);
v___x_2618_ = lean_array_mk(v_fst_2616_);
v___x_2619_ = l_Array_reverse___redArg(v___x_2618_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_size(v___x_2619_);
v___x_2622_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2617_, v___x_2619_, v___x_2620_, v___x_2621_);
lean_dec_ref(v___x_2619_);
lean_dec(v_snd_2617_);
v___y_2584_ = v___x_2622_;
goto v___jp_2583_;
}
v___jp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_array_get_size(v___y_2584_);
v___x_2587_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2588_ = lean_nat_dec_lt(v___x_2585_, v___x_2586_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
lean_dec_ref(v_env_2581_);
lean_dec_ref(v_filterExport_2579_);
v___x_2589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2587_);
lean_ctor_set(v___x_2589_, 2, v___y_2584_);
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; 
v___x_2590_ = lean_nat_dec_le(v___x_2586_, v___x_2586_);
if (v___x_2590_ == 0)
{
if (v___x_2588_ == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref(v_env_2581_);
lean_dec_ref(v_filterExport_2579_);
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2587_);
lean_ctor_set(v___x_2591_, 2, v___y_2584_);
return v___x_2591_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2586_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2579_, v_env_2581_, v___y_2584_, v___x_2592_, v___x_2593_, v___x_2587_);
lean_inc_ref(v___x_2594_);
v___x_2595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
lean_ctor_set(v___x_2595_, 2, v___y_2584_);
return v___x_2595_;
}
}
else
{
size_t v___x_2596_; size_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2596_ = ((size_t)0ULL);
v___x_2597_ = lean_usize_of_nat(v___x_2586_);
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2579_, v_env_2581_, v___y_2584_, v___x_2596_, v___x_2597_, v___x_2587_);
lean_inc_ref(v___x_2598_);
v___x_2599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
lean_ctor_set(v___x_2599_, 2, v___y_2584_);
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2623_, lean_object* v_preserveOrder_2624_, lean_object* v_env_2625_, lean_object* v_x_2626_){
_start:
{
uint8_t v_preserveOrder_boxed_2627_; lean_object* v_res_2628_; 
v_preserveOrder_boxed_2627_ = lean_unbox(v_preserveOrder_2624_);
v_res_2628_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2623_, v_preserveOrder_boxed_2627_, v_env_2625_, v_x_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2638_){
_start:
{
lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2653_; 
v_snd_2639_ = lean_ctor_get(v_x_2638_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_x_2638_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_x_2638_, 0);
lean_dec(v_unused_2654_);
v___x_2641_ = v_x_2638_;
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_dec(v_x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2653_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___y_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2639_) == 0)
{
lean_object* v_size_2651_; 
v_size_2651_ = lean_ctor_get(v_snd_2639_, 0);
lean_inc(v_size_2651_);
lean_dec_ref_known(v_snd_2639_, 5);
v___y_2645_ = v_size_2651_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___y_2645_ = v___x_2652_;
goto v___jp_2644_;
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2646_ = l_Nat_reprFast(v___y_2645_);
v___x_2647_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 5);
lean_ctor_set(v___x_2641_, 1, v___x_2647_);
lean_ctor_set(v___x_2641_, 0, v___x_2643_);
v___x_2649_ = v___x_2641_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2655_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2657_);
lean_dec_ref(v_x_2657_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2665_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2670_, lean_object* v_x_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2670_, v_x_2671_, v___y_2672_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v_x_2671_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2685_, uint8_t v_preserveOrder_2686_, lean_object* v_filterExport_2687_){
_start:
{
lean_object* v___f_2689_; lean_object* v___x_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___f_2689_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2690_ = lean_box(v_preserveOrder_2686_);
v___f_2691_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2691_, 0, v_filterExport_2687_);
lean_closure_set(v___f_2691_, 1, v___x_2690_);
v___f_2692_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2693_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2696_ = lean_box(2);
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2698_, 0, v_ref_2685_);
lean_ctor_set(v___x_2698_, 1, v___f_2694_);
lean_ctor_set(v___x_2698_, 2, v___f_2695_);
lean_ctor_set(v___x_2698_, 3, v___f_2689_);
lean_ctor_set(v___x_2698_, 4, v___f_2691_);
lean_ctor_set(v___x_2698_, 5, v___f_2692_);
lean_ctor_set(v___x_2698_, 6, v___x_2696_);
lean_ctor_set(v___x_2698_, 7, v___x_2697_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___f_2693_);
v___x_2700_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2701_, lean_object* v_preserveOrder_2702_, lean_object* v_filterExport_2703_, lean_object* v_a_2704_){
_start:
{
uint8_t v_preserveOrder_boxed_2705_; lean_object* v_res_2706_; 
v_preserveOrder_boxed_2705_ = lean_unbox(v_preserveOrder_2702_);
v_res_2706_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2701_, v_preserveOrder_boxed_2705_, v_filterExport_2703_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2707_, lean_object* v_ref_2708_, uint8_t v_preserveOrder_2709_, lean_object* v_filterExport_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2708_, v_preserveOrder_2709_, v_filterExport_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2713_, lean_object* v_ref_2714_, lean_object* v_preserveOrder_2715_, lean_object* v_filterExport_2716_, lean_object* v_a_2717_){
_start:
{
uint8_t v_preserveOrder_boxed_2718_; lean_object* v_res_2719_; 
v_preserveOrder_boxed_2718_ = lean_unbox(v_preserveOrder_2715_);
v_res_2719_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2713_, v_ref_2714_, v_preserveOrder_boxed_2718_, v_filterExport_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2720_, lean_object* v_filterExport_2721_, lean_object* v_env_2722_, lean_object* v_as_2723_, size_t v_i_2724_, size_t v_stop_2725_, lean_object* v_b_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2721_, v_env_2722_, v_as_2723_, v_i_2724_, v_stop_2725_, v_b_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_filterExport_2729_, lean_object* v_env_2730_, lean_object* v_as_2731_, lean_object* v_i_2732_, lean_object* v_stop_2733_, lean_object* v_b_2734_){
_start:
{
size_t v_i_boxed_2735_; size_t v_stop_boxed_2736_; lean_object* v_res_2737_; 
v_i_boxed_2735_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_stop_boxed_2736_ = lean_unbox_usize(v_stop_2733_);
lean_dec(v_stop_2733_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2728_, v_filterExport_2729_, v_env_2730_, v_as_2731_, v_i_boxed_2735_, v_stop_boxed_2736_, v_b_2734_);
lean_dec_ref(v_as_2731_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2738_, lean_object* v_t_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2738_, v_t_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2741_, lean_object* v_t_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2741_, v_t_2742_);
lean_dec(v_t_2742_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2744_, lean_object* v_init_2745_, lean_object* v_t_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2745_, v_t_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_init_2749_, lean_object* v_t_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2748_, v_init_2749_, v_t_2750_);
lean_dec(v_t_2750_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2752_, lean_object* v_n_2753_, lean_object* v_as_2754_, lean_object* v_lo_2755_, lean_object* v_hi_2756_, lean_object* v_w_2757_, lean_object* v_hlo_2758_, lean_object* v_hhi_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2753_, v_as_2754_, v_lo_2755_, v_hi_2756_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_n_2762_, lean_object* v_as_2763_, lean_object* v_lo_2764_, lean_object* v_hi_2765_, lean_object* v_w_2766_, lean_object* v_hlo_2767_, lean_object* v_hhi_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2761_, v_n_2762_, v_as_2763_, v_lo_2764_, v_hi_2765_, v_w_2766_, v_hlo_2767_, v_hhi_2768_);
lean_dec(v_hi_2765_);
lean_dec(v_n_2762_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2770_, lean_object* v_snd_2771_, lean_object* v_as_2772_, lean_object* v_start_2773_, lean_object* v_stop_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2771_, v_as_2772_, v_start_2773_, v_stop_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_snd_2777_, lean_object* v_as_2778_, lean_object* v_start_2779_, lean_object* v_stop_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2776_, v_snd_2777_, v_as_2778_, v_start_2779_, v_stop_2780_);
lean_dec(v_stop_2780_);
lean_dec(v_start_2779_);
lean_dec_ref(v_as_2778_);
lean_dec(v_snd_2777_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2782_, lean_object* v_init_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2783_, v_x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_init_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2786_, v_init_2787_, v_x_2788_);
lean_dec(v_x_2788_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2790_, lean_object* v_n_2791_, lean_object* v_lo_2792_, lean_object* v_hi_2793_, lean_object* v_hhi_2794_, lean_object* v_pivot_2795_, lean_object* v_as_2796_, lean_object* v_i_2797_, lean_object* v_k_2798_, lean_object* v_ilo_2799_, lean_object* v_ik_2800_, lean_object* v_w_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2793_, v_pivot_2795_, v_as_2796_, v_i_2797_, v_k_2798_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2803_, lean_object* v_n_2804_, lean_object* v_lo_2805_, lean_object* v_hi_2806_, lean_object* v_hhi_2807_, lean_object* v_pivot_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_k_2811_, lean_object* v_ilo_2812_, lean_object* v_ik_2813_, lean_object* v_w_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2803_, v_n_2804_, v_lo_2805_, v_hi_2806_, v_hhi_2807_, v_pivot_2808_, v_as_2809_, v_i_2810_, v_k_2811_, v_ilo_2812_, v_ik_2813_, v_w_2814_);
lean_dec_ref(v_pivot_2808_);
lean_dec(v_hi_2806_);
lean_dec(v_lo_2805_);
lean_dec(v_n_2804_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2816_, lean_object* v_snd_2817_, lean_object* v_as_2818_, size_t v_i_2819_, size_t v_stop_2820_, lean_object* v_b_2821_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2817_, v_as_2818_, v_i_2819_, v_stop_2820_, v_b_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_snd_2824_, lean_object* v_as_2825_, lean_object* v_i_2826_, lean_object* v_stop_2827_, lean_object* v_b_2828_){
_start:
{
size_t v_i_boxed_2829_; size_t v_stop_boxed_2830_; lean_object* v_res_2831_; 
v_i_boxed_2829_ = lean_unbox_usize(v_i_2826_);
lean_dec(v_i_2826_);
v_stop_boxed_2830_ = lean_unbox_usize(v_stop_2827_);
lean_dec(v_stop_2827_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2823_, v_snd_2824_, v_as_2825_, v_i_boxed_2829_, v_stop_boxed_2830_, v_b_2828_);
lean_dec_ref(v_as_2825_);
lean_dec(v_snd_2824_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v_nextMacroScope_2836_; lean_object* v_ngen_2837_; lean_object* v_auxDeclNGen_2838_; lean_object* v_traceState_2839_; lean_object* v_messages_2840_; lean_object* v_infoState_2841_; lean_object* v_snapshotTasks_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2853_; 
v___x_2835_ = lean_st_ref_take(v___y_2833_);
v_nextMacroScope_2836_ = lean_ctor_get(v___x_2835_, 1);
v_ngen_2837_ = lean_ctor_get(v___x_2835_, 2);
v_auxDeclNGen_2838_ = lean_ctor_get(v___x_2835_, 3);
v_traceState_2839_ = lean_ctor_get(v___x_2835_, 4);
v_messages_2840_ = lean_ctor_get(v___x_2835_, 6);
v_infoState_2841_ = lean_ctor_get(v___x_2835_, 7);
v_snapshotTasks_2842_ = lean_ctor_get(v___x_2835_, 8);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; lean_object* v_unused_2855_; 
v_unused_2854_ = lean_ctor_get(v___x_2835_, 5);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v___x_2835_, 0);
lean_dec(v_unused_2855_);
v___x_2844_ = v___x_2835_;
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snapshotTasks_2842_);
lean_inc(v_infoState_2841_);
lean_inc(v_messages_2840_);
lean_inc(v_traceState_2839_);
lean_inc(v_auxDeclNGen_2838_);
lean_inc(v_ngen_2837_);
lean_inc(v_nextMacroScope_2836_);
lean_dec(v___x_2835_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2846_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 5, v___x_2846_);
lean_ctor_set(v___x_2844_, 0, v_env_2832_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_env_2832_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_nextMacroScope_2836_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_ngen_2837_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_auxDeclNGen_2838_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v_traceState_2839_);
lean_ctor_set(v_reuseFailAlloc_2852_, 5, v___x_2846_);
lean_ctor_set(v_reuseFailAlloc_2852_, 6, v_messages_2840_);
lean_ctor_set(v_reuseFailAlloc_2852_, 7, v_infoState_2841_);
lean_ctor_set(v_reuseFailAlloc_2852_, 8, v_snapshotTasks_2842_);
v___x_2848_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = lean_st_ref_put(v___y_2833_, v___x_2848_);
v___x_2850_ = lean_box(0);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2856_, v___y_2857_);
lean_dec(v___y_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2860_, v___y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2870_, lean_object* v_ext_2871_, lean_object* v_afterSet_2872_, lean_object* v_toAttributeImplCore_2873_, lean_object* v_decl_2874_, lean_object* v_stx_2875_, uint8_t v_kind_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; uint8_t v___y_2885_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; uint8_t v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = 0;
v___x_2935_ = l_Lean_instBEqAttributeKind_beq(v_kind_2876_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v_name_2936_; lean_object* v___x_2937_; 
lean_dec(v_stx_2875_);
lean_dec(v_decl_2874_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
lean_dec_ref(v_getParam_2870_);
v_name_2936_ = lean_ctor_get(v_toAttributeImplCore_2873_, 1);
lean_inc(v_name_2936_);
lean_dec_ref(v_toAttributeImplCore_2873_);
v___x_2937_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2936_, v_kind_2876_, v___y_2877_, v___y_2878_);
return v___x_2937_;
}
else
{
goto v___jp_2928_;
}
v___jp_2880_:
{
if (v___y_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec_ref(v___y_2882_);
v___x_2886_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2881_, v___y_2883_);
return v___x_2886_;
}
else
{
lean_dec_ref(v___y_2881_);
return v___y_2882_;
}
}
v___jp_2887_:
{
lean_object* v___x_2891_; 
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v_decl_2874_);
v___x_2891_ = lean_apply_5(v_getParam_2870_, v_decl_2874_, v_stx_2875_, v___y_2889_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v_toEnvExtension_2894_; lean_object* v_env_2895_; lean_object* v_nextMacroScope_2896_; lean_object* v_ngen_2897_; lean_object* v_auxDeclNGen_2898_; lean_object* v_traceState_2899_; lean_object* v_messages_2900_; lean_object* v_infoState_2901_; lean_object* v_snapshotTasks_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2918_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = lean_st_ref_take(v___y_2890_);
v_toEnvExtension_2894_ = lean_ctor_get(v_ext_2871_, 0);
v_env_2895_ = lean_ctor_get(v___x_2893_, 0);
v_nextMacroScope_2896_ = lean_ctor_get(v___x_2893_, 1);
v_ngen_2897_ = lean_ctor_get(v___x_2893_, 2);
v_auxDeclNGen_2898_ = lean_ctor_get(v___x_2893_, 3);
v_traceState_2899_ = lean_ctor_get(v___x_2893_, 4);
v_messages_2900_ = lean_ctor_get(v___x_2893_, 6);
v_infoState_2901_ = lean_ctor_get(v___x_2893_, 7);
v_snapshotTasks_2902_ = lean_ctor_get(v___x_2893_, 8);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2893_, 5);
lean_dec(v_unused_2919_);
v___x_2904_ = v___x_2893_;
v_isShared_2905_ = v_isSharedCheck_2918_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snapshotTasks_2902_);
lean_inc(v_infoState_2901_);
lean_inc(v_messages_2900_);
lean_inc(v_traceState_2899_);
lean_inc(v_auxDeclNGen_2898_);
lean_inc(v_ngen_2897_);
lean_inc(v_nextMacroScope_2896_);
lean_inc(v_env_2895_);
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2918_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v_asyncMode_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v_asyncMode_2906_ = lean_ctor_get(v_toEnvExtension_2894_, 2);
lean_inc(v_asyncMode_2906_);
lean_inc(v_a_2892_);
lean_inc_n(v_decl_2874_, 2);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v_decl_2874_);
lean_ctor_set(v___x_2907_, 1, v_a_2892_);
v___x_2908_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2871_, v_env_2895_, v___x_2907_, v_asyncMode_2906_, v_decl_2874_);
lean_dec(v_asyncMode_2906_);
v___x_2909_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 5, v___x_2909_);
lean_ctor_set(v___x_2904_, 0, v___x_2908_);
v___x_2911_ = v___x_2904_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_nextMacroScope_2896_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_ngen_2897_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_auxDeclNGen_2898_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_traceState_2899_);
lean_ctor_set(v_reuseFailAlloc_2917_, 5, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2917_, 6, v_messages_2900_);
lean_ctor_set(v_reuseFailAlloc_2917_, 7, v_infoState_2901_);
lean_ctor_set(v_reuseFailAlloc_2917_, 8, v_snapshotTasks_2902_);
v___x_2911_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_st_ref_put(v___y_2890_, v___x_2911_);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
v___x_2913_ = lean_apply_5(v_afterSet_2872_, v_decl_2874_, v_a_2892_, v___y_2889_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref(v___y_2888_);
return v___x_2913_;
}
else
{
lean_object* v_a_2914_; uint8_t v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
v___x_2915_ = l_Lean_Exception_isInterrupt(v_a_2914_);
if (v___x_2915_ == 0)
{
uint8_t v___x_2916_; 
v___x_2916_ = l_Lean_Exception_isRuntime(v_a_2914_);
v___y_2881_ = v___y_2888_;
v___y_2882_ = v___x_2913_;
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___x_2916_;
goto v___jp_2880_;
}
else
{
lean_dec(v_a_2914_);
v___y_2881_ = v___y_2888_;
v___y_2882_ = v___x_2913_;
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___y_2889_;
v___y_2885_ = v___x_2915_;
goto v___jp_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v___y_2888_);
lean_dec(v_decl_2874_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
v_a_2920_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2891_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2891_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
v___jp_2928_:
{
lean_object* v___x_2929_; lean_object* v_env_2930_; lean_object* v___x_2931_; 
v___x_2929_ = lean_st_ref_get(v___y_2878_);
v_env_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc_ref(v_env_2930_);
lean_dec(v___x_2929_);
v___x_2931_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2930_, v_decl_2874_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2873_);
v___y_2888_ = v_env_2930_;
v___y_2889_ = v___y_2877_;
v___y_2890_ = v___y_2878_;
goto v___jp_2887_;
}
else
{
lean_object* v_name_2932_; lean_object* v___x_2933_; 
lean_dec_ref_known(v___x_2931_, 1);
lean_dec_ref(v_env_2930_);
lean_dec(v_stx_2875_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
lean_dec_ref(v_getParam_2870_);
v_name_2932_ = lean_ctor_get(v_toAttributeImplCore_2873_, 1);
lean_inc(v_name_2932_);
lean_dec_ref(v_toAttributeImplCore_2873_);
v___x_2933_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2932_, v_decl_2874_, v___y_2877_, v___y_2878_);
return v___x_2933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2938_, lean_object* v_ext_2939_, lean_object* v_afterSet_2940_, lean_object* v_toAttributeImplCore_2941_, lean_object* v_decl_2942_, lean_object* v_stx_2943_, lean_object* v_kind_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
uint8_t v_kind_boxed_2948_; lean_object* v_res_2949_; 
v_kind_boxed_2948_ = lean_unbox(v_kind_2944_);
v_res_2949_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2938_, v_ext_2939_, v_afterSet_2940_, v_toAttributeImplCore_2941_, v_decl_2942_, v_stx_2943_, v_kind_boxed_2948_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2950_, lean_object* v_decl_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_name_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_name_2955_ = lean_ctor_get(v_toAttributeImplCore_2950_, 1);
lean_inc(v_name_2955_);
lean_dec_ref(v_toAttributeImplCore_2950_);
v___x_2956_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2957_ = l_Lean_MessageData_ofName(v_name_2955_);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
v___x_2959_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2960_, v___y_2952_, v___y_2953_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2962_, lean_object* v_decl_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2962_, v_decl_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v_decl_2963_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2968_, lean_object* v_ext_2969_){
_start:
{
lean_object* v_toAttributeImplCore_2971_; lean_object* v_getParam_2972_; lean_object* v_afterSet_2973_; uint8_t v_preserveOrder_2974_; lean_object* v___f_2975_; lean_object* v___f_2976_; lean_object* v_attrImpl_2977_; lean_object* v___x_2978_; 
v_toAttributeImplCore_2971_ = lean_ctor_get(v_impl_2968_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2971_, 3);
v_getParam_2972_ = lean_ctor_get(v_impl_2968_, 1);
lean_inc_ref(v_getParam_2972_);
v_afterSet_2973_ = lean_ctor_get(v_impl_2968_, 2);
lean_inc_ref(v_afterSet_2973_);
v_preserveOrder_2974_ = lean_ctor_get_uint8(v_impl_2968_, sizeof(void*)*4);
lean_dec_ref(v_impl_2968_);
lean_inc_ref(v_ext_2969_);
v___f_2975_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2975_, 0, v_getParam_2972_);
lean_closure_set(v___f_2975_, 1, v_ext_2969_);
lean_closure_set(v___f_2975_, 2, v_afterSet_2973_);
lean_closure_set(v___f_2975_, 3, v_toAttributeImplCore_2971_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2976_, 0, v_toAttributeImplCore_2971_);
v_attrImpl_2977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2977_, 0, v_toAttributeImplCore_2971_);
lean_ctor_set(v_attrImpl_2977_, 1, v___f_2975_);
lean_ctor_set(v_attrImpl_2977_, 2, v___f_2976_);
lean_inc_ref(v_attrImpl_2977_);
v___x_2978_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2977_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2986_; 
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2978_, 0);
lean_dec(v_unused_2987_);
v___x_2980_ = v___x_2978_;
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
else
{
lean_dec(v___x_2978_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2986_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2982_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2982_, 0, v_attrImpl_2977_);
lean_ctor_set(v___x_2982_, 1, v_ext_2969_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*2, v_preserveOrder_2974_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2982_);
v___x_2984_ = v___x_2980_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref_known(v_attrImpl_2977_, 3);
lean_dec_ref(v_ext_2969_);
v_a_2988_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2978_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2978_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2996_, lean_object* v_ext_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2996_, v_ext_2997_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3000_, lean_object* v_impl_3001_, lean_object* v_ext_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3001_, v_ext_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3005_, lean_object* v_impl_3006_, lean_object* v_ext_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3005_, v_impl_3006_, v_ext_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3010_){
_start:
{
lean_object* v_toAttributeImplCore_3012_; uint8_t v_preserveOrder_3013_; lean_object* v_filterExport_3014_; lean_object* v_ref_3015_; lean_object* v___x_3016_; 
v_toAttributeImplCore_3012_ = lean_ctor_get(v_impl_3010_, 0);
v_preserveOrder_3013_ = lean_ctor_get_uint8(v_impl_3010_, sizeof(void*)*4);
v_filterExport_3014_ = lean_ctor_get(v_impl_3010_, 3);
v_ref_3015_ = lean_ctor_get(v_toAttributeImplCore_3012_, 0);
lean_inc_ref(v_filterExport_3014_);
lean_inc(v_ref_3015_);
v___x_3016_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3015_, v_preserveOrder_3013_, v_filterExport_3014_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3010_, v_a_3017_);
return v___x_3018_;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v_impl_3010_);
v_a_3019_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3016_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3016_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_registerParametricAttribute___redArg(v_impl_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3030_, lean_object* v_impl_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_registerParametricAttribute___redArg(v_impl_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3034_, lean_object* v_impl_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_registerParametricAttribute(v_00_u03b1_3034_, v_impl_3035_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3038_, lean_object* v___x_3039_, lean_object* v___x_3040_, lean_object* v_a_3041_, lean_object* v_x_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_fst_3044_; uint8_t v___x_3045_; 
v_fst_3044_ = lean_ctor_get(v_a_3041_, 0);
v___x_3045_ = lean_name_eq(v_fst_3044_, v_decl_3038_);
if (v___x_3045_ == 0)
{
lean_object* v___x_3046_; 
lean_dec_ref(v_a_3041_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3039_);
return v___x_3046_;
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref(v___x_3039_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3041_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v___x_3040_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3051_, lean_object* v___x_3052_, lean_object* v___x_3053_, lean_object* v_a_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3051_, v___x_3052_, v___x_3053_, v_a_3054_, v_x_3055_, v___y_3056_);
lean_dec_ref(v___y_3056_);
lean_dec(v_decl_3051_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3085_, lean_object* v_ext_3086_, uint8_t v_preserveOrder_3087_, lean_object* v_env_3088_, lean_object* v_decl_3089_){
_start:
{
lean_object* v___y_3091_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3103_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3088_, v_decl_3089_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_toEnvExtension_3104_; lean_object* v_asyncMode_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_snd_3108_; lean_object* v___x_3109_; 
lean_dec(v_inst_3085_);
v_toEnvExtension_3104_ = lean_ctor_get(v_ext_3086_, 0);
v_asyncMode_3105_ = lean_ctor_get(v_toEnvExtension_3104_, 2);
v___x_3106_ = lean_box(0);
v___x_3107_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3102_, v_ext_3086_, v_env_3088_, v_asyncMode_3105_, v___x_3106_);
v_snd_3108_ = lean_ctor_get(v___x_3107_, 1);
lean_inc(v_snd_3108_);
lean_dec(v___x_3107_);
v___x_3109_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3108_, v_decl_3089_);
lean_dec(v_decl_3089_);
lean_dec(v_snd_3108_);
return v___x_3109_;
}
else
{
if (v_preserveOrder_3087_ == 0)
{
lean_object* v_val_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_val_3110_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3110_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3111_ = 0;
v___x_3112_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3102_, v_ext_3086_, v_env_3088_, v_val_3110_, v___x_3111_);
lean_dec(v_val_3110_);
lean_dec_ref(v_env_3088_);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_array_get_size(v___x_3112_);
v___x_3115_ = lean_nat_dec_lt(v___x_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
lean_dec_ref(v___x_3112_);
lean_dec(v_decl_3089_);
lean_dec(v_inst_3085_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_nat_sub(v___x_3114_, v___x_3117_);
v___x_3119_ = lean_nat_dec_le(v___x_3113_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; 
lean_dec(v___x_3118_);
lean_dec_ref(v___x_3112_);
lean_dec(v_decl_3089_);
lean_dec(v_inst_3085_);
v___x_3120_ = lean_box(0);
return v___x_3120_;
}
else
{
lean_object* v___f_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___f_3121_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_decl_3089_);
lean_ctor_set(v___x_3122_, 1, v_inst_3085_);
v___x_3123_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3124_ = l_Array_binSearchAux___redArg(v___f_3121_, v___x_3123_, v___x_3112_, v___x_3122_, v___x_3113_, v___x_3118_);
lean_dec_ref(v___x_3112_);
v___y_3091_ = v___x_3124_;
goto v___jp_3090_;
}
}
}
else
{
lean_object* v_val_3125_; uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___f_3132_; size_t v_sz_3133_; size_t v___x_3134_; lean_object* v___x_3135_; lean_object* v_fst_3136_; 
lean_dec(v_inst_3085_);
v_val_3125_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3125_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3126_ = 0;
v___x_3127_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3102_, v_ext_3086_, v_env_3088_, v_val_3125_, v___x_3126_);
lean_dec(v_val_3125_);
lean_dec_ref(v_env_3088_);
v___x_3128_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3129_ = lean_box(0);
v___x_3130_ = lean_box(0);
v___x_3131_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3132_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3132_, 0, v_decl_3089_);
lean_closure_set(v___f_3132_, 1, v___x_3131_);
lean_closure_set(v___f_3132_, 2, v___x_3130_);
v_sz_3133_ = lean_array_size(v___x_3127_);
v___x_3134_ = ((size_t)0ULL);
v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3128_, v___x_3127_, v___f_3132_, v_sz_3133_, v___x_3134_, v___x_3131_);
v_fst_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_fst_3136_);
lean_dec(v___x_3135_);
if (lean_obj_tag(v_fst_3136_) == 0)
{
return v___x_3129_;
}
else
{
lean_object* v_val_3137_; 
v_val_3137_ = lean_ctor_get(v_fst_3136_, 0);
lean_inc(v_val_3137_);
lean_dec_ref_known(v_fst_3136_, 1);
v___y_3091_ = v_val_3137_;
goto v___jp_3090_;
}
}
}
v___jp_3090_:
{
if (lean_obj_tag(v___y_3091_) == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = lean_box(0);
return v___x_3092_;
}
else
{
lean_object* v_val_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
v_val_3093_ = lean_ctor_get(v___y_3091_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___y_3091_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3095_ = v___y_3091_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_val_3093_);
lean_dec(v___y_3091_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v_snd_3097_; lean_object* v___x_3099_; 
v_snd_3097_ = lean_ctor_get(v_val_3093_, 1);
lean_inc(v_snd_3097_);
lean_dec(v_val_3093_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v_snd_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_snd_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3138_, lean_object* v_ext_3139_, lean_object* v_preserveOrder_3140_, lean_object* v_env_3141_, lean_object* v_decl_3142_){
_start:
{
uint8_t v_preserveOrder_boxed_3143_; lean_object* v_res_3144_; 
v_preserveOrder_boxed_3143_ = lean_unbox(v_preserveOrder_3140_);
v_res_3144_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3138_, v_ext_3139_, v_preserveOrder_boxed_3143_, v_env_3141_, v_decl_3142_);
lean_dec_ref(v_ext_3139_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3145_, lean_object* v_inst_3146_, lean_object* v_ext_3147_, uint8_t v_preserveOrder_3148_, lean_object* v_env_3149_, lean_object* v_decl_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3146_, v_ext_3147_, v_preserveOrder_3148_, v_env_3149_, v_decl_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3152_, lean_object* v_inst_3153_, lean_object* v_ext_3154_, lean_object* v_preserveOrder_3155_, lean_object* v_env_3156_, lean_object* v_decl_3157_){
_start:
{
uint8_t v_preserveOrder_boxed_3158_; lean_object* v_res_3159_; 
v_preserveOrder_boxed_3158_ = lean_unbox(v_preserveOrder_3155_);
v_res_3159_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3152_, v_inst_3153_, v_ext_3154_, v_preserveOrder_boxed_3158_, v_env_3156_, v_decl_3157_);
lean_dec_ref(v_ext_3154_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3160_, lean_object* v_attr_3161_, lean_object* v_env_3162_, lean_object* v_decl_3163_){
_start:
{
lean_object* v_ext_3164_; uint8_t v_preserveOrder_3165_; lean_object* v___x_3166_; 
v_ext_3164_ = lean_ctor_get(v_attr_3161_, 1);
v_preserveOrder_3165_ = lean_ctor_get_uint8(v_attr_3161_, sizeof(void*)*2);
v___x_3166_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3160_, v_ext_3164_, v_preserveOrder_3165_, v_env_3162_, v_decl_3163_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3167_, lean_object* v_attr_3168_, lean_object* v_env_3169_, lean_object* v_decl_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3167_, v_attr_3168_, v_env_3169_, v_decl_3170_);
lean_dec_ref(v_attr_3168_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3172_, lean_object* v_inst_3173_, lean_object* v_attr_3174_, lean_object* v_env_3175_, lean_object* v_decl_3176_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3173_, v_attr_3174_, v_env_3175_, v_decl_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_inst_3179_, lean_object* v_attr_3180_, lean_object* v_env_3181_, lean_object* v_decl_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3178_, v_inst_3179_, v_attr_3180_, v_env_3181_, v_decl_3182_);
lean_dec_ref(v_attr_3180_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3188_, lean_object* v_attr_3189_, lean_object* v_env_3190_, lean_object* v_decl_3191_, lean_object* v_param_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3190_, v_decl_3191_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_toEnvExtension_3194_; lean_object* v_asyncMode_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_snd_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3229_; 
v_toEnvExtension_3194_ = lean_ctor_get(v_ext_3188_, 0);
v_asyncMode_3195_ = lean_ctor_get(v_toEnvExtension_3194_, 2);
lean_inc(v_asyncMode_3195_);
v___x_3196_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3197_ = lean_box(0);
lean_inc_ref(v_env_3190_);
v___x_3198_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3196_, v_ext_3188_, v_env_3190_, v_asyncMode_3195_, v___x_3197_);
v_snd_3199_ = lean_ctor_get(v___x_3198_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3198_, 0);
lean_dec(v_unused_3230_);
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3229_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snd_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3229_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3199_, v_decl_3191_);
lean_dec(v_snd_3199_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3205_; 
lean_dec_ref(v_attr_3189_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v_param_3192_);
lean_ctor_set(v___x_3201_, 0, v_decl_3191_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_decl_3191_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_param_3192_);
v___x_3205_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3188_, v_env_3190_, v___x_3205_, v_asyncMode_3195_, v___x_3197_);
lean_dec(v_asyncMode_3195_);
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
else
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3227_; 
lean_del_object(v___x_3201_);
lean_dec(v_asyncMode_3195_);
lean_dec(v_param_3192_);
lean_dec_ref(v_env_3190_);
lean_dec_ref(v_ext_3188_);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3203_, 0);
lean_dec(v_unused_3228_);
v___x_3210_ = v___x_3203_;
v_isShared_3211_ = v_isSharedCheck_3227_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v___x_3203_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3227_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_toAttributeImplCore_3212_; lean_object* v_name_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v_toAttributeImplCore_3212_ = lean_ctor_get(v_attr_3189_, 0);
lean_inc_ref(v_toAttributeImplCore_3212_);
lean_dec_ref(v_attr_3189_);
v_name_3213_ = lean_ctor_get(v_toAttributeImplCore_3212_, 1);
lean_inc(v_name_3213_);
lean_dec_ref(v_toAttributeImplCore_3212_);
v___x_3214_ = 1;
v___x_3215_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3216_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3213_, v___x_3214_);
v___x_3217_ = lean_string_append(v___x_3215_, v___x_3216_);
lean_dec_ref(v___x_3216_);
v___x_3218_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3219_ = lean_string_append(v___x_3217_, v___x_3218_);
v___x_3220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3191_, v___x_3214_);
v___x_3221_ = lean_string_append(v___x_3219_, v___x_3220_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3223_ = lean_string_append(v___x_3221_, v___x_3222_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3223_);
v___x_3225_ = v___x_3210_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
else
{
lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_param_3192_);
lean_dec_ref(v_env_3190_);
lean_dec_ref(v_ext_3188_);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3193_, 0);
lean_dec(v_unused_3250_);
v___x_3232_ = v___x_3193_;
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
else
{
lean_dec(v___x_3193_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3249_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v_toAttributeImplCore_3234_; lean_object* v_name_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v_toAttributeImplCore_3234_ = lean_ctor_get(v_attr_3189_, 0);
lean_inc_ref(v_toAttributeImplCore_3234_);
lean_dec_ref(v_attr_3189_);
v_name_3235_ = lean_ctor_get(v_toAttributeImplCore_3234_, 1);
lean_inc(v_name_3235_);
lean_dec_ref(v_toAttributeImplCore_3234_);
v___x_3236_ = 1;
v___x_3237_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3235_, v___x_3236_);
v___x_3239_ = lean_string_append(v___x_3237_, v___x_3238_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3241_ = lean_string_append(v___x_3239_, v___x_3240_);
v___x_3242_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3191_, v___x_3236_);
v___x_3243_ = lean_string_append(v___x_3241_, v___x_3242_);
lean_dec_ref(v___x_3242_);
v___x_3244_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3245_ = lean_string_append(v___x_3243_, v___x_3244_);
if (v_isShared_3233_ == 0)
{
lean_ctor_set_tag(v___x_3232_, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3245_);
v___x_3247_ = v___x_3232_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3251_, lean_object* v_ext_3252_, lean_object* v_attr_3253_, lean_object* v_env_3254_, lean_object* v_decl_3255_, lean_object* v_param_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3252_, v_attr_3253_, v_env_3254_, v_decl_3255_, v_param_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3258_, lean_object* v_env_3259_, lean_object* v_decl_3260_, lean_object* v_param_3261_){
_start:
{
lean_object* v_attr_3262_; lean_object* v_ext_3263_; lean_object* v___x_3264_; 
v_attr_3262_ = lean_ctor_get(v_attr_3258_, 0);
lean_inc_ref(v_attr_3262_);
v_ext_3263_ = lean_ctor_get(v_attr_3258_, 1);
lean_inc_ref(v_ext_3263_);
lean_dec_ref(v_attr_3258_);
v___x_3264_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3263_, v_attr_3262_, v_env_3259_, v_decl_3260_, v_param_3261_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3265_, lean_object* v_attr_3266_, lean_object* v_env_3267_, lean_object* v_decl_3268_, lean_object* v_param_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3266_, v_env_3267_, v_decl_3268_, v_param_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3276_, v___y_3277_);
lean_dec_ref(v___y_3277_);
lean_dec_ref(v_x_3276_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3280_, lean_object* v_x_3281_){
_start:
{
lean_inc(v_s_3280_);
return v_s_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3282_, v_x_3283_);
lean_dec_ref(v_x_3283_);
lean_dec(v_s_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3288_, v_x_3289_);
lean_dec(v_x_3289_);
lean_dec_ref(v_x_3288_);
return v_res_3290_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___f_3295_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3296_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3301_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
lean_ctor_set(v___x_3301_, 2, v___f_3298_);
lean_ctor_set(v___x_3301_, 3, v___f_3297_);
lean_ctor_set(v___x_3301_, 4, v___f_3296_);
lean_ctor_set(v___x_3301_, 5, v___f_3295_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3306_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3309_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3313_);
lean_dec(v_x_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
if (lean_obj_tag(v_x_3317_) == 0)
{
return v_x_3316_;
}
else
{
lean_object* v_head_3318_; lean_object* v_tail_3319_; lean_object* v___x_3320_; 
v_head_3318_ = lean_ctor_get(v_x_3317_, 0);
lean_inc(v_head_3318_);
v_tail_3319_ = lean_ctor_get(v_x_3317_, 1);
lean_inc(v_tail_3319_);
lean_dec_ref_known(v_x_3317_, 2);
v___x_3320_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3315_, v_head_3318_);
if (lean_obj_tag(v___x_3320_) == 1)
{
lean_object* v_val_3321_; lean_object* v___x_3322_; 
v_val_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_val_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3318_, v_val_3321_, v_x_3316_);
v_x_3316_ = v___x_3322_;
v_x_3317_ = v_tail_3319_;
goto _start;
}
else
{
lean_dec(v___x_3320_);
lean_dec(v_head_3318_);
v_x_3317_ = v_tail_3319_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3325_, v_x_3326_, v_x_3327_);
lean_dec(v_newState_3325_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3329_, lean_object* v_newState_3330_, lean_object* v_consts_3331_, lean_object* v_st_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3330_, v_st_3332_, v_consts_3331_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3334_, lean_object* v_newState_3335_, lean_object* v_consts_3336_, lean_object* v_st_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3334_, v_newState_3335_, v_consts_3336_, v_st_3337_);
lean_dec(v_newState_3335_);
lean_dec(v_x_3334_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3348_){
_start:
{
lean_object* v___x_3349_; lean_object* v___y_3351_; 
v___x_3349_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3348_) == 0)
{
lean_object* v_size_3355_; 
v_size_3355_ = lean_ctor_get(v_s_3348_, 0);
lean_inc(v_size_3355_);
lean_dec_ref_known(v_s_3348_, 5);
v___y_3351_ = v_size_3355_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___y_3351_ = v___x_3356_;
goto v___jp_3350_;
}
v___jp_3350_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = l_Nat_reprFast(v___y_3351_);
v___x_3353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3349_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3357_, lean_object* v_as_3358_, size_t v_i_3359_, size_t v_stop_3360_, lean_object* v_b_3361_){
_start:
{
lean_object* v___y_3363_; uint8_t v___x_3367_; 
v___x_3367_ = lean_usize_dec_eq(v_i_3359_, v_stop_3360_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; lean_object* v_fst_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3368_ = lean_array_uget_borrowed(v_as_3358_, v_i_3359_);
v_fst_3369_ = lean_ctor_get(v___x_3368_, 0);
v___x_3370_ = 1;
lean_inc_ref(v_env_3357_);
v___x_3371_ = l_Lean_Environment_setExporting(v_env_3357_, v___x_3370_);
lean_inc(v_fst_3369_);
v___x_3372_ = l_Lean_Environment_contains(v___x_3371_, v_fst_3369_, v___x_3367_);
if (v___x_3372_ == 0)
{
v___y_3363_ = v_b_3361_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3373_; 
lean_inc(v___x_3368_);
v___x_3373_ = lean_array_push(v_b_3361_, v___x_3368_);
v___y_3363_ = v___x_3373_;
goto v___jp_3362_;
}
}
else
{
lean_dec_ref(v_env_3357_);
return v_b_3361_;
}
v___jp_3362_:
{
size_t v___x_3364_; size_t v___x_3365_; 
v___x_3364_ = ((size_t)1ULL);
v___x_3365_ = lean_usize_add(v_i_3359_, v___x_3364_);
v_i_3359_ = v___x_3365_;
v_b_3361_ = v___y_3363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3374_, lean_object* v_as_3375_, lean_object* v_i_3376_, lean_object* v_stop_3377_, lean_object* v_b_3378_){
_start:
{
size_t v_i_boxed_3379_; size_t v_stop_boxed_3380_; lean_object* v_res_3381_; 
v_i_boxed_3379_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_stop_boxed_3380_ = lean_unbox_usize(v_stop_3377_);
lean_dec(v_stop_3377_);
v_res_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3374_, v_as_3375_, v_i_boxed_3379_, v_stop_boxed_3380_, v_b_3378_);
lean_dec_ref(v_as_3375_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3382_, lean_object* v_m_3383_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___y_3387_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___x_3407_; 
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3401_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3385_, v_m_3383_);
v___x_3402_ = lean_array_get_size(v___x_3401_);
v___x_3407_ = lean_nat_dec_eq(v___x_3402_, v___x_3384_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___y_3411_; uint8_t v___x_3413_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_sub(v___x_3402_, v___x_3408_);
v___x_3413_ = lean_nat_dec_le(v___x_3384_, v___x_3409_);
if (v___x_3413_ == 0)
{
lean_inc(v___x_3409_);
v___y_3411_ = v___x_3409_;
goto v___jp_3410_;
}
else
{
v___y_3411_ = v___x_3384_;
goto v___jp_3410_;
}
v___jp_3410_:
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_nat_dec_le(v___y_3411_, v___x_3409_);
if (v___x_3412_ == 0)
{
lean_dec(v___x_3409_);
lean_inc(v___y_3411_);
v___y_3404_ = v___y_3411_;
v___y_3405_ = v___y_3411_;
goto v___jp_3403_;
}
else
{
v___y_3404_ = v___y_3411_;
v___y_3405_ = v___x_3409_;
goto v___jp_3403_;
}
}
}
else
{
v___y_3387_ = v___x_3401_;
goto v___jp_3386_;
}
v___jp_3386_:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = lean_array_get_size(v___y_3387_);
v___x_3389_ = lean_nat_dec_lt(v___x_3384_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref(v_env_3382_);
v___x_3390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3385_);
lean_ctor_set(v___x_3390_, 1, v___x_3385_);
lean_ctor_set(v___x_3390_, 2, v___y_3387_);
return v___x_3390_;
}
else
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_nat_dec_le(v___x_3388_, v___x_3388_);
if (v___x_3391_ == 0)
{
if (v___x_3389_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v_env_3382_);
v___x_3392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3385_);
lean_ctor_set(v___x_3392_, 1, v___x_3385_);
lean_ctor_set(v___x_3392_, 2, v___y_3387_);
return v___x_3392_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = lean_usize_of_nat(v___x_3388_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3382_, v___y_3387_, v___x_3393_, v___x_3394_, v___x_3385_);
lean_inc_ref(v___x_3395_);
v___x_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
lean_ctor_set(v___x_3396_, 2, v___y_3387_);
return v___x_3396_;
}
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3388_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3382_, v___y_3387_, v___x_3397_, v___x_3398_, v___x_3385_);
lean_inc_ref(v___x_3399_);
v___x_3400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
lean_ctor_set(v___x_3400_, 2, v___y_3387_);
return v___x_3400_;
}
}
}
v___jp_3403_:
{
lean_object* v___x_3406_; 
v___x_3406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3402_, v___x_3401_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
v___y_3387_ = v___x_3406_;
goto v___jp_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3414_, lean_object* v_m_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3414_, v_m_3415_);
lean_dec(v_m_3415_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3417_, lean_object* v_p_3418_){
_start:
{
lean_object* v_fst_3419_; lean_object* v_snd_3420_; lean_object* v___x_3421_; 
v_fst_3419_ = lean_ctor_get(v_p_3418_, 0);
lean_inc(v_fst_3419_);
v_snd_3420_ = lean_ctor_get(v_p_3418_, 1);
lean_inc(v_snd_3420_);
lean_dec_ref(v_p_3418_);
v___x_3421_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3419_, v_snd_3420_, v_s_3417_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3422_, lean_object* v_x_3423_, lean_object* v_x_3424_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3422_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3427_, lean_object* v_x_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3427_, v_x_3428_, v_x_3429_);
lean_dec_ref(v_x_3429_);
lean_dec_ref(v_x_3428_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3432_){
_start:
{
if (lean_obj_tag(v_as_3432_) == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
else
{
lean_object* v_head_3436_; lean_object* v_tail_3437_; lean_object* v___x_3438_; 
v_head_3436_ = lean_ctor_get(v_as_3432_, 0);
lean_inc(v_head_3436_);
v_tail_3437_ = lean_ctor_get(v_as_3432_, 1);
lean_inc(v_tail_3437_);
lean_dec_ref_known(v_as_3432_, 2);
v___x_3438_ = l_Lean_registerBuiltinAttribute(v_head_3436_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_dec_ref_known(v___x_3438_, 1);
v_as_3432_ = v_tail_3437_;
goto _start;
}
else
{
lean_dec(v_tail_3437_);
return v___x_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3443_, lean_object* v_snd_3444_, lean_object* v_a_3445_, lean_object* v_fst_3446_, lean_object* v_decl_3447_, lean_object* v_stx_3448_, uint8_t v_kind_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3448_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3496_) == 0)
{
uint8_t v___x_3497_; uint8_t v___x_3498_; 
lean_dec_ref_known(v___x_3496_, 1);
v___x_3497_ = 0;
v___x_3498_ = l_Lean_instBEqAttributeKind_beq(v_kind_3449_, v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec(v_decl_3447_);
lean_dec_ref(v_a_3445_);
lean_dec(v_snd_3444_);
lean_dec_ref(v_validate_3443_);
v___x_3499_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3446_, v_kind_3449_, v___y_3450_, v___y_3451_);
return v___x_3499_;
}
else
{
v___y_3490_ = v___y_3450_;
v___y_3491_ = v___y_3451_;
goto v___jp_3489_;
}
}
else
{
lean_dec(v_decl_3447_);
lean_dec(v_fst_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_snd_3444_);
lean_dec_ref(v_validate_3443_);
return v___x_3496_;
}
v___jp_3453_:
{
lean_object* v___x_3456_; 
lean_inc(v___y_3455_);
lean_inc_ref(v___y_3454_);
lean_inc(v_snd_3444_);
lean_inc(v_decl_3447_);
v___x_3456_ = lean_apply_5(v_validate_3443_, v_decl_3447_, v_snd_3444_, v___y_3454_, v___y_3455_, lean_box(0));
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3487_; 
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3488_);
v___x_3458_ = v___x_3456_;
v_isShared_3459_ = v_isSharedCheck_3487_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v___x_3456_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3487_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_toEnvExtension_3461_; lean_object* v_env_3462_; lean_object* v_nextMacroScope_3463_; lean_object* v_ngen_3464_; lean_object* v_auxDeclNGen_3465_; lean_object* v_traceState_3466_; lean_object* v_messages_3467_; lean_object* v_infoState_3468_; lean_object* v_snapshotTasks_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3485_; 
v___x_3460_ = lean_st_ref_take(v___y_3455_);
v_toEnvExtension_3461_ = lean_ctor_get(v_a_3445_, 0);
v_env_3462_ = lean_ctor_get(v___x_3460_, 0);
v_nextMacroScope_3463_ = lean_ctor_get(v___x_3460_, 1);
v_ngen_3464_ = lean_ctor_get(v___x_3460_, 2);
v_auxDeclNGen_3465_ = lean_ctor_get(v___x_3460_, 3);
v_traceState_3466_ = lean_ctor_get(v___x_3460_, 4);
v_messages_3467_ = lean_ctor_get(v___x_3460_, 6);
v_infoState_3468_ = lean_ctor_get(v___x_3460_, 7);
v_snapshotTasks_3469_ = lean_ctor_get(v___x_3460_, 8);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; 
v_unused_3486_ = lean_ctor_get(v___x_3460_, 5);
lean_dec(v_unused_3486_);
v___x_3471_ = v___x_3460_;
v_isShared_3472_ = v_isSharedCheck_3485_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_snapshotTasks_3469_);
lean_inc(v_infoState_3468_);
lean_inc(v_messages_3467_);
lean_inc(v_traceState_3466_);
lean_inc(v_auxDeclNGen_3465_);
lean_inc(v_ngen_3464_);
lean_inc(v_nextMacroScope_3463_);
lean_inc(v_env_3462_);
lean_dec(v___x_3460_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3485_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_asyncMode_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v_asyncMode_3473_ = lean_ctor_get(v_toEnvExtension_3461_, 2);
lean_inc(v_asyncMode_3473_);
lean_inc(v_decl_3447_);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v_decl_3447_);
lean_ctor_set(v___x_3474_, 1, v_snd_3444_);
v___x_3475_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3445_, v_env_3462_, v___x_3474_, v_asyncMode_3473_, v_decl_3447_);
lean_dec(v_asyncMode_3473_);
v___x_3476_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 5, v___x_3476_);
lean_ctor_set(v___x_3471_, 0, v___x_3475_);
v___x_3478_ = v___x_3471_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_nextMacroScope_3463_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_ngen_3464_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_auxDeclNGen_3465_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_traceState_3466_);
lean_ctor_set(v_reuseFailAlloc_3484_, 5, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3484_, 6, v_messages_3467_);
lean_ctor_set(v_reuseFailAlloc_3484_, 7, v_infoState_3468_);
lean_ctor_set(v_reuseFailAlloc_3484_, 8, v_snapshotTasks_3469_);
v___x_3478_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3479_ = lean_st_ref_put(v___y_3455_, v___x_3478_);
v___x_3480_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3480_);
v___x_3482_ = v___x_3458_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_dec(v_decl_3447_);
lean_dec_ref(v_a_3445_);
lean_dec(v_snd_3444_);
return v___x_3456_;
}
}
v___jp_3489_:
{
lean_object* v___x_3492_; lean_object* v_env_3493_; lean_object* v___x_3494_; 
v___x_3492_ = lean_st_ref_get(v___y_3491_);
v_env_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc_ref(v_env_3493_);
lean_dec(v___x_3492_);
v___x_3494_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3493_, v_decl_3447_);
lean_dec_ref(v_env_3493_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec(v_fst_3446_);
v___y_3454_ = v___y_3490_;
v___y_3455_ = v___y_3491_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3495_; 
lean_dec_ref_known(v___x_3494_, 1);
lean_dec_ref(v_a_3445_);
lean_dec(v_snd_3444_);
lean_dec_ref(v_validate_3443_);
v___x_3495_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3446_, v_decl_3447_, v___y_3490_, v___y_3491_);
return v___x_3495_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3500_, lean_object* v_snd_3501_, lean_object* v_a_3502_, lean_object* v_fst_3503_, lean_object* v_decl_3504_, lean_object* v_stx_3505_, lean_object* v_kind_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
uint8_t v_kind_boxed_3510_; lean_object* v_res_3511_; 
v_kind_boxed_3510_ = lean_unbox(v_kind_3506_);
v_res_3511_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3500_, v_snd_3501_, v_a_3502_, v_fst_3503_, v_decl_3504_, v_stx_3505_, v_kind_boxed_3510_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3512_, lean_object* v_decl_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3517_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3518_ = l_Lean_MessageData_ofName(v_fst_3512_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3521_, v___y_3514_, v___y_3515_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3523_, lean_object* v_decl_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3523_, v_decl_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v_decl_3524_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3529_, lean_object* v_a_3530_, lean_object* v_ref_3531_, uint8_t v_applicationTime_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
if (lean_obj_tag(v_a_3533_) == 0)
{
lean_object* v___x_3535_; 
lean_dec(v_ref_3531_);
lean_dec_ref(v_a_3530_);
lean_dec_ref(v_validate_3529_);
v___x_3535_ = l_List_reverse___redArg(v_a_3534_);
return v___x_3535_;
}
else
{
lean_object* v_head_3536_; lean_object* v_snd_3537_; lean_object* v_tail_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3553_; 
v_head_3536_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_head_3536_);
v_snd_3537_ = lean_ctor_get(v_head_3536_, 1);
lean_inc(v_snd_3537_);
v_tail_3538_ = lean_ctor_get(v_a_3533_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3533_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v_a_3533_, 0);
lean_dec(v_unused_3554_);
v___x_3540_ = v_a_3533_;
v_isShared_3541_ = v_isSharedCheck_3553_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_tail_3538_);
lean_dec(v_a_3533_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3553_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v_fst_3542_; lean_object* v_fst_3543_; lean_object* v_snd_3544_; lean_object* v___f_3545_; lean_object* v___f_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v_fst_3542_ = lean_ctor_get(v_head_3536_, 0);
lean_inc_n(v_fst_3542_, 3);
lean_dec(v_head_3536_);
v_fst_3543_ = lean_ctor_get(v_snd_3537_, 0);
lean_inc(v_fst_3543_);
v_snd_3544_ = lean_ctor_get(v_snd_3537_, 1);
lean_inc(v_snd_3544_);
lean_dec(v_snd_3537_);
v___f_3545_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3545_, 0, v_fst_3542_);
lean_inc_ref(v_a_3530_);
lean_inc_ref(v_validate_3529_);
v___f_3546_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3546_, 0, v_validate_3529_);
lean_closure_set(v___f_3546_, 1, v_snd_3544_);
lean_closure_set(v___f_3546_, 2, v_a_3530_);
lean_closure_set(v___f_3546_, 3, v_fst_3542_);
lean_inc(v_ref_3531_);
v___x_3547_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3547_, 0, v_ref_3531_);
lean_ctor_set(v___x_3547_, 1, v_fst_3542_);
lean_ctor_set(v___x_3547_, 2, v_fst_3543_);
lean_ctor_set_uint8(v___x_3547_, sizeof(void*)*3, v_applicationTime_3532_);
v___x_3548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
lean_ctor_set(v___x_3548_, 1, v___f_3546_);
lean_ctor_set(v___x_3548_, 2, v___f_3545_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 1, v_a_3534_);
lean_ctor_set(v___x_3540_, 0, v___x_3548_);
v___x_3550_ = v___x_3540_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3534_);
v___x_3550_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
v_a_3533_ = v_tail_3538_;
v_a_3534_ = v___x_3550_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3555_, lean_object* v_a_3556_, lean_object* v_ref_3557_, lean_object* v_applicationTime_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
uint8_t v_applicationTime_boxed_3561_; lean_object* v_res_3562_; 
v_applicationTime_boxed_3561_ = lean_unbox(v_applicationTime_3558_);
v_res_3562_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3555_, v_a_3556_, v_ref_3557_, v_applicationTime_boxed_3561_, v_a_3559_, v_a_3560_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3576_, lean_object* v_validate_3577_, uint8_t v_applicationTime_3578_, lean_object* v_ref_3579_){
_start:
{
lean_object* v___f_3581_; lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___f_3581_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3582_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3583_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3584_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3585_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3586_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3587_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3579_);
v___x_3589_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3589_, 0, v_ref_3579_);
lean_ctor_set(v___x_3589_, 1, v___f_3585_);
lean_ctor_set(v___x_3589_, 2, v___f_3586_);
lean_ctor_set(v___x_3589_, 3, v___f_3584_);
lean_ctor_set(v___x_3589_, 4, v___f_3583_);
lean_ctor_set(v___x_3589_, 5, v___f_3582_);
lean_ctor_set(v___x_3589_, 6, v___x_3587_);
lean_ctor_set(v___x_3589_, 7, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v___f_3581_);
v___x_3591_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3590_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc_n(v_a_3592_, 2);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = lean_box(0);
v___x_3594_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3577_, v_a_3592_, v_ref_3579_, v_applicationTime_3578_, v_attrDescrs_3576_, v___x_3593_);
lean_inc(v___x_3594_);
v___x_3595_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3594_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3595_, 0);
lean_dec(v_unused_3604_);
v___x_3597_ = v___x_3595_;
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v___x_3595_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3603_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3594_);
lean_ctor_set(v___x_3599_, 1, v_a_3592_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3599_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec(v___x_3594_);
lean_dec(v_a_3592_);
v_a_3605_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3595_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3595_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3605_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec(v_ref_3579_);
lean_dec_ref(v_validate_3577_);
lean_dec(v_attrDescrs_3576_);
v_a_3613_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3591_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3591_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3621_, lean_object* v_validate_3622_, lean_object* v_applicationTime_3623_, lean_object* v_ref_3624_, lean_object* v_a_3625_){
_start:
{
uint8_t v_applicationTime_boxed_3626_; lean_object* v_res_3627_; 
v_applicationTime_boxed_3626_ = lean_unbox(v_applicationTime_3623_);
v_res_3627_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3621_, v_validate_3622_, v_applicationTime_boxed_3626_, v_ref_3624_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3628_, lean_object* v_attrDescrs_3629_, lean_object* v_validate_3630_, uint8_t v_applicationTime_3631_, lean_object* v_ref_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3629_, v_validate_3630_, v_applicationTime_3631_, v_ref_3632_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3635_, lean_object* v_attrDescrs_3636_, lean_object* v_validate_3637_, lean_object* v_applicationTime_3638_, lean_object* v_ref_3639_, lean_object* v_a_3640_){
_start:
{
uint8_t v_applicationTime_boxed_3641_; lean_object* v_res_3642_; 
v_applicationTime_boxed_3641_ = lean_unbox(v_applicationTime_3638_);
v_res_3642_ = l_Lean_registerEnumAttributes(v_00_u03b1_3635_, v_attrDescrs_3636_, v_validate_3637_, v_applicationTime_boxed_3641_, v_ref_3639_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3643_, lean_object* v_env_3644_, lean_object* v_as_3645_, size_t v_i_3646_, size_t v_stop_3647_, lean_object* v_b_3648_){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3644_, v_as_3645_, v_i_3646_, v_stop_3647_, v_b_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3650_, lean_object* v_env_3651_, lean_object* v_as_3652_, lean_object* v_i_3653_, lean_object* v_stop_3654_, lean_object* v_b_3655_){
_start:
{
size_t v_i_boxed_3656_; size_t v_stop_boxed_3657_; lean_object* v_res_3658_; 
v_i_boxed_3656_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_stop_boxed_3657_ = lean_unbox_usize(v_stop_3654_);
lean_dec(v_stop_3654_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3650_, v_env_3651_, v_as_3652_, v_i_boxed_3656_, v_stop_boxed_3657_, v_b_3655_);
lean_dec_ref(v_as_3652_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3659_, lean_object* v_newState_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3660_, v_x_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_newState_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3664_, v_newState_3665_, v_x_3666_, v_x_3667_);
lean_dec(v_newState_3665_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3669_, lean_object* v_validate_3670_, lean_object* v_a_3671_, lean_object* v_ref_3672_, uint8_t v_applicationTime_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3670_, v_a_3671_, v_ref_3672_, v_applicationTime_3673_, v_a_3674_, v_a_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_validate_3678_, lean_object* v_a_3679_, lean_object* v_ref_3680_, lean_object* v_applicationTime_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
uint8_t v_applicationTime_boxed_3684_; lean_object* v_res_3685_; 
v_applicationTime_boxed_3684_ = lean_unbox(v_applicationTime_3681_);
v_res_3685_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3677_, v_validate_3678_, v_a_3679_, v_ref_3680_, v_applicationTime_boxed_3684_, v_a_3682_, v_a_3683_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3686_, lean_object* v_attr_3687_, lean_object* v_env_3688_, lean_object* v_decl_3689_){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = lean_box(1);
v___x_3691_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3688_, v_decl_3689_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_ext_3692_; lean_object* v_toEnvExtension_3693_; lean_object* v_asyncMode_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
lean_dec(v_inst_3686_);
v_ext_3692_ = lean_ctor_get(v_attr_3687_, 1);
lean_inc_ref(v_ext_3692_);
lean_dec_ref(v_attr_3687_);
v_toEnvExtension_3693_ = lean_ctor_get(v_ext_3692_, 0);
v_asyncMode_3694_ = lean_ctor_get(v_toEnvExtension_3693_, 2);
lean_inc(v_asyncMode_3694_);
lean_inc(v_decl_3689_);
v___x_3695_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3690_, v_ext_3692_, v_env_3688_, v_asyncMode_3694_, v_decl_3689_);
lean_dec(v_asyncMode_3694_);
lean_dec_ref(v_ext_3692_);
v___x_3696_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3695_, v_decl_3689_);
lean_dec(v_decl_3689_);
lean_dec(v___x_3695_);
return v___x_3696_;
}
else
{
lean_object* v_val_3697_; lean_object* v_ext_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3728_; 
v_val_3697_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_val_3697_);
lean_dec_ref_known(v___x_3691_, 1);
v_ext_3698_ = lean_ctor_get(v_attr_3687_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_attr_3687_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_attr_3687_, 0);
lean_dec(v_unused_3729_);
v___x_3700_ = v_attr_3687_;
v_isShared_3701_ = v_isSharedCheck_3728_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_ext_3698_);
lean_dec(v_attr_3687_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3728_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
uint8_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3702_ = 0;
v___x_3703_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3690_, v_ext_3698_, v_env_3688_, v_val_3697_, v___x_3702_);
lean_dec(v_val_3697_);
lean_dec_ref(v_env_3688_);
lean_dec_ref(v_ext_3698_);
v___x_3704_ = lean_unsigned_to_nat(0u);
v___x_3705_ = lean_array_get_size(v___x_3703_);
v___x_3706_ = lean_nat_dec_lt(v___x_3704_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; 
lean_dec_ref(v___x_3703_);
lean_del_object(v___x_3700_);
lean_dec(v_decl_3689_);
lean_dec(v_inst_3686_);
v___x_3707_ = lean_box(0);
return v___x_3707_;
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_unsigned_to_nat(1u);
v___x_3709_ = lean_nat_sub(v___x_3705_, v___x_3708_);
v___x_3710_ = lean_nat_dec_le(v___x_3704_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
lean_dec(v___x_3709_);
lean_dec_ref(v___x_3703_);
lean_del_object(v___x_3700_);
lean_dec(v_decl_3689_);
lean_dec(v_inst_3686_);
v___x_3711_ = lean_box(0);
return v___x_3711_;
}
else
{
lean_object* v___f_3712_; lean_object* v___x_3714_; 
v___f_3712_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 1, v_inst_3686_);
lean_ctor_set(v___x_3700_, 0, v_decl_3689_);
v___x_3714_ = v___x_3700_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_decl_3689_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_inst_3686_);
v___x_3714_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3716_ = l_Array_binSearchAux___redArg(v___f_3712_, v___x_3715_, v___x_3703_, v___x_3714_, v___x_3704_, v___x_3709_);
lean_dec_ref(v___x_3703_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_box(0);
return v___x_3717_;
}
else
{
lean_object* v_val_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3726_; 
v_val_3718_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3720_ = v___x_3716_;
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_val_3718_);
lean_dec(v___x_3716_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3726_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v_snd_3722_; lean_object* v___x_3724_; 
v_snd_3722_ = lean_ctor_get(v_val_3718_, 1);
lean_inc(v_snd_3722_);
lean_dec(v_val_3718_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v_snd_3722_);
v___x_3724_ = v___x_3720_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_snd_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3730_, lean_object* v_inst_3731_, lean_object* v_attr_3732_, lean_object* v_env_3733_, lean_object* v_decl_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3731_, v_attr_3732_, v_env_3733_, v_decl_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3744_, lean_object* v_env_3745_, lean_object* v_decl_3746_, lean_object* v_val_3747_){
_start:
{
lean_object* v_ext_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3811_; 
v_ext_3748_ = lean_ctor_get(v_attrs_3744_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_attrs_3744_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_attrs_3744_, 0);
lean_dec(v_unused_3812_);
v___x_3750_ = v_attrs_3744_;
v_isShared_3751_ = v_isSharedCheck_3811_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_ext_3748_);
lean_dec(v_attrs_3744_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3811_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v_toEnvExtension_3752_; lean_object* v_name_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_pfx_3763_; lean_object* v___x_3764_; 
v_toEnvExtension_3752_ = lean_ctor_get(v_ext_3748_, 0);
v_name_3753_ = lean_ctor_get(v_ext_3748_, 1);
v___x_3754_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3755_ = 1;
lean_inc(v_name_3753_);
v___x_3756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3753_, v___x_3755_);
v___x_3757_ = lean_string_append(v___x_3754_, v___x_3756_);
lean_dec_ref(v___x_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3759_ = lean_string_append(v___x_3757_, v___x_3758_);
lean_inc(v_decl_3746_);
v___x_3760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3746_, v___x_3755_);
v___x_3761_ = lean_string_append(v___x_3759_, v___x_3760_);
lean_dec_ref(v___x_3760_);
v___x_3762_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3763_ = lean_string_append(v___x_3761_, v___x_3762_);
v___x_3764_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3745_, v_decl_3746_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_asyncMode_3765_; uint8_t v___x_3766_; 
v_asyncMode_3765_ = lean_ctor_get(v_toEnvExtension_3752_, 2);
lean_inc(v_asyncMode_3765_);
lean_inc(v_decl_3746_);
lean_inc_ref(v_env_3745_);
v___x_3766_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3745_, v_decl_3746_, v_asyncMode_3765_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___y_3770_; lean_object* v___x_3774_; 
lean_dec(v_asyncMode_3765_);
lean_del_object(v___x_3750_);
lean_dec_ref(v_ext_3748_);
lean_dec(v_val_3747_);
lean_dec(v_decl_3746_);
v___x_3767_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3768_ = lean_string_append(v_pfx_3763_, v___x_3767_);
v___x_3774_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3745_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3770_ = v___x_3775_;
goto v___jp_3769_;
}
else
{
lean_object* v_val_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_val_3776_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3774_, 1);
v___x_3777_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3776_, v___x_3755_);
v___x_3779_ = l_addParenHeuristic(v___x_3778_);
v___x_3780_ = lean_string_append(v___x_3777_, v___x_3779_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
v___y_3770_ = v___x_3782_;
goto v___jp_3769_;
}
v___jp_3769_:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = lean_string_append(v___x_3768_, v___y_3770_);
lean_dec_ref(v___y_3770_);
v___x_3772_ = lean_string_append(v___x_3771_, v___x_3762_);
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3783_ = lean_box(1);
lean_inc(v_decl_3746_);
lean_inc_ref(v_env_3745_);
v___x_3784_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3783_, v_ext_3748_, v_env_3745_, v_asyncMode_3765_, v_decl_3746_);
v___x_3785_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3784_, v_decl_3746_);
lean_dec(v___x_3784_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v_pfx_3763_);
lean_inc(v_decl_3746_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 1, v_val_3747_);
lean_ctor_set(v___x_3750_, 0, v_decl_3746_);
v___x_3787_ = v___x_3750_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_decl_3746_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_val_3747_);
v___x_3787_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3748_, v_env_3745_, v___x_3787_, v_asyncMode_3765_, v_decl_3746_);
lean_dec(v_asyncMode_3765_);
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
else
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3799_; 
lean_dec(v_asyncMode_3765_);
lean_del_object(v___x_3750_);
lean_dec_ref(v_ext_3748_);
lean_dec(v_val_3747_);
lean_dec(v_decl_3746_);
lean_dec_ref(v_env_3745_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3785_, 0);
lean_dec(v_unused_3800_);
v___x_3792_ = v___x_3785_;
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3785_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3799_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3794_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3795_ = lean_string_append(v_pfx_3763_, v___x_3794_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3795_);
v___x_3797_ = v___x_3792_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
else
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3809_; 
lean_del_object(v___x_3750_);
lean_dec_ref(v_ext_3748_);
lean_dec(v_val_3747_);
lean_dec(v_decl_3746_);
lean_dec_ref(v_env_3745_);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v___x_3764_, 0);
lean_dec(v_unused_3810_);
v___x_3802_ = v___x_3764_;
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v___x_3764_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3809_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3804_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3805_ = lean_string_append(v_pfx_3763_, v___x_3804_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3805_);
v___x_3807_ = v___x_3802_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3813_, lean_object* v_attrs_3814_, lean_object* v_env_3815_, lean_object* v_decl_3816_, lean_object* v_val_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3814_, v_env_3815_, v_decl_3816_, v_val_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3821_ = lean_st_mk_ref(v___x_3820_);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3827_, lean_object* v_builder_3828_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3830_ = l_Lean_attributeImplBuilderTableRef;
v___x_3831_ = lean_st_ref_get(v___x_3830_);
v___x_3832_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3831_, v_builderId_3827_);
lean_dec(v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3833_ = lean_st_ref_take(v___x_3830_);
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3833_, v_builderId_3827_, v_builder_3828_);
v___x_3835_ = lean_st_ref_put(v___x_3830_, v___x_3834_);
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
return v___x_3836_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v_builder_3828_);
v___x_3837_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3827_, v___x_3832_);
v___x_3839_ = lean_string_append(v___x_3837_, v___x_3838_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3841_ = lean_string_append(v___x_3839_, v___x_3840_);
v___x_3842_ = lean_mk_io_user_error(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3844_, lean_object* v_builder_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_registerAttributeImplBuilder(v_builderId_3844_, v_builder_3845_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3848_){
_start:
{
if (lean_obj_tag(v_e_3848_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3858_; 
v_a_3850_ = lean_ctor_get(v_e_3848_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_e_3848_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3852_ = v_e_3848_;
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v_e_3848_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3858_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
v___x_3854_ = lean_mk_io_user_error(v_a_3850_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 1);
lean_ctor_set(v___x_3852_, 0, v___x_3854_);
v___x_3856_ = v___x_3852_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
v_a_3859_ = lean_ctor_get(v_e_3848_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_e_3848_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v_e_3848_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v_e_3848_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
lean_ctor_set_tag(v___x_3861_, 0);
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3870_, lean_object* v_e_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3874_, lean_object* v_e_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3874_, v_e_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
if (lean_obj_tag(v_x_3879_) == 0)
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_box(0);
return v___x_3880_;
}
else
{
lean_object* v_key_3881_; lean_object* v_value_3882_; lean_object* v_tail_3883_; uint8_t v___x_3884_; 
v_key_3881_ = lean_ctor_get(v_x_3879_, 0);
v_value_3882_ = lean_ctor_get(v_x_3879_, 1);
v_tail_3883_ = lean_ctor_get(v_x_3879_, 2);
v___x_3884_ = lean_name_eq(v_key_3881_, v_a_3878_);
if (v___x_3884_ == 0)
{
v_x_3879_ = v_tail_3883_;
goto _start;
}
else
{
lean_object* v___x_3886_; 
lean_inc(v_value_3882_);
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_value_3882_);
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3887_, v_x_3888_);
lean_dec(v_x_3888_);
lean_dec(v_a_3887_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v_buckets_3892_; lean_object* v___x_3893_; uint64_t v___y_3895_; 
v_buckets_3892_ = lean_ctor_get(v_m_3890_, 1);
v___x_3893_ = lean_array_get_size(v_buckets_3892_);
if (lean_obj_tag(v_a_3891_) == 0)
{
uint64_t v___x_3909_; 
v___x_3909_ = 1723ULL;
v___y_3895_ = v___x_3909_;
goto v___jp_3894_;
}
else
{
uint64_t v_hash_3910_; 
v_hash_3910_ = lean_ctor_get_uint64(v_a_3891_, sizeof(void*)*2);
v___y_3895_ = v_hash_3910_;
goto v___jp_3894_;
}
v___jp_3894_:
{
uint64_t v___x_3896_; uint64_t v___x_3897_; uint64_t v_fold_3898_; uint64_t v___x_3899_; uint64_t v___x_3900_; uint64_t v___x_3901_; size_t v___x_3902_; size_t v___x_3903_; size_t v___x_3904_; size_t v___x_3905_; size_t v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3896_ = 32ULL;
v___x_3897_ = lean_uint64_shift_right(v___y_3895_, v___x_3896_);
v_fold_3898_ = lean_uint64_xor(v___y_3895_, v___x_3897_);
v___x_3899_ = 16ULL;
v___x_3900_ = lean_uint64_shift_right(v_fold_3898_, v___x_3899_);
v___x_3901_ = lean_uint64_xor(v_fold_3898_, v___x_3900_);
v___x_3902_ = lean_uint64_to_usize(v___x_3901_);
v___x_3903_ = lean_usize_of_nat(v___x_3893_);
v___x_3904_ = ((size_t)1ULL);
v___x_3905_ = lean_usize_sub(v___x_3903_, v___x_3904_);
v___x_3906_ = lean_usize_land(v___x_3902_, v___x_3905_);
v___x_3907_ = lean_array_uget_borrowed(v_buckets_3892_, v___x_3906_);
v___x_3908_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3891_, v___x_3907_);
return v___x_3908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_m_3911_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3915_){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v_builderId_3919_; lean_object* v_ref_3920_; lean_object* v_args_3921_; lean_object* v___x_3922_; 
v___x_3917_ = l_Lean_attributeImplBuilderTableRef;
v___x_3918_ = lean_st_ref_get(v___x_3917_);
v_builderId_3919_ = lean_ctor_get(v_e_3915_, 0);
lean_inc(v_builderId_3919_);
v_ref_3920_ = lean_ctor_get(v_e_3915_, 1);
lean_inc(v_ref_3920_);
v_args_3921_ = lean_ctor_get(v_e_3915_, 2);
lean_inc(v_args_3921_);
lean_dec_ref(v_e_3915_);
v___x_3922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3918_, v_builderId_3919_);
lean_dec(v___x_3918_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v___x_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec(v_args_3921_);
lean_dec(v_ref_3920_);
v___x_3923_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3924_ = 1;
v___x_3925_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3919_, v___x_3924_);
v___x_3926_ = lean_string_append(v___x_3923_, v___x_3925_);
lean_dec_ref(v___x_3925_);
v___x_3927_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3928_ = lean_string_append(v___x_3926_, v___x_3927_);
v___x_3929_ = lean_mk_io_user_error(v___x_3928_);
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
else
{
lean_object* v_val_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v_builderId_3919_);
v_val_3931_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3932_ = lean_apply_2(v_val_3931_, v_ref_3920_, v_args_3921_);
v___x_3933_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3932_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_mkAttributeImplOfEntry(v_e_3934_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3937_, lean_object* v_m_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3938_, v_a_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3941_, lean_object* v_m_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3941_, v_m_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_m_3942_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3945_, lean_object* v_a_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3946_, v_x_3947_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3949_, lean_object* v_a_3950_, lean_object* v_x_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3949_, v_a_3950_, v_x_3951_);
lean_dec(v_x_3951_);
lean_dec(v_a_3950_);
return v_res_3952_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3953_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3954_ = lean_box(0);
v___x_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___x_3953_);
return v___x_3955_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3956_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3959_ = l_Lean_attributeMapRef;
v___x_3960_ = lean_st_ref_get(v___x_3959_);
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3960_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3971_, lean_object* v_opts_3972_, lean_object* v_declName_3973_){
_start:
{
uint8_t v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = 0;
lean_inc(v_declName_3973_);
lean_inc_ref(v_env_3971_);
v___x_3977_ = l_Lean_Environment_find_x3f(v_env_3971_, v_declName_3973_, v___x_3976_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v___x_3978_; uint8_t v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_dec_ref(v_env_3971_);
v___x_3978_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3979_ = 1;
v___x_3980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3973_, v___x_3979_);
v___x_3981_ = lean_string_append(v___x_3978_, v___x_3980_);
lean_dec_ref(v___x_3980_);
v___x_3982_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3983_ = lean_string_append(v___x_3981_, v___x_3982_);
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
return v___x_3984_;
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3986_; 
v_val_3985_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_val_3985_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3986_ = l_Lean_ConstantInfo_type(v_val_3985_);
lean_dec(v_val_3985_);
if (lean_obj_tag(v___x_3986_) == 4)
{
lean_object* v_declName_3987_; 
v_declName_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_declName_3987_);
lean_dec_ref_known(v___x_3986_, 2);
if (lean_obj_tag(v_declName_3987_) == 1)
{
lean_object* v_pre_3988_; 
v_pre_3988_ = lean_ctor_get(v_declName_3987_, 0);
lean_inc(v_pre_3988_);
if (lean_obj_tag(v_pre_3988_) == 1)
{
lean_object* v_pre_3989_; 
v_pre_3989_ = lean_ctor_get(v_pre_3988_, 0);
if (lean_obj_tag(v_pre_3989_) == 0)
{
lean_object* v_str_3990_; lean_object* v_str_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_str_3990_ = lean_ctor_get(v_declName_3987_, 1);
lean_inc_ref(v_str_3990_);
lean_dec_ref_known(v_declName_3987_, 2);
v_str_3991_ = lean_ctor_get(v_pre_3988_, 1);
lean_inc_ref(v_str_3991_);
lean_dec_ref_known(v_pre_3988_, 2);
v___x_3992_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3993_ = lean_string_dec_eq(v_str_3991_, v___x_3992_);
lean_dec_ref(v_str_3991_);
if (v___x_3993_ == 0)
{
lean_dec_ref(v_str_3990_);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
else
{
lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3994_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3995_ = lean_string_dec_eq(v_str_3990_, v___x_3994_);
lean_dec_ref(v_str_3990_);
if (v___x_3995_ == 0)
{
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
else
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_Environment_evalConst___redArg(v_env_3971_, v_opts_3972_, v_declName_3973_, v___x_3995_);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
return v___x_3996_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3988_, 2);
lean_dec_ref_known(v_declName_3987_, 2);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
}
else
{
lean_dec(v_pre_3988_);
lean_dec_ref_known(v_declName_3987_, 2);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
}
else
{
lean_dec(v_declName_3987_);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
}
else
{
lean_dec_ref(v___x_3986_);
lean_dec(v_declName_3973_);
lean_dec_ref(v_env_3971_);
goto v___jp_3974_;
}
}
v___jp_3974_:
{
lean_object* v___x_3975_; 
v___x_3975_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3997_, lean_object* v_opts_3998_, lean_object* v_declName_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3997_, v_opts_3998_, v_declName_3999_);
lean_dec_ref(v_opts_3998_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4001_, size_t v_i_4002_, size_t v_stop_4003_, lean_object* v_b_4004_){
_start:
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_usize_dec_eq(v_i_4002_, v_stop_4003_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_array_uget_borrowed(v_as_4001_, v_i_4002_);
lean_inc(v___x_4007_);
v___x_4008_ = l_Lean_mkAttributeImplOfEntry(v___x_4007_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v_toAttributeImplCore_4010_; lean_object* v_name_4011_; lean_object* v___x_4012_; size_t v___x_4013_; size_t v___x_4014_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v_toAttributeImplCore_4010_ = lean_ctor_get(v_a_4009_, 0);
v_name_4011_ = lean_ctor_get(v_toAttributeImplCore_4010_, 1);
lean_inc(v_name_4011_);
v___x_4012_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4004_, v_name_4011_, v_a_4009_);
v___x_4013_ = ((size_t)1ULL);
v___x_4014_ = lean_usize_add(v_i_4002_, v___x_4013_);
v_i_4002_ = v___x_4014_;
v_b_4004_ = v___x_4012_;
goto _start;
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_b_4004_);
v_a_4016_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4008_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4008_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_b_4004_);
return v___x_4024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4025_, lean_object* v_i_4026_, lean_object* v_stop_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_){
_start:
{
size_t v_i_boxed_4030_; size_t v_stop_boxed_4031_; lean_object* v_res_4032_; 
v_i_boxed_4030_ = lean_unbox_usize(v_i_4026_);
lean_dec(v_i_4026_);
v_stop_boxed_4031_ = lean_unbox_usize(v_stop_4027_);
lean_dec(v_stop_4027_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4025_, v_i_boxed_4030_, v_stop_boxed_4031_, v_b_4028_);
lean_dec_ref(v_as_4025_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4033_, size_t v_i_4034_, size_t v_stop_4035_, lean_object* v_b_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_a_4040_; lean_object* v___y_4045_; uint8_t v___x_4047_; 
v___x_4047_ = lean_usize_dec_eq(v_i_4034_, v_stop_4035_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4048_ = lean_array_uget_borrowed(v_as_4033_, v_i_4034_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_array_get_size(v___x_4048_);
v___x_4051_ = lean_nat_dec_lt(v___x_4049_, v___x_4050_);
if (v___x_4051_ == 0)
{
v_a_4040_ = v_b_4036_;
goto v___jp_4039_;
}
else
{
uint8_t v___x_4052_; 
v___x_4052_ = lean_nat_dec_le(v___x_4050_, v___x_4050_);
if (v___x_4052_ == 0)
{
if (v___x_4051_ == 0)
{
v_a_4040_ = v_b_4036_;
goto v___jp_4039_;
}
else
{
size_t v___x_4053_; size_t v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = ((size_t)0ULL);
v___x_4054_ = lean_usize_of_nat(v___x_4050_);
v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4048_, v___x_4053_, v___x_4054_, v_b_4036_);
v___y_4045_ = v___x_4055_;
goto v___jp_4044_;
}
}
else
{
size_t v___x_4056_; size_t v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = ((size_t)0ULL);
v___x_4057_ = lean_usize_of_nat(v___x_4050_);
v___x_4058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4048_, v___x_4056_, v___x_4057_, v_b_4036_);
v___y_4045_ = v___x_4058_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v___x_4059_; 
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v_b_4036_);
return v___x_4059_;
}
v___jp_4039_:
{
size_t v___x_4041_; size_t v___x_4042_; 
v___x_4041_ = ((size_t)1ULL);
v___x_4042_ = lean_usize_add(v_i_4034_, v___x_4041_);
v_i_4034_ = v___x_4042_;
v_b_4036_ = v_a_4040_;
goto _start;
}
v___jp_4044_:
{
if (lean_obj_tag(v___y_4045_) == 0)
{
lean_object* v_a_4046_; 
v_a_4046_ = lean_ctor_get(v___y_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___y_4045_, 1);
v_a_4040_ = v_a_4046_;
goto v___jp_4039_;
}
else
{
return v___y_4045_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4060_, lean_object* v_i_4061_, lean_object* v_stop_4062_, lean_object* v_b_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
size_t v_i_boxed_4066_; size_t v_stop_boxed_4067_; lean_object* v_res_4068_; 
v_i_boxed_4066_ = lean_unbox_usize(v_i_4061_);
lean_dec(v_i_4061_);
v_stop_boxed_4067_ = lean_unbox_usize(v_stop_4062_);
lean_dec(v_stop_4062_);
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4060_, v_i_boxed_4066_, v_stop_boxed_4067_, v_b_4063_, v___y_4064_);
lean_dec_ref(v___y_4064_);
lean_dec_ref(v_as_4060_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_a_4073_; lean_object* v___y_4078_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v___x_4088_ = l_Lean_attributeMapRef;
v___x_4089_ = lean_st_ref_get(v___x_4088_);
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = lean_array_get_size(v_es_4069_);
v___x_4092_ = lean_nat_dec_lt(v___x_4090_, v___x_4091_);
if (v___x_4092_ == 0)
{
v_a_4073_ = v___x_4089_;
goto v___jp_4072_;
}
else
{
uint8_t v___x_4093_; 
v___x_4093_ = lean_nat_dec_le(v___x_4091_, v___x_4091_);
if (v___x_4093_ == 0)
{
if (v___x_4092_ == 0)
{
v_a_4073_ = v___x_4089_;
goto v___jp_4072_;
}
else
{
size_t v___x_4094_; size_t v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = ((size_t)0ULL);
v___x_4095_ = lean_usize_of_nat(v___x_4091_);
v___x_4096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4069_, v___x_4094_, v___x_4095_, v___x_4089_, v_a_4070_);
v___y_4078_ = v___x_4096_;
goto v___jp_4077_;
}
}
else
{
size_t v___x_4097_; size_t v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = ((size_t)0ULL);
v___x_4098_ = lean_usize_of_nat(v___x_4091_);
v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4069_, v___x_4097_, v___x_4098_, v___x_4089_, v_a_4070_);
v___y_4078_ = v___x_4099_;
goto v___jp_4077_;
}
}
v___jp_4072_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = lean_box(0);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v_a_4073_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
v___jp_4077_:
{
if (lean_obj_tag(v___y_4078_) == 0)
{
lean_object* v_a_4079_; 
v_a_4079_ = lean_ctor_get(v___y_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___y_4078_, 1);
v_a_4073_ = v_a_4079_;
goto v___jp_4072_;
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_a_4080_ = lean_ctor_get(v___y_4078_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___y_4078_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___y_4078_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___y_4078_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4100_, v_a_4101_);
lean_dec_ref(v_a_4101_);
lean_dec_ref(v_es_4100_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4104_, size_t v_i_4105_, size_t v_stop_4106_, lean_object* v_b_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4104_, v_i_4105_, v_stop_4106_, v_b_4107_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4111_, lean_object* v_i_4112_, lean_object* v_stop_4113_, lean_object* v_b_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
size_t v_i_boxed_4117_; size_t v_stop_boxed_4118_; lean_object* v_res_4119_; 
v_i_boxed_4117_ = lean_unbox_usize(v_i_4112_);
lean_dec(v_i_4112_);
v_stop_boxed_4118_ = lean_unbox_usize(v_stop_4113_);
lean_dec(v_stop_4113_);
v_res_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4111_, v_i_boxed_4117_, v_stop_boxed_4118_, v_b_4114_, v___y_4115_);
lean_dec_ref(v___y_4115_);
lean_dec_ref(v_as_4111_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4120_, lean_object* v_e_4121_){
_start:
{
lean_object* v_snd_4122_; lean_object* v_toAttributeImplCore_4123_; lean_object* v_fst_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4142_; 
v_snd_4122_ = lean_ctor_get(v_e_4121_, 1);
lean_inc(v_snd_4122_);
v_toAttributeImplCore_4123_ = lean_ctor_get(v_snd_4122_, 0);
v_fst_4124_ = lean_ctor_get(v_e_4121_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_e_4121_);
if (v_isSharedCheck_4142_ == 0)
{
lean_object* v_unused_4143_; 
v_unused_4143_ = lean_ctor_get(v_e_4121_, 1);
lean_dec(v_unused_4143_);
v___x_4126_ = v_e_4121_;
v_isShared_4127_ = v_isSharedCheck_4142_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_fst_4124_);
lean_dec(v_e_4121_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4142_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v_newEntries_4128_; lean_object* v_map_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4141_; 
v_newEntries_4128_ = lean_ctor_get(v_s_4120_, 0);
v_map_4129_ = lean_ctor_get(v_s_4120_, 1);
v_isSharedCheck_4141_ = !lean_is_exclusive(v_s_4120_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4131_ = v_s_4120_;
v_isShared_4132_ = v_isSharedCheck_4141_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_map_4129_);
lean_inc(v_newEntries_4128_);
lean_dec(v_s_4120_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4141_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v_name_4133_; lean_object* v___x_4135_; 
v_name_4133_ = lean_ctor_get(v_toAttributeImplCore_4123_, 1);
lean_inc(v_name_4133_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set_tag(v___x_4126_, 1);
lean_ctor_set(v___x_4126_, 1, v_newEntries_4128_);
v___x_4135_ = v___x_4126_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_fst_4124_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v_newEntries_4128_);
v___x_4135_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4138_; 
v___x_4136_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4129_, v_name_4133_, v_snd_4122_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 1, v___x_4136_);
lean_ctor_set(v___x_4131_, 0, v___x_4135_);
v___x_4138_ = v___x_4131_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4135_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4144_, lean_object* v_s_4145_){
_start:
{
lean_object* v_newEntries_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_newEntries_4146_ = lean_ctor_get(v_s_4145_, 0);
lean_inc(v_newEntries_4146_);
lean_dec_ref(v_s_4145_);
v___x_4147_ = l_List_reverse___redArg(v_newEntries_4146_);
v___x_4148_ = lean_array_mk(v___x_4147_);
lean_inc_ref_n(v___x_4148_, 2);
v___x_4149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
lean_ctor_set(v___x_4149_, 2, v___x_4148_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4150_, lean_object* v_s_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4150_, v_s_4151_);
lean_dec_ref(v_x_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4153_){
_start:
{
lean_object* v_newEntries_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4165_; 
v_newEntries_4154_ = lean_ctor_get(v_s_4153_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_s_4153_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_s_4153_, 1);
lean_dec(v_unused_4166_);
v___x_4156_ = v_s_4153_;
v_isShared_4157_ = v_isSharedCheck_4165_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_newEntries_4154_);
lean_dec(v_s_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4165_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4163_; 
v___x_4158_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4159_ = l_List_lengthTR___redArg(v_newEntries_4154_);
lean_dec(v_newEntries_4154_);
v___x_4160_ = l_Nat_reprFast(v___x_4159_);
v___x_4161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set_tag(v___x_4156_, 5);
lean_ctor_set(v___x_4156_, 1, v___x_4161_);
lean_ctor_set(v___x_4156_, 0, v___x_4158_);
v___x_4163_ = v___x_4156_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4158_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_4161_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4167_){
_start:
{
lean_object* v_newEntries_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v_newEntries_4168_ = lean_ctor_get(v_s_4167_, 0);
lean_inc(v_newEntries_4168_);
lean_dec_ref(v_s_4167_);
v___x_4169_ = l_List_reverse___redArg(v_newEntries_4168_);
v___x_4170_ = lean_array_mk(v___x_4169_);
return v___x_4170_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; lean_object* v___f_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4180_ = lean_box(0);
v___x_4181_ = lean_box(2);
v___f_4182_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4183_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4184_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4185_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4186_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4187_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4188_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
lean_ctor_set(v___x_4188_, 1, v___x_4186_);
lean_ctor_set(v___x_4188_, 2, v___x_4185_);
lean_ctor_set(v___x_4188_, 3, v___x_4184_);
lean_ctor_set(v___x_4188_, 4, v___f_4183_);
lean_ctor_set(v___x_4188_, 5, v___f_4182_);
lean_ctor_set(v___x_4188_, 6, v___x_4181_);
lean_ctor_set(v___x_4188_, 7, v___x_4180_);
return v___x_4188_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___f_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4190_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v___f_4189_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4194_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4199_ = l_Lean_attributeMapRef;
v___x_4200_ = lean_st_ref_get(v___x_4199_);
v___x_4201_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4200_, v_n_4197_);
lean_dec(v___x_4200_);
v___x_4202_ = lean_box(v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4204_, lean_object* v_a_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_isBuiltinAttribute(v_n_4204_);
lean_dec(v_n_4204_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4207_, lean_object* v_x_4208_){
_start:
{
if (lean_obj_tag(v_x_4208_) == 0)
{
return v_x_4207_;
}
else
{
lean_object* v_key_4209_; lean_object* v_tail_4210_; lean_object* v___x_4211_; 
v_key_4209_ = lean_ctor_get(v_x_4208_, 0);
v_tail_4210_ = lean_ctor_get(v_x_4208_, 2);
lean_inc(v_key_4209_);
v___x_4211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4211_, 0, v_key_4209_);
lean_ctor_set(v___x_4211_, 1, v_x_4207_);
v_x_4207_ = v___x_4211_;
v_x_4208_ = v_tail_4210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4213_, lean_object* v_x_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4213_, v_x_4214_);
lean_dec(v_x_4214_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4216_, size_t v_i_4217_, size_t v_stop_4218_, lean_object* v_b_4219_){
_start:
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_usize_dec_eq(v_i_4217_, v_stop_4218_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; size_t v___x_4223_; size_t v___x_4224_; 
v___x_4221_ = lean_array_uget_borrowed(v_as_4216_, v_i_4217_);
v___x_4222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4219_, v___x_4221_);
v___x_4223_ = ((size_t)1ULL);
v___x_4224_ = lean_usize_add(v_i_4217_, v___x_4223_);
v_i_4217_ = v___x_4224_;
v_b_4219_ = v___x_4222_;
goto _start;
}
else
{
return v_b_4219_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4226_, lean_object* v_i_4227_, lean_object* v_stop_4228_, lean_object* v_b_4229_){
_start:
{
size_t v_i_boxed_4230_; size_t v_stop_boxed_4231_; lean_object* v_res_4232_; 
v_i_boxed_4230_ = lean_unbox_usize(v_i_4227_);
lean_dec(v_i_4227_);
v_stop_boxed_4231_ = lean_unbox_usize(v_stop_4228_);
lean_dec(v_stop_4228_);
v_res_4232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4226_, v_i_boxed_4230_, v_stop_boxed_4231_, v_b_4229_);
lean_dec_ref(v_as_4226_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v_buckets_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v___x_4234_ = l_Lean_attributeMapRef;
v___x_4235_ = lean_st_ref_get(v___x_4234_);
v_buckets_4236_ = lean_ctor_get(v___x_4235_, 1);
lean_inc_ref(v_buckets_4236_);
lean_dec(v___x_4235_);
v___x_4237_ = lean_box(0);
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_array_get_size(v_buckets_4236_);
v___x_4240_ = lean_nat_dec_lt(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; 
lean_dec_ref(v_buckets_4236_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4237_);
return v___x_4241_;
}
else
{
size_t v___x_4242_; size_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4242_ = ((size_t)0ULL);
v___x_4243_ = lean_usize_of_nat(v___x_4239_);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4236_, v___x_4242_, v___x_4243_, v___x_4237_);
lean_dec_ref(v_buckets_4236_);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
return v___x_4245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_getBuiltinAttributeNames();
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4249_){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = l_Lean_attributeMapRef;
v___x_4252_ = lean_st_ref_get(v___x_4251_);
v___x_4253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4252_, v_attrName_4249_);
lean_dec(v___x_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4254_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4255_ = 1;
v___x_4256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4249_, v___x_4255_);
v___x_4257_ = lean_string_append(v___x_4254_, v___x_4256_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4259_ = lean_string_append(v___x_4257_, v___x_4258_);
v___x_4260_ = lean_mk_io_user_error(v___x_4259_);
v___x_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
return v___x_4261_;
}
else
{
lean_object* v_val_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec(v_attrName_4249_);
v_val_4262_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4253_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_val_4262_);
lean_dec(v___x_4253_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
lean_ctor_set_tag(v___x_4264_, 0);
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_val_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4270_);
return v_res_4272_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4273_, lean_object* v_attrName_4274_){
_start:
{
lean_object* v___x_4275_; lean_object* v_toEnvExtension_4276_; lean_object* v_asyncMode_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v_map_4281_; uint8_t v___x_4282_; 
v___x_4275_ = l_Lean_attributeExtension;
v_toEnvExtension_4276_ = lean_ctor_get(v___x_4275_, 0);
v_asyncMode_4277_ = lean_ctor_get(v_toEnvExtension_4276_, 2);
v___x_4278_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4279_ = lean_box(0);
v___x_4280_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4278_, v___x_4275_, v_env_4273_, v_asyncMode_4277_, v___x_4279_);
v_map_4281_ = lean_ctor_get(v___x_4280_, 1);
lean_inc_ref(v_map_4281_);
lean_dec(v___x_4280_);
v___x_4282_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4281_, v_attrName_4274_);
lean_dec_ref(v_map_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4283_, lean_object* v_attrName_4284_){
_start:
{
uint8_t v_res_4285_; lean_object* v_r_4286_; 
v_res_4285_ = l_Lean_isAttribute(v_env_4283_, v_attrName_4284_);
lean_dec(v_attrName_4284_);
v_r_4286_ = lean_box(v_res_4285_);
return v_r_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4287_){
_start:
{
lean_object* v___x_4288_; lean_object* v_toEnvExtension_4289_; lean_object* v_asyncMode_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v_map_4294_; lean_object* v_buckets_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4288_ = l_Lean_attributeExtension;
v_toEnvExtension_4289_ = lean_ctor_get(v___x_4288_, 0);
v_asyncMode_4290_ = lean_ctor_get(v_toEnvExtension_4289_, 2);
v___x_4291_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4292_ = lean_box(0);
v___x_4293_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4291_, v___x_4288_, v_env_4287_, v_asyncMode_4290_, v___x_4292_);
v_map_4294_ = lean_ctor_get(v___x_4293_, 1);
lean_inc_ref(v_map_4294_);
lean_dec(v___x_4293_);
v_buckets_4295_ = lean_ctor_get(v_map_4294_, 1);
lean_inc_ref(v_buckets_4295_);
lean_dec_ref(v_map_4294_);
v___x_4296_ = lean_box(0);
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_array_get_size(v_buckets_4295_);
v___x_4299_ = lean_nat_dec_lt(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_dec_ref(v_buckets_4295_);
return v___x_4296_;
}
else
{
size_t v___x_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v___x_4300_ = ((size_t)0ULL);
v___x_4301_ = lean_usize_of_nat(v___x_4298_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4295_, v___x_4300_, v___x_4301_, v___x_4296_);
lean_dec_ref(v_buckets_4295_);
return v___x_4302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4303_, lean_object* v_attrName_4304_){
_start:
{
lean_object* v___x_4305_; lean_object* v_toEnvExtension_4306_; lean_object* v_asyncMode_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v_map_4311_; lean_object* v___x_4312_; 
v___x_4305_ = l_Lean_attributeExtension;
v_toEnvExtension_4306_ = lean_ctor_get(v___x_4305_, 0);
v_asyncMode_4307_ = lean_ctor_get(v_toEnvExtension_4306_, 2);
v___x_4308_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4309_ = lean_box(0);
v___x_4310_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4308_, v___x_4305_, v_env_4303_, v_asyncMode_4307_, v___x_4309_);
v_map_4311_ = lean_ctor_get(v___x_4310_, 1);
lean_inc_ref(v_map_4311_);
lean_dec(v___x_4310_);
v___x_4312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4311_, v_attrName_4304_);
lean_dec_ref(v_map_4311_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v___x_4313_; uint8_t v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4313_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4314_ = 1;
v___x_4315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4304_, v___x_4314_);
v___x_4316_ = lean_string_append(v___x_4313_, v___x_4315_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4318_ = lean_string_append(v___x_4316_, v___x_4317_);
v___x_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4318_);
return v___x_4319_;
}
else
{
lean_object* v_val_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_attrName_4304_);
v_val_4320_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4312_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_val_4320_);
lean_dec(v___x_4312_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_val_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4328_, lean_object* v_builderId_4329_, lean_object* v_ref_4330_, lean_object* v_args_4331_){
_start:
{
lean_object* v_entry_4333_; lean_object* v___x_4334_; 
v_entry_4333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4333_, 0, v_builderId_4329_);
lean_ctor_set(v_entry_4333_, 1, v_ref_4330_);
lean_ctor_set(v_entry_4333_, 2, v_args_4331_);
lean_inc_ref(v_entry_4333_);
v___x_4334_ = l_Lean_mkAttributeImplOfEntry(v_entry_4333_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4360_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4337_ = v___x_4334_;
v_isShared_4338_ = v_isSharedCheck_4360_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4334_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4360_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v_toAttributeImplCore_4339_; lean_object* v_name_4340_; uint8_t v___x_4341_; 
v_toAttributeImplCore_4339_ = lean_ctor_get(v_a_4335_, 0);
v_name_4340_ = lean_ctor_get(v_toAttributeImplCore_4339_, 1);
lean_inc_ref(v_env_4328_);
v___x_4341_ = l_Lean_isAttribute(v_env_4328_, v_name_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v_toEnvExtension_4343_; lean_object* v_asyncMode_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4342_ = l_Lean_attributeExtension;
v_toEnvExtension_4343_ = lean_ctor_get(v___x_4342_, 0);
v_asyncMode_4344_ = lean_ctor_get(v_toEnvExtension_4343_, 2);
v___x_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4345_, 0, v_entry_4333_);
lean_ctor_set(v___x_4345_, 1, v_a_4335_);
v___x_4346_ = lean_box(0);
v___x_4347_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4342_, v_env_4328_, v___x_4345_, v_asyncMode_4344_, v___x_4346_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 0, v___x_4347_);
v___x_4349_ = v___x_4337_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
else
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
lean_inc(v_name_4340_);
lean_dec(v_a_4335_);
lean_dec_ref_known(v_entry_4333_, 3);
lean_dec_ref(v_env_4328_);
v___x_4351_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4340_, v___x_4341_);
v___x_4353_ = lean_string_append(v___x_4351_, v___x_4352_);
lean_dec_ref(v___x_4352_);
v___x_4354_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4355_ = lean_string_append(v___x_4353_, v___x_4354_);
v___x_4356_ = lean_mk_io_user_error(v___x_4355_);
if (v_isShared_4338_ == 0)
{
lean_ctor_set_tag(v___x_4337_, 1);
lean_ctor_set(v___x_4337_, 0, v___x_4356_);
v___x_4358_ = v___x_4337_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4356_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec_ref_known(v_entry_4333_, 3);
lean_dec_ref(v_env_4328_);
v_a_4361_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4334_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4334_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4369_, lean_object* v_builderId_4370_, lean_object* v_ref_4371_, lean_object* v_args_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_registerAttributeOfBuilder(v_env_4369_, v_builderId_4370_, v_ref_4371_, v_args_4372_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
if (lean_obj_tag(v_x_4375_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v_a_4379_ = lean_ctor_get(v_x_4375_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v_x_4375_, 1);
v___x_4380_ = l_Lean_stringToMessageData(v_a_4379_);
v___x_4381_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4380_, v___y_4376_, v___y_4377_);
return v___x_4381_;
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
v_a_4382_ = lean_ctor_get(v_x_4375_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_x_4375_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v_x_4375_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v_x_4375_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4395_, lean_object* v_attrName_4396_, lean_object* v_stx_4397_, uint8_t v_kind_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v_env_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4402_ = lean_st_ref_get(v_a_4400_);
v_env_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc_ref(v_env_4403_);
lean_dec(v___x_4402_);
v___x_4404_ = l_Lean_getAttributeImpl(v_env_4403_, v_attrName_4396_);
v___x_4405_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4404_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v_add_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v_add_4407_ = lean_ctor_get(v_a_4406_, 1);
lean_inc_ref(v_add_4407_);
lean_dec(v_a_4406_);
v___x_4408_ = lean_box(v_kind_4398_);
lean_inc(v_a_4400_);
lean_inc_ref(v_a_4399_);
v___x_4409_ = lean_apply_6(v_add_4407_, v_declName_4395_, v_stx_4397_, v___x_4408_, v_a_4399_, v_a_4400_, lean_box(0));
return v___x_4409_;
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_stx_4397_);
lean_dec(v_declName_4395_);
v_a_4410_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4405_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4405_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4418_, lean_object* v_attrName_4419_, lean_object* v_stx_4420_, lean_object* v_kind_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
uint8_t v_kind_boxed_4425_; lean_object* v_res_4426_; 
v_kind_boxed_4425_ = lean_unbox(v_kind_4421_);
v_res_4426_ = l_Lean_Attribute_add(v_declName_4418_, v_attrName_4419_, v_stx_4420_, v_kind_boxed_4425_, v_a_4422_, v_a_4423_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4427_, lean_object* v_x_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4428_, v___y_4429_, v___y_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4433_, lean_object* v_x_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4433_, v_x_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4439_, lean_object* v_attrName_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v___x_4444_; lean_object* v_env_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4444_ = lean_st_ref_get(v_a_4442_);
v_env_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc_ref(v_env_4445_);
lean_dec(v___x_4444_);
v___x_4446_ = l_Lean_getAttributeImpl(v_env_4445_, v_attrName_4440_);
v___x_4447_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4446_, v_a_4441_, v_a_4442_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v_erase_4449_; lean_object* v___x_4450_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v_erase_4449_ = lean_ctor_get(v_a_4448_, 2);
lean_inc_ref(v_erase_4449_);
lean_dec(v_a_4448_);
lean_inc(v_a_4442_);
lean_inc_ref(v_a_4441_);
v___x_4450_ = lean_apply_4(v_erase_4449_, v_declName_4439_, v_a_4441_, v_a_4442_, lean_box(0));
return v___x_4450_;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_declName_4439_);
v_a_4451_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4447_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4447_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4459_, lean_object* v_attrName_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_Attribute_erase(v_declName_4459_, v_attrName_4460_, v_a_4461_, v_a_4462_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4465_, lean_object* v_x_4466_){
_start:
{
if (lean_obj_tag(v_x_4466_) == 0)
{
return v_x_4465_;
}
else
{
lean_object* v_key_4467_; lean_object* v_value_4468_; lean_object* v_tail_4469_; lean_object* v_newEntries_4470_; lean_object* v_map_4471_; uint8_t v___x_4472_; 
v_key_4467_ = lean_ctor_get(v_x_4466_, 0);
lean_inc(v_key_4467_);
v_value_4468_ = lean_ctor_get(v_x_4466_, 1);
lean_inc(v_value_4468_);
v_tail_4469_ = lean_ctor_get(v_x_4466_, 2);
lean_inc(v_tail_4469_);
lean_dec_ref_known(v_x_4466_, 3);
v_newEntries_4470_ = lean_ctor_get(v_x_4465_, 0);
v_map_4471_ = lean_ctor_get(v_x_4465_, 1);
v___x_4472_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4471_, v_key_4467_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4481_; 
lean_inc_ref(v_map_4471_);
lean_inc(v_newEntries_4470_);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_x_4465_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; lean_object* v_unused_4483_; 
v_unused_4482_ = lean_ctor_get(v_x_4465_, 1);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_x_4465_, 0);
lean_dec(v_unused_4483_);
v___x_4474_ = v_x_4465_;
v_isShared_4475_ = v_isSharedCheck_4481_;
goto v_resetjp_4473_;
}
else
{
lean_dec(v_x_4465_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4481_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4476_; lean_object* v___x_4478_; 
v___x_4476_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4471_, v_key_4467_, v_value_4468_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 1, v___x_4476_);
v___x_4478_ = v___x_4474_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_newEntries_4470_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
v_x_4465_ = v___x_4478_;
v_x_4466_ = v_tail_4469_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4468_);
lean_dec(v_key_4467_);
v_x_4466_ = v_tail_4469_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4485_, size_t v_i_4486_, size_t v_stop_4487_, lean_object* v_b_4488_){
_start:
{
uint8_t v___x_4489_; 
v___x_4489_ = lean_usize_dec_eq(v_i_4486_, v_stop_4487_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4491_; size_t v___x_4492_; size_t v___x_4493_; 
v___x_4490_ = lean_array_uget_borrowed(v_as_4485_, v_i_4486_);
lean_inc(v___x_4490_);
v___x_4491_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4488_, v___x_4490_);
v___x_4492_ = ((size_t)1ULL);
v___x_4493_ = lean_usize_add(v_i_4486_, v___x_4492_);
v_i_4486_ = v___x_4493_;
v_b_4488_ = v___x_4491_;
goto _start;
}
else
{
return v_b_4488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4495_, lean_object* v_i_4496_, lean_object* v_stop_4497_, lean_object* v_b_4498_){
_start:
{
size_t v_i_boxed_4499_; size_t v_stop_boxed_4500_; lean_object* v_res_4501_; 
v_i_boxed_4499_ = lean_unbox_usize(v_i_4496_);
lean_dec(v_i_4496_);
v_stop_boxed_4500_ = lean_unbox_usize(v_stop_4497_);
lean_dec(v_stop_4497_);
v_res_4501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4495_, v_i_boxed_4499_, v_stop_boxed_4500_, v_b_4498_);
lean_dec_ref(v_as_4495_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4502_){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___y_4508_; lean_object* v_toEnvExtension_4511_; lean_object* v_asyncMode_4512_; lean_object* v_buckets_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4504_ = l_Lean_attributeMapRef;
v___x_4505_ = lean_st_ref_get(v___x_4504_);
v___x_4506_ = l_Lean_attributeExtension;
v_toEnvExtension_4511_ = lean_ctor_get(v___x_4506_, 0);
v_asyncMode_4512_ = lean_ctor_get(v_toEnvExtension_4511_, 2);
v_buckets_4513_ = lean_ctor_get(v___x_4505_, 1);
lean_inc_ref(v_buckets_4513_);
lean_dec(v___x_4505_);
v___x_4514_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4515_ = lean_box(0);
lean_inc_ref(v_env_4502_);
v___x_4516_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4514_, v___x_4506_, v_env_4502_, v_asyncMode_4512_, v___x_4515_);
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = lean_array_get_size(v_buckets_4513_);
v___x_4519_ = lean_nat_dec_lt(v___x_4517_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_dec_ref(v_buckets_4513_);
v___y_4508_ = v___x_4516_;
goto v___jp_4507_;
}
else
{
size_t v___x_4520_; size_t v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = ((size_t)0ULL);
v___x_4521_ = lean_usize_of_nat(v___x_4518_);
v___x_4522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4513_, v___x_4520_, v___x_4521_, v___x_4516_);
lean_dec_ref(v_buckets_4513_);
v___y_4508_ = v___x_4522_;
goto v___jp_4507_;
}
v___jp_4507_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4509_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4506_, v_env_4502_, v___y_4508_);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = lean_update_env_attributes(v_env_4523_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v_size_4529_; lean_object* v___x_4530_; 
v___x_4527_ = l_Lean_attributeMapRef;
v___x_4528_ = lean_st_ref_get(v___x_4527_);
v_size_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_size_4529_);
lean_dec(v___x_4528_);
v___x_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4530_, 0, v_size_4529_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = lean_get_num_attributes();
return v_res_4532_;
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
