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
uint8_t v___y_1012__boxed_312_; lean_object* v_res_313_; 
v___y_1012__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_1012__boxed_312_, v___y_309_, v___y_310_);
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
v___x_1163_ = lean_st_ref_put(v___y_1143_, v___x_1162_);
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
lean_object* v___x_1186_; lean_object* v_env_1187_; lean_object* v___x_1188_; uint8_t v_isModule_1189_; 
v___x_1186_ = lean_st_ref_get(v___y_1184_);
v_env_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc_ref(v_env_1187_);
lean_dec(v___x_1186_);
v___x_1188_ = l_Lean_Environment_header(v_env_1187_);
v_isModule_1189_ = lean_ctor_get_uint8(v___x_1188_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1188_);
if (v_isModule_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_env_1187_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1190_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1190_;
}
else
{
uint8_t v_isExporting_1191_; 
v_isExporting_1191_ = lean_ctor_get_uint8(v_env_1187_, sizeof(void*)*8);
lean_dec_ref(v_env_1187_);
if (v_isExporting_1182_ == 0)
{
if (v_isExporting_1191_ == 0)
{
lean_object* v___x_1242_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1242_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1242_;
}
else
{
goto v___jp_1192_;
}
}
else
{
if (v_isExporting_1191_ == 0)
{
goto v___jp_1192_;
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
v___jp_1192_:
{
lean_object* v___x_1193_; lean_object* v_env_1194_; lean_object* v_nextMacroScope_1195_; lean_object* v_ngen_1196_; lean_object* v_auxDeclNGen_1197_; lean_object* v_traceState_1198_; lean_object* v_messages_1199_; lean_object* v_infoState_1200_; lean_object* v_snapshotTasks_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1240_; 
v___x_1193_ = lean_st_ref_take(v___y_1184_);
v_env_1194_ = lean_ctor_get(v___x_1193_, 0);
v_nextMacroScope_1195_ = lean_ctor_get(v___x_1193_, 1);
v_ngen_1196_ = lean_ctor_get(v___x_1193_, 2);
v_auxDeclNGen_1197_ = lean_ctor_get(v___x_1193_, 3);
v_traceState_1198_ = lean_ctor_get(v___x_1193_, 4);
v_messages_1199_ = lean_ctor_get(v___x_1193_, 6);
v_infoState_1200_ = lean_ctor_get(v___x_1193_, 7);
v_snapshotTasks_1201_ = lean_ctor_get(v___x_1193_, 8);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v___x_1193_, 5);
lean_dec(v_unused_1241_);
v___x_1203_ = v___x_1193_;
v_isShared_1204_ = v_isSharedCheck_1240_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snapshotTasks_1201_);
lean_inc(v_infoState_1200_);
lean_inc(v_messages_1199_);
lean_inc(v_traceState_1198_);
lean_inc(v_auxDeclNGen_1197_);
lean_inc(v_ngen_1196_);
lean_inc(v_nextMacroScope_1195_);
lean_inc(v_env_1194_);
lean_dec(v___x_1193_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1240_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1205_ = l_Lean_Environment_setExporting(v_env_1194_, v_isExporting_1182_);
v___x_1206_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 5, v___x_1206_);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_nextMacroScope_1195_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_ngen_1196_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_auxDeclNGen_1197_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_traceState_1198_);
lean_ctor_set(v_reuseFailAlloc_1239_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1239_, 6, v_messages_1199_);
lean_ctor_set(v_reuseFailAlloc_1239_, 7, v_infoState_1200_);
lean_ctor_set(v_reuseFailAlloc_1239_, 8, v_snapshotTasks_1201_);
v___x_1208_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v_r_1210_; 
v___x_1209_ = lean_st_ref_put(v___y_1184_, v___x_1208_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v_r_1210_ = lean_apply_3(v_x_1181_, v___y_1183_, v___y_1184_, lean_box(0));
if (lean_obj_tag(v_r_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1227_; 
v_a_1211_ = lean_ctor_get(v_r_1210_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_r_1210_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1213_ = v_r_1210_;
v_isShared_1214_ = v_isSharedCheck_1227_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v_r_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1227_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
lean_inc(v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v___x_1217_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1184_, v_isExporting_1191_, v___x_1206_, v___x_1216_);
lean_dec_ref(v___x_1216_);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1225_);
v___x_1219_ = v___x_1217_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v___x_1217_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v_a_1211_);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1211_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_a_1228_ = lean_ctor_get(v_r_1210_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v_r_1210_, 1);
v___x_1229_ = lean_box(0);
v___x_1230_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1184_, v_isExporting_1191_, v___x_1206_, v___x_1229_);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1230_, 0);
lean_dec(v_unused_1238_);
v___x_1232_ = v___x_1230_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v___x_1230_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set_tag(v___x_1232_, 1);
lean_ctor_set(v___x_1232_, 0, v_a_1228_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1228_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1287_, uint8_t v___y_1288_, lean_object* v_x_1289_){
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
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1299_ = lean_string_dec_eq(v_str_1292_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___x_1299_;
}
else
{
return v_suppressElabErrors_1287_;
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
return v___x_1301_;
}
else
{
return v_suppressElabErrors_1287_;
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
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1309_ = lean_string_dec_eq(v_str_1304_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1311_ = lean_string_dec_eq(v_str_1303_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___x_1311_;
}
else
{
return v_suppressElabErrors_1287_;
}
}
}
}
else
{
return v___y_1288_;
}
}
default: 
{
return v___y_1288_;
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
return v___x_1314_;
}
else
{
return v_suppressElabErrors_1287_;
}
}
default: 
{
return v___y_1288_;
}
}
}
else
{
return v___y_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1315_, lean_object* v___y_1316_, lean_object* v_x_1317_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1318_; uint8_t v___y_4969__boxed_1319_; uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_suppressElabErrors_boxed_1318_ = lean_unbox(v_suppressElabErrors_1315_);
v___y_4969__boxed_1319_ = lean_unbox(v___y_1316_);
v_res_1320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1318_, v___y_4969__boxed_1319_, v_x_1317_);
lean_dec(v_x_1317_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1322_, lean_object* v_msgData_1323_, uint8_t v_severity_1324_, uint8_t v_isSilent_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; uint8_t v___x_1413_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1421_; uint8_t v___y_1423_; uint8_t v___x_1438_; 
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
lean_ctor_set(v___x_1355_, 1, v___y_1336_);
lean_inc_ref(v___y_1334_);
lean_inc_ref(v___y_1331_);
v___x_1356_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1356_, 0, v___y_1331_);
lean_ctor_set(v___x_1356_, 1, v___y_1335_);
lean_ctor_set(v___x_1356_, 2, v___y_1333_);
lean_ctor_set(v___x_1356_, 3, v___y_1334_);
lean_ctor_set(v___x_1356_, 4, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*5, v___y_1332_);
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
v___x_1360_ = lean_st_ref_put(v___y_1338_, v___x_1359_);
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
lean_inc_ref_n(v___y_1367_, 2);
v___x_1380_ = l_Lean_FileMap_toPosition(v___y_1367_, v___y_1369_);
lean_dec(v___y_1369_);
v___x_1381_ = l_Lean_FileMap_toPosition(v___y_1367_, v___y_1373_);
lean_dec(v___y_1373_);
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1368_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v___y_1366_);
v___y_1330_ = v___y_1370_;
v___y_1331_ = v___y_1371_;
v___y_1332_ = v___y_1372_;
v___y_1333_ = v___x_1382_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v___x_1380_;
v___y_1336_ = v_a_1376_;
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
v___y_1330_ = v___y_1370_;
v___y_1331_ = v___y_1371_;
v___y_1332_ = v___y_1372_;
v___y_1333_ = v___x_1382_;
v___y_1334_ = v___x_1383_;
v___y_1335_ = v___x_1380_;
v___y_1336_ = v_a_1376_;
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
v___x_1399_ = l_Lean_Syntax_getTailPos_x3f(v___y_1397_, v___y_1396_);
lean_dec(v___y_1397_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_inc(v___y_1398_);
v___y_1366_ = v___y_1391_;
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1398_;
v___y_1370_ = v___y_1394_;
v___y_1371_ = v___y_1395_;
v___y_1372_ = v___y_1396_;
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
v___y_1367_ = v___y_1392_;
v___y_1368_ = v___y_1393_;
v___y_1369_ = v___y_1398_;
v___y_1370_ = v___y_1394_;
v___y_1371_ = v___y_1395_;
v___y_1372_ = v___y_1396_;
v___y_1373_ = v_val_1400_;
goto v___jp_1365_;
}
}
v___jp_1401_:
{
lean_object* v_ref_1409_; lean_object* v___x_1410_; 
v_ref_1409_ = l_Lean_replaceRef(v_ref_1322_, v___y_1403_);
v___x_1410_ = l_Lean_Syntax_getPos_x3f(v_ref_1409_, v___y_1407_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___y_1391_ = v___y_1402_;
v___y_1392_ = v___y_1404_;
v___y_1393_ = v___y_1405_;
v___y_1394_ = v___y_1408_;
v___y_1395_ = v___y_1406_;
v___y_1396_ = v___y_1407_;
v___y_1397_ = v_ref_1409_;
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
v___y_1392_ = v___y_1404_;
v___y_1393_ = v___y_1405_;
v___y_1394_ = v___y_1408_;
v___y_1395_ = v___y_1406_;
v___y_1396_ = v___y_1407_;
v___y_1397_ = v_ref_1409_;
v___y_1398_ = v_val_1412_;
goto v___jp_1390_;
}
}
v___jp_1414_:
{
if (v___y_1421_ == 0)
{
v___y_1402_ = v___y_1416_;
v___y_1403_ = v___y_1415_;
v___y_1404_ = v___y_1417_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v_severity_1324_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___y_1416_;
v___y_1403_ = v___y_1415_;
v___y_1404_ = v___y_1417_;
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1419_;
v___y_1407_ = v___y_1420_;
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
v___x_1429_ = lean_box(v_suppressElabErrors_1428_);
v___x_1430_ = lean_box(v___y_1423_);
v___f_1431_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1431_, 0, v___x_1429_);
lean_closure_set(v___f_1431_, 1, v___x_1430_);
v___x_1432_ = 1;
v___x_1433_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1324_, v___x_1432_);
if (v___x_1433_ == 0)
{
v___y_1415_ = v_ref_1427_;
v___y_1416_ = v___f_1431_;
v___y_1417_ = v_fileMap_1425_;
v___y_1418_ = v_suppressElabErrors_1428_;
v___y_1419_ = v_fileName_1424_;
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
v___y_1416_ = v___f_1431_;
v___y_1417_ = v_fileMap_1425_;
v___y_1418_ = v_suppressElabErrors_1428_;
v___y_1419_ = v_fileName_1424_;
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
v___x_2017_ = lean_st_ref_put(v___y_1994_, v___x_2016_);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2287_, lean_object* v_as_2288_, lean_object* v_k_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v_m_2294_; lean_object* v_a_2295_; uint8_t v___x_2296_; 
v___x_2292_ = lean_nat_add(v_x_2290_, v_x_2291_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v_m_2294_ = lean_nat_shiftr(v___x_2292_, v___x_2293_);
lean_dec(v___x_2292_);
v_a_2295_ = lean_array_fget_borrowed(v_as_2288_, v_m_2294_);
v___x_2296_ = l_Lean_Name_quickLt(v_a_2295_, v_k_2289_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
lean_dec(v_x_2291_);
v___x_2297_ = lean_unsigned_to_nat(0u);
v___x_2298_ = l_Lean_Name_quickLt(v_k_2289_, v_a_2295_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; 
lean_dec(v_m_2294_);
lean_dec(v_x_2290_);
v___x_2299_ = lean_nat_dec_le(v___x_2297_, v___y_2287_);
return v___x_2299_;
}
else
{
uint8_t v___x_2300_; lean_object* v___x_2301_; uint8_t v___y_2303_; 
v___x_2300_ = lean_nat_dec_eq(v_m_2294_, v___x_2297_);
v___x_2301_ = lean_nat_sub(v_m_2294_, v___x_2293_);
lean_dec(v_m_2294_);
if (v___x_2300_ == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_nat_dec_lt(v___x_2301_, v_x_2290_);
v___y_2303_ = v___x_2305_;
goto v___jp_2302_;
}
else
{
v___y_2303_ = v___x_2300_;
goto v___jp_2302_;
}
v___jp_2302_:
{
if (v___y_2303_ == 0)
{
v_x_2291_ = v___x_2301_;
goto _start;
}
else
{
lean_dec(v___x_2301_);
lean_dec(v_x_2290_);
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2306_; uint8_t v___x_2307_; 
lean_dec(v_x_2290_);
v___x_2306_ = lean_nat_add(v_m_2294_, v___x_2293_);
lean_dec(v_m_2294_);
v___x_2307_ = lean_nat_dec_le(v___x_2306_, v_x_2291_);
if (v___x_2307_ == 0)
{
lean_dec(v___x_2306_);
lean_dec(v_x_2291_);
return v___x_2307_;
}
else
{
v_x_2290_ = v___x_2306_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2309_, lean_object* v_as_2310_, lean_object* v_k_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2309_, v_as_2310_, v_k_2311_, v_x_2312_, v_x_2313_);
lean_dec(v_k_2311_);
lean_dec_ref(v_as_2310_);
lean_dec(v___y_2309_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2316_, lean_object* v_env_2317_, lean_object* v_decl_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_box(1);
v___x_2320_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2317_, v_decl_2318_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_ext_2321_; lean_object* v_toEnvExtension_2322_; lean_object* v_asyncMode_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; 
v_ext_2321_ = lean_ctor_get(v_attr_2316_, 1);
v_toEnvExtension_2322_ = lean_ctor_get(v_ext_2321_, 0);
v_asyncMode_2323_ = lean_ctor_get(v_toEnvExtension_2322_, 2);
lean_inc(v_decl_2318_);
v___x_2324_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2319_, v_ext_2321_, v_env_2317_, v_asyncMode_2323_, v_decl_2318_);
v___x_2325_ = l_Lean_NameSet_contains(v___x_2324_, v_decl_2318_);
lean_dec(v_decl_2318_);
lean_dec(v___x_2324_);
return v___x_2325_;
}
else
{
lean_object* v_val_2326_; lean_object* v_ext_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_val_2326_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_val_2326_);
lean_dec_ref_known(v___x_2320_, 1);
v_ext_2327_ = lean_ctor_get(v_attr_2316_, 1);
v___x_2328_ = 0;
v___x_2329_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2319_, v_ext_2327_, v_env_2317_, v_val_2326_, v___x_2328_);
lean_dec(v_val_2326_);
lean_dec_ref(v_env_2317_);
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = lean_array_get_size(v___x_2329_);
v___x_2332_ = lean_nat_dec_lt(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_dec_ref(v___x_2329_);
lean_dec(v_decl_2318_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_sub(v___x_2331_, v___x_2333_);
v___x_2335_ = lean_nat_dec_le(v___x_2330_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_dec(v___x_2334_);
lean_dec_ref(v___x_2329_);
lean_dec(v_decl_2318_);
return v___x_2335_;
}
else
{
uint8_t v___x_2336_; 
lean_inc(v___x_2334_);
v___x_2336_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2334_, v___x_2329_, v_decl_2318_, v___x_2330_, v___x_2334_);
lean_dec(v_decl_2318_);
lean_dec_ref(v___x_2329_);
lean_dec(v___x_2334_);
return v___x_2336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2337_, lean_object* v_env_2338_, lean_object* v_decl_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_Lean_TagAttribute_hasTag(v_attr_2337_, v_env_2338_, v_decl_2339_);
lean_dec_ref(v_attr_2337_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2342_, lean_object* v_as_2343_, lean_object* v_k_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2342_, v_as_2343_, v_k_2344_, v_x_2345_, v_x_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2349_, lean_object* v_as_2350_, lean_object* v_k_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
uint8_t v_res_2355_; lean_object* v_r_2356_; 
v_res_2355_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2349_, v_as_2350_, v_k_2351_, v_x_2352_, v_x_2353_, v_x_2354_);
lean_dec(v_k_2351_);
lean_dec_ref(v_as_2350_);
lean_dec(v___y_2349_);
v_r_2356_ = lean_box(v_res_2355_);
return v_r_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2362_, v___y_2363_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_x_2362_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2366_, lean_object* v_x_2367_){
_start:
{
lean_inc_ref(v_s_2366_);
return v_s_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2368_, lean_object* v_x_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2368_, v_x_2369_);
lean_dec_ref(v_x_2369_);
lean_dec_ref(v_s_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2378_, v_x_2379_);
lean_dec_ref(v_x_2379_);
lean_dec_ref(v_x_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_box(0);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2383_);
lean_dec_ref(v_x_2383_);
return v_res_2384_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2390_; lean_object* v___f_2391_; lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___f_2390_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2391_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2392_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2393_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2394_ = lean_box(0);
v___x_2395_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2394_);
lean_ctor_set(v___x_2396_, 2, v___f_2393_);
lean_ctor_set(v___x_2396_, 3, v___f_2392_);
lean_ctor_set(v___x_2396_, 4, v___f_2391_);
lean_ctor_set(v___x_2396_, 5, v___f_2390_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = 0;
v___x_2398_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2399_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2400_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
lean_ctor_set(v___x_2400_, 1, v___x_2398_);
lean_ctor_set_uint8(v___x_2400_, sizeof(void*)*2, v___x_2397_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2406_, lean_object* v_p_2407_){
_start:
{
lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2426_; 
v_fst_2408_ = lean_ctor_get(v_x_2406_, 0);
v_snd_2409_ = lean_ctor_get(v_x_2406_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2406_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2411_ = v_x_2406_;
v_isShared_2412_ = v_isSharedCheck_2426_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_snd_2409_);
lean_inc(v_fst_2408_);
lean_dec(v_x_2406_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2426_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2425_; 
v_fst_2413_ = lean_ctor_get(v_p_2407_, 0);
v_snd_2414_ = lean_ctor_get(v_p_2407_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_p_2407_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2416_ = v_p_2407_;
v_isShared_2417_ = v_isSharedCheck_2425_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snd_2414_);
lean_inc(v_fst_2413_);
lean_dec(v_p_2407_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2425_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
lean_inc(v_fst_2413_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 1);
lean_ctor_set(v___x_2411_, 1, v_fst_2408_);
lean_ctor_set(v___x_2411_, 0, v_fst_2413_);
v___x_2419_ = v___x_2411_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_fst_2413_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_fst_2408_);
v___x_2419_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2413_, v_snd_2414_, v_snd_2409_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2420_);
lean_ctor_set(v___x_2416_, 0, v___x_2419_);
v___x_2422_ = v___x_2416_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_k_2429_ = lean_ctor_get(v_x_2428_, 1);
v_v_2430_ = lean_ctor_get(v_x_2428_, 2);
v_l_2431_ = lean_ctor_get(v_x_2428_, 3);
v_r_2432_ = lean_ctor_get(v_x_2428_, 4);
v___x_2433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2427_, v_l_2431_);
lean_inc(v_v_2430_);
lean_inc(v_k_2429_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_k_2429_);
lean_ctor_set(v___x_2434_, 1, v_v_2430_);
v___x_2435_ = lean_array_push(v___x_2433_, v___x_2434_);
v_init_2427_ = v___x_2435_;
v_x_2428_ = v_r_2432_;
goto _start;
}
else
{
return v_init_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2437_, lean_object* v_x_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2437_, v_x_2438_);
lean_dec(v_x_2438_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2440_, lean_object* v_as_2441_, size_t v_i_2442_, size_t v_stop_2443_, lean_object* v_b_2444_){
_start:
{
lean_object* v___y_2446_; uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_eq(v_i_2442_, v_stop_2443_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_array_uget_borrowed(v_as_2441_, v_i_2442_);
v___x_2452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2440_, v___x_2451_);
if (lean_obj_tag(v___x_2452_) == 0)
{
v___y_2446_ = v_b_2444_;
goto v___jp_2445_;
}
else
{
lean_object* v_val_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_val_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v___x_2452_, 1);
lean_inc(v___x_2451_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2451_);
lean_ctor_set(v___x_2454_, 1, v_val_2453_);
v___x_2455_ = lean_array_push(v_b_2444_, v___x_2454_);
v___y_2446_ = v___x_2455_;
goto v___jp_2445_;
}
}
else
{
return v_b_2444_;
}
v___jp_2445_:
{
size_t v___x_2447_; size_t v___x_2448_; 
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_add(v_i_2442_, v___x_2447_);
v_i_2442_ = v___x_2448_;
v_b_2444_ = v___y_2446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2456_, lean_object* v_as_2457_, lean_object* v_i_2458_, lean_object* v_stop_2459_, lean_object* v_b_2460_){
_start:
{
size_t v_i_boxed_2461_; size_t v_stop_boxed_2462_; lean_object* v_res_2463_; 
v_i_boxed_2461_ = lean_unbox_usize(v_i_2458_);
lean_dec(v_i_2458_);
v_stop_boxed_2462_ = lean_unbox_usize(v_stop_2459_);
lean_dec(v_stop_2459_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2456_, v_as_2457_, v_i_boxed_2461_, v_stop_boxed_2462_, v_b_2460_);
lean_dec_ref(v_as_2457_);
lean_dec(v_snd_2456_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2464_, lean_object* v_as_2465_, lean_object* v_start_2466_, lean_object* v_stop_2467_){
_start:
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2469_ = lean_nat_dec_lt(v_start_2466_, v_stop_2467_);
if (v___x_2469_ == 0)
{
return v___x_2468_;
}
else
{
lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2470_ = lean_array_get_size(v_as_2465_);
v___x_2471_ = lean_nat_dec_le(v_stop_2467_, v___x_2470_);
if (v___x_2471_ == 0)
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_nat_dec_lt(v_start_2466_, v___x_2470_);
if (v___x_2472_ == 0)
{
return v___x_2468_;
}
else
{
size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_usize_of_nat(v_start_2466_);
v___x_2474_ = lean_usize_of_nat(v___x_2470_);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2464_, v_as_2465_, v___x_2473_, v___x_2474_, v___x_2468_);
return v___x_2475_;
}
}
else
{
size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_usize_of_nat(v_start_2466_);
v___x_2477_ = lean_usize_of_nat(v_stop_2467_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2464_, v_as_2465_, v___x_2476_, v___x_2477_, v___x_2468_);
return v___x_2478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2479_, lean_object* v_as_2480_, lean_object* v_start_2481_, lean_object* v_stop_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2479_, v_as_2480_, v_start_2481_, v_stop_2482_);
lean_dec(v_stop_2482_);
lean_dec(v_start_2481_);
lean_dec_ref(v_as_2480_);
lean_dec(v_snd_2479_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2484_, lean_object* v_pivot_2485_, lean_object* v_as_2486_, lean_object* v_i_2487_, lean_object* v_k_2488_){
_start:
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_nat_dec_lt(v_k_2488_, v_hi_2484_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_k_2488_);
v___x_2490_ = lean_array_fswap(v_as_2486_, v_i_2487_, v_hi_2484_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_i_2487_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v_fst_2493_; lean_object* v_fst_2494_; uint8_t v___x_2495_; 
v___x_2492_ = lean_array_fget_borrowed(v_as_2486_, v_k_2488_);
v_fst_2493_ = lean_ctor_get(v___x_2492_, 0);
v_fst_2494_ = lean_ctor_get(v_pivot_2485_, 0);
v___x_2495_ = l_Lean_Name_quickLt(v_fst_2493_, v_fst_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = lean_nat_add(v_k_2488_, v___x_2496_);
lean_dec(v_k_2488_);
v_k_2488_ = v___x_2497_;
goto _start;
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = lean_array_fswap(v_as_2486_, v_i_2487_, v_k_2488_);
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_nat_add(v_i_2487_, v___x_2500_);
lean_dec(v_i_2487_);
v___x_2502_ = lean_nat_add(v_k_2488_, v___x_2500_);
lean_dec(v_k_2488_);
v_as_2486_ = v___x_2499_;
v_i_2487_ = v___x_2501_;
v_k_2488_ = v___x_2502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2504_, lean_object* v_pivot_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_k_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2504_, v_pivot_2505_, v_as_2506_, v_i_2507_, v_k_2508_);
lean_dec_ref(v_pivot_2505_);
lean_dec(v_hi_2504_);
return v_res_2509_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2510_, lean_object* v_b_2511_){
_start:
{
lean_object* v_fst_2512_; lean_object* v_fst_2513_; uint8_t v___x_2514_; 
v_fst_2512_ = lean_ctor_get(v_a_2510_, 0);
v_fst_2513_ = lean_ctor_get(v_b_2511_, 0);
v___x_2514_ = l_Lean_Name_quickLt(v_fst_2512_, v_fst_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2515_, lean_object* v_b_2516_){
_start:
{
uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_res_2517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2515_, v_b_2516_);
lean_dec_ref(v_b_2516_);
lean_dec_ref(v_a_2515_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2519_, lean_object* v_as_2520_, lean_object* v_lo_2521_, lean_object* v_hi_2522_){
_start:
{
lean_object* v___y_2524_; uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_lt(v_lo_2521_, v_hi_2522_);
if (v___x_2534_ == 0)
{
lean_dec(v_lo_2521_);
return v_as_2520_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_mid_2537_; lean_object* v___y_2539_; lean_object* v___y_2545_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2535_ = lean_nat_add(v_lo_2521_, v_hi_2522_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v_mid_2537_ = lean_nat_shiftr(v___x_2535_, v___x_2536_);
lean_dec(v___x_2535_);
v___x_2550_ = lean_array_fget_borrowed(v_as_2520_, v_mid_2537_);
v___x_2551_ = lean_array_fget_borrowed(v_as_2520_, v_lo_2521_);
v___x_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
v___y_2545_ = v_as_2520_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_array_fswap(v_as_2520_, v_lo_2521_, v_mid_2537_);
v___y_2545_ = v___x_2553_;
goto v___jp_2544_;
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2540_ = lean_array_fget_borrowed(v___y_2539_, v_mid_2537_);
v___x_2541_ = lean_array_fget_borrowed(v___y_2539_, v_hi_2522_);
v___x_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec(v_mid_2537_);
v___y_2524_ = v___y_2539_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_fswap(v___y_2539_, v_mid_2537_, v_hi_2522_);
lean_dec(v_mid_2537_);
v___y_2524_ = v___x_2543_;
goto v___jp_2523_;
}
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2546_ = lean_array_fget_borrowed(v___y_2545_, v_hi_2522_);
v___x_2547_ = lean_array_fget_borrowed(v___y_2545_, v_lo_2521_);
v___x_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
v___y_2539_ = v___y_2545_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_array_fswap(v___y_2545_, v_lo_2521_, v_hi_2522_);
v___y_2539_ = v___x_2549_;
goto v___jp_2538_;
}
}
}
v___jp_2523_:
{
lean_object* v_pivot_2525_; lean_object* v___x_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; uint8_t v___x_2529_; 
v_pivot_2525_ = lean_array_fget(v___y_2524_, v_hi_2522_);
lean_inc_n(v_lo_2521_, 2);
v___x_2526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2522_, v_pivot_2525_, v___y_2524_, v_lo_2521_, v_lo_2521_);
lean_dec(v_pivot_2525_);
v_fst_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_fst_2527_);
v_snd_2528_ = lean_ctor_get(v___x_2526_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v___x_2526_);
v___x_2529_ = lean_nat_dec_le(v_hi_2522_, v_fst_2527_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2519_, v_snd_2528_, v_lo_2521_, v_fst_2527_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_add(v_fst_2527_, v___x_2531_);
lean_dec(v_fst_2527_);
v_as_2520_ = v___x_2530_;
v_lo_2521_ = v___x_2532_;
goto _start;
}
else
{
lean_dec(v_fst_2527_);
lean_dec(v_lo_2521_);
return v_snd_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2554_, lean_object* v_as_2555_, lean_object* v_lo_2556_, lean_object* v_hi_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2554_, v_as_2555_, v_lo_2556_, v_hi_2557_);
lean_dec(v_hi_2557_);
lean_dec(v_n_2554_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2559_, lean_object* v_env_2560_, lean_object* v_as_2561_, size_t v_i_2562_, size_t v_stop_2563_, lean_object* v_b_2564_){
_start:
{
lean_object* v___y_2566_; uint8_t v___x_2570_; 
v___x_2570_ = lean_usize_dec_eq(v_i_2562_, v_stop_2563_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2571_ = lean_array_uget_borrowed(v_as_2561_, v_i_2562_);
v_fst_2572_ = lean_ctor_get(v___x_2571_, 0);
v_snd_2573_ = lean_ctor_get(v___x_2571_, 1);
lean_inc_ref(v_filterExport_2559_);
lean_inc(v_snd_2573_);
lean_inc(v_fst_2572_);
lean_inc_ref(v_env_2560_);
v___x_2574_ = lean_apply_3(v_filterExport_2559_, v_env_2560_, v_fst_2572_, v_snd_2573_);
v___x_2575_ = lean_unbox(v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2566_ = v_b_2564_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2576_; 
lean_inc(v___x_2571_);
v___x_2576_ = lean_array_push(v_b_2564_, v___x_2571_);
v___y_2566_ = v___x_2576_;
goto v___jp_2565_;
}
}
else
{
lean_dec_ref(v_env_2560_);
lean_dec_ref(v_filterExport_2559_);
return v_b_2564_;
}
v___jp_2565_:
{
size_t v___x_2567_; size_t v___x_2568_; 
v___x_2567_ = ((size_t)1ULL);
v___x_2568_ = lean_usize_add(v_i_2562_, v___x_2567_);
v_i_2562_ = v___x_2568_;
v_b_2564_ = v___y_2566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2577_, lean_object* v_env_2578_, lean_object* v_as_2579_, lean_object* v_i_2580_, lean_object* v_stop_2581_, lean_object* v_b_2582_){
_start:
{
size_t v_i_boxed_2583_; size_t v_stop_boxed_2584_; lean_object* v_res_2585_; 
v_i_boxed_2583_ = lean_unbox_usize(v_i_2580_);
lean_dec(v_i_2580_);
v_stop_boxed_2584_ = lean_unbox_usize(v_stop_2581_);
lean_dec(v_stop_2581_);
v_res_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2577_, v_env_2578_, v_as_2579_, v_i_boxed_2583_, v_stop_boxed_2584_, v_b_2582_);
lean_dec_ref(v_as_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2586_, uint8_t v_preserveOrder_2587_, lean_object* v_env_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v___y_2591_; 
if (v_preserveOrder_2587_ == 0)
{
lean_object* v_snd_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_r_2610_; lean_object* v___x_2611_; lean_object* v___y_2613_; lean_object* v___y_2614_; uint8_t v___x_2616_; 
v_snd_2607_ = lean_ctor_get(v_x_2589_, 1);
lean_inc(v_snd_2607_);
lean_dec_ref(v_x_2589_);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2610_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2609_, v_snd_2607_);
lean_dec(v_snd_2607_);
v___x_2611_ = lean_array_get_size(v_r_2610_);
v___x_2616_ = lean_nat_dec_eq(v___x_2611_, v___x_2608_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___y_2620_; uint8_t v___x_2622_; 
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_sub(v___x_2611_, v___x_2617_);
v___x_2622_ = lean_nat_dec_le(v___x_2608_, v___x_2618_);
if (v___x_2622_ == 0)
{
lean_inc(v___x_2618_);
v___y_2620_ = v___x_2618_;
goto v___jp_2619_;
}
else
{
v___y_2620_ = v___x_2608_;
goto v___jp_2619_;
}
v___jp_2619_:
{
uint8_t v___x_2621_; 
v___x_2621_ = lean_nat_dec_le(v___y_2620_, v___x_2618_);
if (v___x_2621_ == 0)
{
lean_dec(v___x_2618_);
lean_inc(v___y_2620_);
v___y_2613_ = v___y_2620_;
v___y_2614_ = v___y_2620_;
goto v___jp_2612_;
}
else
{
v___y_2613_ = v___y_2620_;
v___y_2614_ = v___x_2618_;
goto v___jp_2612_;
}
}
}
else
{
v___y_2591_ = v_r_2610_;
goto v___jp_2590_;
}
v___jp_2612_:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2611_, v_r_2610_, v___y_2613_, v___y_2614_);
lean_dec(v___y_2614_);
v___y_2591_ = v___x_2615_;
goto v___jp_2590_;
}
}
else
{
lean_object* v_fst_2623_; lean_object* v_snd_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_fst_2623_ = lean_ctor_get(v_x_2589_, 0);
lean_inc(v_fst_2623_);
v_snd_2624_ = lean_ctor_get(v_x_2589_, 1);
lean_inc(v_snd_2624_);
lean_dec_ref(v_x_2589_);
v___x_2625_ = lean_array_mk(v_fst_2623_);
v___x_2626_ = l_Array_reverse___redArg(v___x_2625_);
v___x_2627_ = lean_unsigned_to_nat(0u);
v___x_2628_ = lean_array_get_size(v___x_2626_);
v___x_2629_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2624_, v___x_2626_, v___x_2627_, v___x_2628_);
lean_dec_ref(v___x_2626_);
lean_dec(v_snd_2624_);
v___y_2591_ = v___x_2629_;
goto v___jp_2590_;
}
v___jp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = lean_array_get_size(v___y_2591_);
v___x_2594_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2595_ = lean_nat_dec_lt(v___x_2592_, v___x_2593_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_dec_ref(v_env_2588_);
lean_dec_ref(v_filterExport_2586_);
v___x_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2594_);
lean_ctor_set(v___x_2596_, 2, v___y_2591_);
return v___x_2596_;
}
else
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_nat_dec_le(v___x_2593_, v___x_2593_);
if (v___x_2597_ == 0)
{
if (v___x_2595_ == 0)
{
lean_object* v___x_2598_; 
lean_dec_ref(v_env_2588_);
lean_dec_ref(v_filterExport_2586_);
v___x_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2594_);
lean_ctor_set(v___x_2598_, 1, v___x_2594_);
lean_ctor_set(v___x_2598_, 2, v___y_2591_);
return v___x_2598_;
}
else
{
size_t v___x_2599_; size_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = lean_usize_of_nat(v___x_2593_);
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2586_, v_env_2588_, v___y_2591_, v___x_2599_, v___x_2600_, v___x_2594_);
lean_inc_ref(v___x_2601_);
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
lean_ctor_set(v___x_2602_, 2, v___y_2591_);
return v___x_2602_;
}
}
else
{
size_t v___x_2603_; size_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2603_ = ((size_t)0ULL);
v___x_2604_ = lean_usize_of_nat(v___x_2593_);
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2586_, v_env_2588_, v___y_2591_, v___x_2603_, v___x_2604_, v___x_2594_);
lean_inc_ref(v___x_2605_);
v___x_2606_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_ctor_set(v___x_2606_, 2, v___y_2591_);
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2630_, lean_object* v_preserveOrder_2631_, lean_object* v_env_2632_, lean_object* v_x_2633_){
_start:
{
uint8_t v_preserveOrder_boxed_2634_; lean_object* v_res_2635_; 
v_preserveOrder_boxed_2634_ = lean_unbox(v_preserveOrder_2631_);
v_res_2635_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2630_, v_preserveOrder_boxed_2634_, v_env_2632_, v_x_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2645_){
_start:
{
lean_object* v_snd_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2660_; 
v_snd_2646_ = lean_ctor_get(v_x_2645_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_x_2645_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_x_2645_, 0);
lean_dec(v_unused_2661_);
v___x_2648_ = v_x_2645_;
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_snd_2646_);
lean_dec(v_x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2660_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; lean_object* v___y_2652_; 
v___x_2650_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2646_) == 0)
{
lean_object* v_size_2658_; 
v_size_2658_ = lean_ctor_get(v_snd_2646_, 0);
lean_inc(v_size_2658_);
lean_dec_ref_known(v_snd_2646_, 5);
v___y_2652_ = v_size_2658_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___y_2652_ = v___x_2659_;
goto v___jp_2651_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2653_ = l_Nat_reprFast(v___y_2652_);
v___x_2654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 5);
lean_ctor_set(v___x_2648_, 1, v___x_2654_);
lean_ctor_set(v___x_2648_, 0, v___x_2650_);
v___x_2656_ = v___x_2648_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2664_);
lean_dec_ref(v_x_2664_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2672_, lean_object* v_x_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2672_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2677_, lean_object* v_x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2677_, v_x_2678_, v___y_2679_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v_x_2678_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2692_, uint8_t v_preserveOrder_2693_, lean_object* v_filterExport_2694_){
_start:
{
lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___f_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2697_ = lean_box(v_preserveOrder_2693_);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2698_, 0, v_filterExport_2694_);
lean_closure_set(v___f_2698_, 1, v___x_2697_);
v___f_2699_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2700_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2701_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2702_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2703_ = lean_box(2);
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2705_, 0, v_ref_2692_);
lean_ctor_set(v___x_2705_, 1, v___f_2701_);
lean_ctor_set(v___x_2705_, 2, v___f_2702_);
lean_ctor_set(v___x_2705_, 3, v___f_2696_);
lean_ctor_set(v___x_2705_, 4, v___f_2698_);
lean_ctor_set(v___x_2705_, 5, v___f_2699_);
lean_ctor_set(v___x_2705_, 6, v___x_2703_);
lean_ctor_set(v___x_2705_, 7, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v___f_2700_);
v___x_2707_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2708_, lean_object* v_preserveOrder_2709_, lean_object* v_filterExport_2710_, lean_object* v_a_2711_){
_start:
{
uint8_t v_preserveOrder_boxed_2712_; lean_object* v_res_2713_; 
v_preserveOrder_boxed_2712_ = lean_unbox(v_preserveOrder_2709_);
v_res_2713_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2708_, v_preserveOrder_boxed_2712_, v_filterExport_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2714_, lean_object* v_ref_2715_, uint8_t v_preserveOrder_2716_, lean_object* v_filterExport_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2715_, v_preserveOrder_2716_, v_filterExport_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v_preserveOrder_2722_, lean_object* v_filterExport_2723_, lean_object* v_a_2724_){
_start:
{
uint8_t v_preserveOrder_boxed_2725_; lean_object* v_res_2726_; 
v_preserveOrder_boxed_2725_ = lean_unbox(v_preserveOrder_2722_);
v_res_2726_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2720_, v_ref_2721_, v_preserveOrder_boxed_2725_, v_filterExport_2723_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2727_, lean_object* v_filterExport_2728_, lean_object* v_env_2729_, lean_object* v_as_2730_, size_t v_i_2731_, size_t v_stop_2732_, lean_object* v_b_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2728_, v_env_2729_, v_as_2730_, v_i_2731_, v_stop_2732_, v_b_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2735_, lean_object* v_filterExport_2736_, lean_object* v_env_2737_, lean_object* v_as_2738_, lean_object* v_i_2739_, lean_object* v_stop_2740_, lean_object* v_b_2741_){
_start:
{
size_t v_i_boxed_2742_; size_t v_stop_boxed_2743_; lean_object* v_res_2744_; 
v_i_boxed_2742_ = lean_unbox_usize(v_i_2739_);
lean_dec(v_i_2739_);
v_stop_boxed_2743_ = lean_unbox_usize(v_stop_2740_);
lean_dec(v_stop_2740_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2735_, v_filterExport_2736_, v_env_2737_, v_as_2738_, v_i_boxed_2742_, v_stop_boxed_2743_, v_b_2741_);
lean_dec_ref(v_as_2738_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2745_, lean_object* v_t_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2745_, v_t_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2748_, lean_object* v_t_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2748_, v_t_2749_);
lean_dec(v_t_2749_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2751_, lean_object* v_init_2752_, lean_object* v_t_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2752_, v_t_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_init_2756_, lean_object* v_t_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2755_, v_init_2756_, v_t_2757_);
lean_dec(v_t_2757_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2759_, lean_object* v_n_2760_, lean_object* v_as_2761_, lean_object* v_lo_2762_, lean_object* v_hi_2763_, lean_object* v_w_2764_, lean_object* v_hlo_2765_, lean_object* v_hhi_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2760_, v_as_2761_, v_lo_2762_, v_hi_2763_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_n_2769_, lean_object* v_as_2770_, lean_object* v_lo_2771_, lean_object* v_hi_2772_, lean_object* v_w_2773_, lean_object* v_hlo_2774_, lean_object* v_hhi_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2768_, v_n_2769_, v_as_2770_, v_lo_2771_, v_hi_2772_, v_w_2773_, v_hlo_2774_, v_hhi_2775_);
lean_dec(v_hi_2772_);
lean_dec(v_n_2769_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2777_, lean_object* v_snd_2778_, lean_object* v_as_2779_, lean_object* v_start_2780_, lean_object* v_stop_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2778_, v_as_2779_, v_start_2780_, v_stop_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_snd_2784_, lean_object* v_as_2785_, lean_object* v_start_2786_, lean_object* v_stop_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2783_, v_snd_2784_, v_as_2785_, v_start_2786_, v_stop_2787_);
lean_dec(v_stop_2787_);
lean_dec(v_start_2786_);
lean_dec_ref(v_as_2785_);
lean_dec(v_snd_2784_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2789_, lean_object* v_init_2790_, lean_object* v_x_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_init_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2793_, v_init_2794_, v_x_2795_);
lean_dec(v_x_2795_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2797_, lean_object* v_n_2798_, lean_object* v_lo_2799_, lean_object* v_hi_2800_, lean_object* v_hhi_2801_, lean_object* v_pivot_2802_, lean_object* v_as_2803_, lean_object* v_i_2804_, lean_object* v_k_2805_, lean_object* v_ilo_2806_, lean_object* v_ik_2807_, lean_object* v_w_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2800_, v_pivot_2802_, v_as_2803_, v_i_2804_, v_k_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2810_, lean_object* v_n_2811_, lean_object* v_lo_2812_, lean_object* v_hi_2813_, lean_object* v_hhi_2814_, lean_object* v_pivot_2815_, lean_object* v_as_2816_, lean_object* v_i_2817_, lean_object* v_k_2818_, lean_object* v_ilo_2819_, lean_object* v_ik_2820_, lean_object* v_w_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2810_, v_n_2811_, v_lo_2812_, v_hi_2813_, v_hhi_2814_, v_pivot_2815_, v_as_2816_, v_i_2817_, v_k_2818_, v_ilo_2819_, v_ik_2820_, v_w_2821_);
lean_dec_ref(v_pivot_2815_);
lean_dec(v_hi_2813_);
lean_dec(v_lo_2812_);
lean_dec(v_n_2811_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2823_, lean_object* v_snd_2824_, lean_object* v_as_2825_, size_t v_i_2826_, size_t v_stop_2827_, lean_object* v_b_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2824_, v_as_2825_, v_i_2826_, v_stop_2827_, v_b_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_snd_2831_, lean_object* v_as_2832_, lean_object* v_i_2833_, lean_object* v_stop_2834_, lean_object* v_b_2835_){
_start:
{
size_t v_i_boxed_2836_; size_t v_stop_boxed_2837_; lean_object* v_res_2838_; 
v_i_boxed_2836_ = lean_unbox_usize(v_i_2833_);
lean_dec(v_i_2833_);
v_stop_boxed_2837_ = lean_unbox_usize(v_stop_2834_);
lean_dec(v_stop_2834_);
v_res_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2830_, v_snd_2831_, v_as_2832_, v_i_boxed_2836_, v_stop_boxed_2837_, v_b_2835_);
lean_dec_ref(v_as_2832_);
lean_dec(v_snd_2831_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; lean_object* v_nextMacroScope_2843_; lean_object* v_ngen_2844_; lean_object* v_auxDeclNGen_2845_; lean_object* v_traceState_2846_; lean_object* v_messages_2847_; lean_object* v_infoState_2848_; lean_object* v_snapshotTasks_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2860_; 
v___x_2842_ = lean_st_ref_take(v___y_2840_);
v_nextMacroScope_2843_ = lean_ctor_get(v___x_2842_, 1);
v_ngen_2844_ = lean_ctor_get(v___x_2842_, 2);
v_auxDeclNGen_2845_ = lean_ctor_get(v___x_2842_, 3);
v_traceState_2846_ = lean_ctor_get(v___x_2842_, 4);
v_messages_2847_ = lean_ctor_get(v___x_2842_, 6);
v_infoState_2848_ = lean_ctor_get(v___x_2842_, 7);
v_snapshotTasks_2849_ = lean_ctor_get(v___x_2842_, 8);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; lean_object* v_unused_2862_; 
v_unused_2861_ = lean_ctor_get(v___x_2842_, 5);
lean_dec(v_unused_2861_);
v_unused_2862_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2862_);
v___x_2851_ = v___x_2842_;
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_snapshotTasks_2849_);
lean_inc(v_infoState_2848_);
lean_inc(v_messages_2847_);
lean_inc(v_traceState_2846_);
lean_inc(v_auxDeclNGen_2845_);
lean_inc(v_ngen_2844_);
lean_inc(v_nextMacroScope_2843_);
lean_dec(v___x_2842_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2860_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 5, v___x_2853_);
lean_ctor_set(v___x_2851_, 0, v_env_2839_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_env_2839_);
lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_nextMacroScope_2843_);
lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_ngen_2844_);
lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_auxDeclNGen_2845_);
lean_ctor_set(v_reuseFailAlloc_2859_, 4, v_traceState_2846_);
lean_ctor_set(v_reuseFailAlloc_2859_, 5, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2859_, 6, v_messages_2847_);
lean_ctor_set(v_reuseFailAlloc_2859_, 7, v_infoState_2848_);
lean_ctor_set(v_reuseFailAlloc_2859_, 8, v_snapshotTasks_2849_);
v___x_2855_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2856_ = lean_st_ref_put(v___y_2840_, v___x_2855_);
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
return v___x_2858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2863_, v___y_2864_);
lean_dec(v___y_2864_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2867_, v___y_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2877_, lean_object* v_ext_2878_, lean_object* v_afterSet_2879_, lean_object* v_toAttributeImplCore_2880_, lean_object* v_decl_2881_, lean_object* v_stx_2882_, uint8_t v_kind_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___y_2892_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = 0;
v___x_2942_ = l_Lean_instBEqAttributeKind_beq(v_kind_2883_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v_name_2943_; lean_object* v___x_2944_; 
lean_dec(v_stx_2882_);
lean_dec(v_decl_2881_);
lean_dec_ref(v_afterSet_2879_);
lean_dec_ref(v_ext_2878_);
lean_dec_ref(v_getParam_2877_);
v_name_2943_ = lean_ctor_get(v_toAttributeImplCore_2880_, 1);
lean_inc(v_name_2943_);
lean_dec_ref(v_toAttributeImplCore_2880_);
v___x_2944_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2943_, v_kind_2883_, v___y_2884_, v___y_2885_);
return v___x_2944_;
}
else
{
goto v___jp_2935_;
}
v___jp_2887_:
{
if (v___y_2892_ == 0)
{
lean_object* v___x_2893_; 
lean_dec_ref(v___y_2889_);
v___x_2893_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2888_, v___y_2890_);
return v___x_2893_;
}
else
{
lean_dec_ref(v___y_2888_);
return v___y_2889_;
}
}
v___jp_2894_:
{
lean_object* v___x_2898_; 
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
lean_inc(v_decl_2881_);
v___x_2898_ = lean_apply_5(v_getParam_2877_, v_decl_2881_, v_stx_2882_, v___y_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v_toEnvExtension_2901_; lean_object* v_env_2902_; lean_object* v_nextMacroScope_2903_; lean_object* v_ngen_2904_; lean_object* v_auxDeclNGen_2905_; lean_object* v_traceState_2906_; lean_object* v_messages_2907_; lean_object* v_infoState_2908_; lean_object* v_snapshotTasks_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2925_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = lean_st_ref_take(v___y_2897_);
v_toEnvExtension_2901_ = lean_ctor_get(v_ext_2878_, 0);
v_env_2902_ = lean_ctor_get(v___x_2900_, 0);
v_nextMacroScope_2903_ = lean_ctor_get(v___x_2900_, 1);
v_ngen_2904_ = lean_ctor_get(v___x_2900_, 2);
v_auxDeclNGen_2905_ = lean_ctor_get(v___x_2900_, 3);
v_traceState_2906_ = lean_ctor_get(v___x_2900_, 4);
v_messages_2907_ = lean_ctor_get(v___x_2900_, 6);
v_infoState_2908_ = lean_ctor_get(v___x_2900_, 7);
v_snapshotTasks_2909_ = lean_ctor_get(v___x_2900_, 8);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2900_, 5);
lean_dec(v_unused_2926_);
v___x_2911_ = v___x_2900_;
v_isShared_2912_ = v_isSharedCheck_2925_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_snapshotTasks_2909_);
lean_inc(v_infoState_2908_);
lean_inc(v_messages_2907_);
lean_inc(v_traceState_2906_);
lean_inc(v_auxDeclNGen_2905_);
lean_inc(v_ngen_2904_);
lean_inc(v_nextMacroScope_2903_);
lean_inc(v_env_2902_);
lean_dec(v___x_2900_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2925_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_asyncMode_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v_asyncMode_2913_ = lean_ctor_get(v_toEnvExtension_2901_, 2);
lean_inc(v_asyncMode_2913_);
lean_inc(v_a_2899_);
lean_inc_n(v_decl_2881_, 2);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v_decl_2881_);
lean_ctor_set(v___x_2914_, 1, v_a_2899_);
v___x_2915_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2878_, v_env_2902_, v___x_2914_, v_asyncMode_2913_, v_decl_2881_);
lean_dec(v_asyncMode_2913_);
v___x_2916_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 5, v___x_2916_);
lean_ctor_set(v___x_2911_, 0, v___x_2915_);
v___x_2918_ = v___x_2911_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_nextMacroScope_2903_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_ngen_2904_);
lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_auxDeclNGen_2905_);
lean_ctor_set(v_reuseFailAlloc_2924_, 4, v_traceState_2906_);
lean_ctor_set(v_reuseFailAlloc_2924_, 5, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2924_, 6, v_messages_2907_);
lean_ctor_set(v_reuseFailAlloc_2924_, 7, v_infoState_2908_);
lean_ctor_set(v_reuseFailAlloc_2924_, 8, v_snapshotTasks_2909_);
v___x_2918_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_st_ref_put(v___y_2897_, v___x_2918_);
lean_inc(v___y_2897_);
lean_inc_ref(v___y_2896_);
v___x_2920_ = lean_apply_5(v_afterSet_2879_, v_decl_2881_, v_a_2899_, v___y_2896_, v___y_2897_, lean_box(0));
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_dec_ref(v___y_2895_);
return v___x_2920_;
}
else
{
lean_object* v_a_2921_; uint8_t v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
v___x_2922_ = l_Lean_Exception_isInterrupt(v_a_2921_);
if (v___x_2922_ == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = l_Lean_Exception_isRuntime(v_a_2921_);
v___y_2888_ = v___y_2895_;
v___y_2889_ = v___x_2920_;
v___y_2890_ = v___y_2897_;
v___y_2891_ = v___y_2896_;
v___y_2892_ = v___x_2923_;
goto v___jp_2887_;
}
else
{
lean_dec(v_a_2921_);
v___y_2888_ = v___y_2895_;
v___y_2889_ = v___x_2920_;
v___y_2890_ = v___y_2897_;
v___y_2891_ = v___y_2896_;
v___y_2892_ = v___x_2922_;
goto v___jp_2887_;
}
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v___y_2895_);
lean_dec(v_decl_2881_);
lean_dec_ref(v_afterSet_2879_);
lean_dec_ref(v_ext_2878_);
v_a_2927_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2898_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2898_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
v___jp_2935_:
{
lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_st_ref_get(v___y_2885_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2938_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2937_, v_decl_2881_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2880_);
v___y_2895_ = v_env_2937_;
v___y_2896_ = v___y_2884_;
v___y_2897_ = v___y_2885_;
goto v___jp_2894_;
}
else
{
lean_object* v_name_2939_; lean_object* v___x_2940_; 
lean_dec_ref_known(v___x_2938_, 1);
lean_dec_ref(v_env_2937_);
lean_dec(v_stx_2882_);
lean_dec_ref(v_afterSet_2879_);
lean_dec_ref(v_ext_2878_);
lean_dec_ref(v_getParam_2877_);
v_name_2939_ = lean_ctor_get(v_toAttributeImplCore_2880_, 1);
lean_inc(v_name_2939_);
lean_dec_ref(v_toAttributeImplCore_2880_);
v___x_2940_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2939_, v_decl_2881_, v___y_2884_, v___y_2885_);
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2945_, lean_object* v_ext_2946_, lean_object* v_afterSet_2947_, lean_object* v_toAttributeImplCore_2948_, lean_object* v_decl_2949_, lean_object* v_stx_2950_, lean_object* v_kind_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v_kind_boxed_2955_; lean_object* v_res_2956_; 
v_kind_boxed_2955_ = lean_unbox(v_kind_2951_);
v_res_2956_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2945_, v_ext_2946_, v_afterSet_2947_, v_toAttributeImplCore_2948_, v_decl_2949_, v_stx_2950_, v_kind_boxed_2955_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2957_, lean_object* v_decl_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_name_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_name_2962_ = lean_ctor_get(v_toAttributeImplCore_2957_, 1);
lean_inc(v_name_2962_);
lean_dec_ref(v_toAttributeImplCore_2957_);
v___x_2963_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2964_ = l_Lean_MessageData_ofName(v_name_2962_);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2967_, v___y_2959_, v___y_2960_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2969_, lean_object* v_decl_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2969_, v_decl_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v_decl_2970_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2975_, lean_object* v_ext_2976_){
_start:
{
lean_object* v_toAttributeImplCore_2978_; lean_object* v_getParam_2979_; lean_object* v_afterSet_2980_; uint8_t v_preserveOrder_2981_; lean_object* v___f_2982_; lean_object* v___f_2983_; lean_object* v_attrImpl_2984_; lean_object* v___x_2985_; 
v_toAttributeImplCore_2978_ = lean_ctor_get(v_impl_2975_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2978_, 3);
v_getParam_2979_ = lean_ctor_get(v_impl_2975_, 1);
lean_inc_ref(v_getParam_2979_);
v_afterSet_2980_ = lean_ctor_get(v_impl_2975_, 2);
lean_inc_ref(v_afterSet_2980_);
v_preserveOrder_2981_ = lean_ctor_get_uint8(v_impl_2975_, sizeof(void*)*4);
lean_dec_ref(v_impl_2975_);
lean_inc_ref(v_ext_2976_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2982_, 0, v_getParam_2979_);
lean_closure_set(v___f_2982_, 1, v_ext_2976_);
lean_closure_set(v___f_2982_, 2, v_afterSet_2980_);
lean_closure_set(v___f_2982_, 3, v_toAttributeImplCore_2978_);
v___f_2983_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2983_, 0, v_toAttributeImplCore_2978_);
v_attrImpl_2984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2984_, 0, v_toAttributeImplCore_2978_);
lean_ctor_set(v_attrImpl_2984_, 1, v___f_2982_);
lean_ctor_set(v_attrImpl_2984_, 2, v___f_2983_);
lean_inc_ref(v_attrImpl_2984_);
v___x_2985_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2993_; 
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_2994_);
v___x_2987_ = v___x_2985_;
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v___x_2985_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2989_, 0, v_attrImpl_2984_);
lean_ctor_set(v___x_2989_, 1, v_ext_2976_);
lean_ctor_set_uint8(v___x_2989_, sizeof(void*)*2, v_preserveOrder_2981_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2989_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref_known(v_attrImpl_2984_, 3);
lean_dec_ref(v_ext_2976_);
v_a_2995_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2985_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2985_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3003_, lean_object* v_ext_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3003_, v_ext_3004_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3007_, lean_object* v_impl_3008_, lean_object* v_ext_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3008_, v_ext_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_impl_3013_, lean_object* v_ext_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3012_, v_impl_3013_, v_ext_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3017_){
_start:
{
lean_object* v_toAttributeImplCore_3019_; uint8_t v_preserveOrder_3020_; lean_object* v_filterExport_3021_; lean_object* v_ref_3022_; lean_object* v___x_3023_; 
v_toAttributeImplCore_3019_ = lean_ctor_get(v_impl_3017_, 0);
v_preserveOrder_3020_ = lean_ctor_get_uint8(v_impl_3017_, sizeof(void*)*4);
v_filterExport_3021_ = lean_ctor_get(v_impl_3017_, 3);
v_ref_3022_ = lean_ctor_get(v_toAttributeImplCore_3019_, 0);
lean_inc_ref(v_filterExport_3021_);
lean_inc(v_ref_3022_);
v___x_3023_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3022_, v_preserveOrder_3020_, v_filterExport_3021_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3017_, v_a_3024_);
return v___x_3025_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_impl_3017_);
v_a_3026_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3023_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3023_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Lean_registerParametricAttribute___redArg(v_impl_3034_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3037_, lean_object* v_impl_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_registerParametricAttribute___redArg(v_impl_3038_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3041_, lean_object* v_impl_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_registerParametricAttribute(v_00_u03b1_3041_, v_impl_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3045_, lean_object* v___x_3046_, lean_object* v___x_3047_, lean_object* v_a_3048_, lean_object* v_x_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_fst_3051_; uint8_t v___x_3052_; 
v_fst_3051_ = lean_ctor_get(v_a_3048_, 0);
v___x_3052_ = lean_name_eq(v_fst_3051_, v_decl_3045_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
lean_dec_ref(v_a_3048_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3046_);
return v___x_3053_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec_ref(v___x_3046_);
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v_a_3048_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3047_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3058_, lean_object* v___x_3059_, lean_object* v___x_3060_, lean_object* v_a_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3058_, v___x_3059_, v___x_3060_, v_a_3061_, v_x_3062_, v___y_3063_);
lean_dec_ref(v___y_3063_);
lean_dec(v_decl_3058_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3092_, lean_object* v_ext_3093_, uint8_t v_preserveOrder_3094_, lean_object* v_env_3095_, lean_object* v_decl_3096_){
_start:
{
lean_object* v___y_3098_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3110_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3095_, v_decl_3096_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_toEnvExtension_3111_; lean_object* v_asyncMode_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_snd_3115_; lean_object* v___x_3116_; 
lean_dec(v_inst_3092_);
v_toEnvExtension_3111_ = lean_ctor_get(v_ext_3093_, 0);
v_asyncMode_3112_ = lean_ctor_get(v_toEnvExtension_3111_, 2);
v___x_3113_ = lean_box(0);
v___x_3114_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3109_, v_ext_3093_, v_env_3095_, v_asyncMode_3112_, v___x_3113_);
v_snd_3115_ = lean_ctor_get(v___x_3114_, 1);
lean_inc(v_snd_3115_);
lean_dec(v___x_3114_);
v___x_3116_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3115_, v_decl_3096_);
lean_dec(v_decl_3096_);
lean_dec(v_snd_3115_);
return v___x_3116_;
}
else
{
if (v_preserveOrder_3094_ == 0)
{
lean_object* v_val_3117_; uint8_t v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_val_3117_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3118_ = 0;
v___x_3119_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3109_, v_ext_3093_, v_env_3095_, v_val_3117_, v___x_3118_);
lean_dec(v_val_3117_);
lean_dec_ref(v_env_3095_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_array_get_size(v___x_3119_);
v___x_3122_ = lean_nat_dec_lt(v___x_3120_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v___x_3119_);
lean_dec(v_decl_3096_);
lean_dec(v_inst_3092_);
v___x_3123_ = lean_box(0);
return v___x_3123_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_sub(v___x_3121_, v___x_3124_);
v___x_3126_ = lean_nat_dec_le(v___x_3120_, v___x_3125_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec(v___x_3125_);
lean_dec_ref(v___x_3119_);
lean_dec(v_decl_3096_);
lean_dec(v_inst_3092_);
v___x_3127_ = lean_box(0);
return v___x_3127_;
}
else
{
lean_object* v___f_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___f_3128_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v_decl_3096_);
lean_ctor_set(v___x_3129_, 1, v_inst_3092_);
v___x_3130_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3131_ = l_Array_binSearchAux___redArg(v___f_3128_, v___x_3130_, v___x_3119_, v___x_3129_, v___x_3120_, v___x_3125_);
lean_dec_ref(v___x_3119_);
v___y_3098_ = v___x_3131_;
goto v___jp_3097_;
}
}
}
else
{
lean_object* v_val_3132_; uint8_t v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___f_3139_; size_t v_sz_3140_; size_t v___x_3141_; lean_object* v___x_3142_; lean_object* v_fst_3143_; 
lean_dec(v_inst_3092_);
v_val_3132_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3133_ = 0;
v___x_3134_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3109_, v_ext_3093_, v_env_3095_, v_val_3132_, v___x_3133_);
lean_dec(v_val_3132_);
lean_dec_ref(v_env_3095_);
v___x_3135_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3136_ = lean_box(0);
v___x_3137_ = lean_box(0);
v___x_3138_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3139_, 0, v_decl_3096_);
lean_closure_set(v___f_3139_, 1, v___x_3138_);
lean_closure_set(v___f_3139_, 2, v___x_3137_);
v_sz_3140_ = lean_array_size(v___x_3134_);
v___x_3141_ = ((size_t)0ULL);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3135_, v___x_3134_, v___f_3139_, v_sz_3140_, v___x_3141_, v___x_3138_);
v_fst_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_fst_3143_);
lean_dec(v___x_3142_);
if (lean_obj_tag(v_fst_3143_) == 0)
{
return v___x_3136_;
}
else
{
lean_object* v_val_3144_; 
v_val_3144_ = lean_ctor_get(v_fst_3143_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v_fst_3143_, 1);
v___y_3098_ = v_val_3144_;
goto v___jp_3097_;
}
}
}
v___jp_3097_:
{
if (lean_obj_tag(v___y_3098_) == 0)
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_box(0);
return v___x_3099_;
}
else
{
lean_object* v_val_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3108_; 
v_val_3100_ = lean_ctor_get(v___y_3098_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___y_3098_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3102_ = v___y_3098_;
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_val_3100_);
lean_dec(v___y_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3108_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v_snd_3104_; lean_object* v___x_3106_; 
v_snd_3104_ = lean_ctor_get(v_val_3100_, 1);
lean_inc(v_snd_3104_);
lean_dec(v_val_3100_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v_snd_3104_);
v___x_3106_ = v___x_3102_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_snd_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3145_, lean_object* v_ext_3146_, lean_object* v_preserveOrder_3147_, lean_object* v_env_3148_, lean_object* v_decl_3149_){
_start:
{
uint8_t v_preserveOrder_boxed_3150_; lean_object* v_res_3151_; 
v_preserveOrder_boxed_3150_ = lean_unbox(v_preserveOrder_3147_);
v_res_3151_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3145_, v_ext_3146_, v_preserveOrder_boxed_3150_, v_env_3148_, v_decl_3149_);
lean_dec_ref(v_ext_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3152_, lean_object* v_inst_3153_, lean_object* v_ext_3154_, uint8_t v_preserveOrder_3155_, lean_object* v_env_3156_, lean_object* v_decl_3157_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3153_, v_ext_3154_, v_preserveOrder_3155_, v_env_3156_, v_decl_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3159_, lean_object* v_inst_3160_, lean_object* v_ext_3161_, lean_object* v_preserveOrder_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
uint8_t v_preserveOrder_boxed_3165_; lean_object* v_res_3166_; 
v_preserveOrder_boxed_3165_ = lean_unbox(v_preserveOrder_3162_);
v_res_3166_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3159_, v_inst_3160_, v_ext_3161_, v_preserveOrder_boxed_3165_, v_env_3163_, v_decl_3164_);
lean_dec_ref(v_ext_3161_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3167_, lean_object* v_attr_3168_, lean_object* v_env_3169_, lean_object* v_decl_3170_){
_start:
{
lean_object* v_ext_3171_; uint8_t v_preserveOrder_3172_; lean_object* v___x_3173_; 
v_ext_3171_ = lean_ctor_get(v_attr_3168_, 1);
v_preserveOrder_3172_ = lean_ctor_get_uint8(v_attr_3168_, sizeof(void*)*2);
v___x_3173_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3167_, v_ext_3171_, v_preserveOrder_3172_, v_env_3169_, v_decl_3170_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3174_, lean_object* v_attr_3175_, lean_object* v_env_3176_, lean_object* v_decl_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3174_, v_attr_3175_, v_env_3176_, v_decl_3177_);
lean_dec_ref(v_attr_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3179_, lean_object* v_inst_3180_, lean_object* v_attr_3181_, lean_object* v_env_3182_, lean_object* v_decl_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3180_, v_attr_3181_, v_env_3182_, v_decl_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_attr_3187_, lean_object* v_env_3188_, lean_object* v_decl_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3185_, v_inst_3186_, v_attr_3187_, v_env_3188_, v_decl_3189_);
lean_dec_ref(v_attr_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3195_, lean_object* v_attr_3196_, lean_object* v_env_3197_, lean_object* v_decl_3198_, lean_object* v_param_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3197_, v_decl_3198_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_toEnvExtension_3201_; lean_object* v_asyncMode_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_snd_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3236_; 
v_toEnvExtension_3201_ = lean_ctor_get(v_ext_3195_, 0);
v_asyncMode_3202_ = lean_ctor_get(v_toEnvExtension_3201_, 2);
lean_inc(v_asyncMode_3202_);
v___x_3203_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3204_ = lean_box(0);
lean_inc_ref(v_env_3197_);
v___x_3205_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3203_, v_ext_3195_, v_env_3197_, v_asyncMode_3202_, v___x_3204_);
v_snd_3206_ = lean_ctor_get(v___x_3205_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3237_);
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_snd_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3236_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3206_, v_decl_3198_);
lean_dec(v_snd_3206_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v_attr_3196_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v_param_3199_);
lean_ctor_set(v___x_3208_, 0, v_decl_3198_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_decl_3198_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_param_3199_);
v___x_3212_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3195_, v_env_3197_, v___x_3212_, v_asyncMode_3202_, v___x_3204_);
lean_dec(v_asyncMode_3202_);
v___x_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
else
{
lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3208_);
lean_dec(v_asyncMode_3202_);
lean_dec(v_param_3199_);
lean_dec_ref(v_env_3197_);
lean_dec_ref(v_ext_3195_);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3235_);
v___x_3217_ = v___x_3210_;
v_isShared_3218_ = v_isSharedCheck_3234_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v___x_3210_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3234_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v_toAttributeImplCore_3219_; lean_object* v_name_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v_toAttributeImplCore_3219_ = lean_ctor_get(v_attr_3196_, 0);
lean_inc_ref(v_toAttributeImplCore_3219_);
lean_dec_ref(v_attr_3196_);
v_name_3220_ = lean_ctor_get(v_toAttributeImplCore_3219_, 1);
lean_inc(v_name_3220_);
lean_dec_ref(v_toAttributeImplCore_3219_);
v___x_3221_ = 1;
v___x_3222_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3220_, v___x_3221_);
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
lean_dec_ref(v___x_3223_);
v___x_3225_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3226_ = lean_string_append(v___x_3224_, v___x_3225_);
v___x_3227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3198_, v___x_3221_);
v___x_3228_ = lean_string_append(v___x_3226_, v___x_3227_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3230_ = lean_string_append(v___x_3228_, v___x_3229_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set_tag(v___x_3217_, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3230_);
v___x_3232_ = v___x_3217_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
else
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_param_3199_);
lean_dec_ref(v_env_3197_);
lean_dec_ref(v_ext_3195_);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v___x_3200_, 0);
lean_dec(v_unused_3257_);
v___x_3239_ = v___x_3200_;
v_isShared_3240_ = v_isSharedCheck_3256_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v___x_3200_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3256_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_toAttributeImplCore_3241_; lean_object* v_name_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v_toAttributeImplCore_3241_ = lean_ctor_get(v_attr_3196_, 0);
lean_inc_ref(v_toAttributeImplCore_3241_);
lean_dec_ref(v_attr_3196_);
v_name_3242_ = lean_ctor_get(v_toAttributeImplCore_3241_, 1);
lean_inc(v_name_3242_);
lean_dec_ref(v_toAttributeImplCore_3241_);
v___x_3243_ = 1;
v___x_3244_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3245_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3242_, v___x_3243_);
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
lean_dec_ref(v___x_3245_);
v___x_3247_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3248_ = lean_string_append(v___x_3246_, v___x_3247_);
v___x_3249_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3198_, v___x_3243_);
v___x_3250_ = lean_string_append(v___x_3248_, v___x_3249_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3252_ = lean_string_append(v___x_3250_, v___x_3251_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3252_);
v___x_3254_ = v___x_3239_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3258_, lean_object* v_ext_3259_, lean_object* v_attr_3260_, lean_object* v_env_3261_, lean_object* v_decl_3262_, lean_object* v_param_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3259_, v_attr_3260_, v_env_3261_, v_decl_3262_, v_param_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3265_, lean_object* v_env_3266_, lean_object* v_decl_3267_, lean_object* v_param_3268_){
_start:
{
lean_object* v_attr_3269_; lean_object* v_ext_3270_; lean_object* v___x_3271_; 
v_attr_3269_ = lean_ctor_get(v_attr_3265_, 0);
lean_inc_ref(v_attr_3269_);
v_ext_3270_ = lean_ctor_get(v_attr_3265_, 1);
lean_inc_ref(v_ext_3270_);
lean_dec_ref(v_attr_3265_);
v___x_3271_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3270_, v_attr_3269_, v_env_3266_, v_decl_3267_, v_param_3268_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3272_, lean_object* v_attr_3273_, lean_object* v_env_3274_, lean_object* v_decl_3275_, lean_object* v_param_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3273_, v_env_3274_, v_decl_3275_, v_param_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3283_, v___y_3284_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v_x_3283_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3287_, lean_object* v_x_3288_){
_start:
{
lean_inc(v_s_3287_);
return v_s_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3289_, v_x_3290_);
lean_dec_ref(v_x_3290_);
lean_dec(v_s_3289_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3295_, v_x_3296_);
lean_dec(v_x_3296_);
lean_dec_ref(v_x_3295_);
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3302_; lean_object* v___f_3303_; lean_object* v___f_3304_; lean_object* v___f_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___f_3302_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3303_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3304_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3305_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3308_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v___x_3306_);
lean_ctor_set(v___x_3308_, 2, v___f_3305_);
lean_ctor_set(v___x_3308_, 3, v___f_3304_);
lean_ctor_set(v___x_3308_, 4, v___f_3303_);
lean_ctor_set(v___x_3308_, 5, v___f_3302_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
lean_ctor_set(v___x_3311_, 1, v___x_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3313_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3320_);
lean_dec(v_x_3320_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_){
_start:
{
if (lean_obj_tag(v_x_3324_) == 0)
{
return v_x_3323_;
}
else
{
lean_object* v_head_3325_; lean_object* v_tail_3326_; lean_object* v___x_3327_; 
v_head_3325_ = lean_ctor_get(v_x_3324_, 0);
lean_inc(v_head_3325_);
v_tail_3326_ = lean_ctor_get(v_x_3324_, 1);
lean_inc(v_tail_3326_);
lean_dec_ref_known(v_x_3324_, 2);
v___x_3327_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3322_, v_head_3325_);
if (lean_obj_tag(v___x_3327_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3329_; 
v_val_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_val_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3325_, v_val_3328_, v_x_3323_);
v_x_3323_ = v___x_3329_;
v_x_3324_ = v_tail_3326_;
goto _start;
}
else
{
lean_dec(v___x_3327_);
lean_dec(v_head_3325_);
v_x_3324_ = v_tail_3326_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3332_, v_x_3333_, v_x_3334_);
lean_dec(v_newState_3332_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3336_, lean_object* v_newState_3337_, lean_object* v_consts_3338_, lean_object* v_st_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3337_, v_st_3339_, v_consts_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3341_, lean_object* v_newState_3342_, lean_object* v_consts_3343_, lean_object* v_st_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3341_, v_newState_3342_, v_consts_3343_, v_st_3344_);
lean_dec(v_newState_3342_);
lean_dec(v_x_3341_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___y_3358_; 
v___x_3356_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3355_) == 0)
{
lean_object* v_size_3362_; 
v_size_3362_ = lean_ctor_get(v_s_3355_, 0);
lean_inc(v_size_3362_);
lean_dec_ref_known(v_s_3355_, 5);
v___y_3358_ = v_size_3362_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_unsigned_to_nat(0u);
v___y_3358_ = v___x_3363_;
goto v___jp_3357_;
}
v___jp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = l_Nat_reprFast(v___y_3358_);
v___x_3360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3356_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3364_, lean_object* v_as_3365_, size_t v_i_3366_, size_t v_stop_3367_, lean_object* v_b_3368_){
_start:
{
lean_object* v___y_3370_; uint8_t v___x_3374_; 
v___x_3374_ = lean_usize_dec_eq(v_i_3366_, v_stop_3367_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v_fst_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3375_ = lean_array_uget_borrowed(v_as_3365_, v_i_3366_);
v_fst_3376_ = lean_ctor_get(v___x_3375_, 0);
v___x_3377_ = 1;
lean_inc_ref(v_env_3364_);
v___x_3378_ = l_Lean_Environment_setExporting(v_env_3364_, v___x_3377_);
lean_inc(v_fst_3376_);
v___x_3379_ = l_Lean_Environment_contains(v___x_3378_, v_fst_3376_, v___x_3374_);
if (v___x_3379_ == 0)
{
v___y_3370_ = v_b_3368_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3380_; 
lean_inc(v___x_3375_);
v___x_3380_ = lean_array_push(v_b_3368_, v___x_3375_);
v___y_3370_ = v___x_3380_;
goto v___jp_3369_;
}
}
else
{
lean_dec_ref(v_env_3364_);
return v_b_3368_;
}
v___jp_3369_:
{
size_t v___x_3371_; size_t v___x_3372_; 
v___x_3371_ = ((size_t)1ULL);
v___x_3372_ = lean_usize_add(v_i_3366_, v___x_3371_);
v_i_3366_ = v___x_3372_;
v_b_3368_ = v___y_3370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3381_, lean_object* v_as_3382_, lean_object* v_i_3383_, lean_object* v_stop_3384_, lean_object* v_b_3385_){
_start:
{
size_t v_i_boxed_3386_; size_t v_stop_boxed_3387_; lean_object* v_res_3388_; 
v_i_boxed_3386_ = lean_unbox_usize(v_i_3383_);
lean_dec(v_i_3383_);
v_stop_boxed_3387_ = lean_unbox_usize(v_stop_3384_);
lean_dec(v_stop_3384_);
v_res_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3381_, v_as_3382_, v_i_boxed_3386_, v_stop_boxed_3387_, v_b_3385_);
lean_dec_ref(v_as_3382_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3389_, lean_object* v_m_3390_){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___y_3394_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___x_3414_; 
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3408_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3392_, v_m_3390_);
v___x_3409_ = lean_array_get_size(v___x_3408_);
v___x_3414_ = lean_nat_dec_eq(v___x_3409_, v___x_3391_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___y_3418_; uint8_t v___x_3420_; 
v___x_3415_ = lean_unsigned_to_nat(1u);
v___x_3416_ = lean_nat_sub(v___x_3409_, v___x_3415_);
v___x_3420_ = lean_nat_dec_le(v___x_3391_, v___x_3416_);
if (v___x_3420_ == 0)
{
lean_inc(v___x_3416_);
v___y_3418_ = v___x_3416_;
goto v___jp_3417_;
}
else
{
v___y_3418_ = v___x_3391_;
goto v___jp_3417_;
}
v___jp_3417_:
{
uint8_t v___x_3419_; 
v___x_3419_ = lean_nat_dec_le(v___y_3418_, v___x_3416_);
if (v___x_3419_ == 0)
{
lean_dec(v___x_3416_);
lean_inc(v___y_3418_);
v___y_3411_ = v___y_3418_;
v___y_3412_ = v___y_3418_;
goto v___jp_3410_;
}
else
{
v___y_3411_ = v___y_3418_;
v___y_3412_ = v___x_3416_;
goto v___jp_3410_;
}
}
}
else
{
v___y_3394_ = v___x_3408_;
goto v___jp_3393_;
}
v___jp_3393_:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_array_get_size(v___y_3394_);
v___x_3396_ = lean_nat_dec_lt(v___x_3391_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; 
lean_dec_ref(v_env_3389_);
v___x_3397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3392_);
lean_ctor_set(v___x_3397_, 1, v___x_3392_);
lean_ctor_set(v___x_3397_, 2, v___y_3394_);
return v___x_3397_;
}
else
{
uint8_t v___x_3398_; 
v___x_3398_ = lean_nat_dec_le(v___x_3395_, v___x_3395_);
if (v___x_3398_ == 0)
{
if (v___x_3396_ == 0)
{
lean_object* v___x_3399_; 
lean_dec_ref(v_env_3389_);
v___x_3399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3392_);
lean_ctor_set(v___x_3399_, 1, v___x_3392_);
lean_ctor_set(v___x_3399_, 2, v___y_3394_);
return v___x_3399_;
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = lean_usize_of_nat(v___x_3395_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3389_, v___y_3394_, v___x_3400_, v___x_3401_, v___x_3392_);
lean_inc_ref(v___x_3402_);
v___x_3403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
lean_ctor_set(v___x_3403_, 2, v___y_3394_);
return v___x_3403_;
}
}
else
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = lean_usize_of_nat(v___x_3395_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3389_, v___y_3394_, v___x_3404_, v___x_3405_, v___x_3392_);
lean_inc_ref(v___x_3406_);
v___x_3407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
lean_ctor_set(v___x_3407_, 2, v___y_3394_);
return v___x_3407_;
}
}
}
v___jp_3410_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3409_, v___x_3408_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
v___y_3394_ = v___x_3413_;
goto v___jp_3393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3421_, lean_object* v_m_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3421_, v_m_3422_);
lean_dec(v_m_3422_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3424_, lean_object* v_p_3425_){
_start:
{
lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3428_; 
v_fst_3426_ = lean_ctor_get(v_p_3425_, 0);
lean_inc(v_fst_3426_);
v_snd_3427_ = lean_ctor_get(v_p_3425_, 1);
lean_inc(v_snd_3427_);
lean_dec_ref(v_p_3425_);
v___x_3428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3426_, v_snd_3427_, v_s_3424_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3429_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3434_, lean_object* v_x_3435_, lean_object* v_x_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3434_, v_x_3435_, v_x_3436_);
lean_dec_ref(v_x_3436_);
lean_dec_ref(v_x_3435_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3439_){
_start:
{
if (lean_obj_tag(v_as_3439_) == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
else
{
lean_object* v_head_3443_; lean_object* v_tail_3444_; lean_object* v___x_3445_; 
v_head_3443_ = lean_ctor_get(v_as_3439_, 0);
lean_inc(v_head_3443_);
v_tail_3444_ = lean_ctor_get(v_as_3439_, 1);
lean_inc(v_tail_3444_);
lean_dec_ref_known(v_as_3439_, 2);
v___x_3445_ = l_Lean_registerBuiltinAttribute(v_head_3443_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_dec_ref_known(v___x_3445_, 1);
v_as_3439_ = v_tail_3444_;
goto _start;
}
else
{
lean_dec(v_tail_3444_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3450_, lean_object* v_snd_3451_, lean_object* v_a_3452_, lean_object* v_fst_3453_, lean_object* v_decl_3454_, lean_object* v_stx_3455_, uint8_t v_kind_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3455_, v___y_3457_, v___y_3458_);
if (lean_obj_tag(v___x_3503_) == 0)
{
uint8_t v___x_3504_; uint8_t v___x_3505_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = 0;
v___x_3505_ = l_Lean_instBEqAttributeKind_beq(v_kind_3456_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v_decl_3454_);
lean_dec_ref(v_a_3452_);
lean_dec(v_snd_3451_);
lean_dec_ref(v_validate_3450_);
v___x_3506_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3453_, v_kind_3456_, v___y_3457_, v___y_3458_);
return v___x_3506_;
}
else
{
v___y_3497_ = v___y_3457_;
v___y_3498_ = v___y_3458_;
goto v___jp_3496_;
}
}
else
{
lean_dec(v_decl_3454_);
lean_dec(v_fst_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_snd_3451_);
lean_dec_ref(v_validate_3450_);
return v___x_3503_;
}
v___jp_3460_:
{
lean_object* v___x_3463_; 
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v_snd_3451_);
lean_inc(v_decl_3454_);
v___x_3463_ = lean_apply_5(v_validate_3450_, v_decl_3454_, v_snd_3451_, v___y_3461_, v___y_3462_, lean_box(0));
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3494_; 
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v___x_3463_, 0);
lean_dec(v_unused_3495_);
v___x_3465_ = v___x_3463_;
v_isShared_3466_ = v_isSharedCheck_3494_;
goto v_resetjp_3464_;
}
else
{
lean_dec(v___x_3463_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3494_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v_toEnvExtension_3468_; lean_object* v_env_3469_; lean_object* v_nextMacroScope_3470_; lean_object* v_ngen_3471_; lean_object* v_auxDeclNGen_3472_; lean_object* v_traceState_3473_; lean_object* v_messages_3474_; lean_object* v_infoState_3475_; lean_object* v_snapshotTasks_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3492_; 
v___x_3467_ = lean_st_ref_take(v___y_3462_);
v_toEnvExtension_3468_ = lean_ctor_get(v_a_3452_, 0);
v_env_3469_ = lean_ctor_get(v___x_3467_, 0);
v_nextMacroScope_3470_ = lean_ctor_get(v___x_3467_, 1);
v_ngen_3471_ = lean_ctor_get(v___x_3467_, 2);
v_auxDeclNGen_3472_ = lean_ctor_get(v___x_3467_, 3);
v_traceState_3473_ = lean_ctor_get(v___x_3467_, 4);
v_messages_3474_ = lean_ctor_get(v___x_3467_, 6);
v_infoState_3475_ = lean_ctor_get(v___x_3467_, 7);
v_snapshotTasks_3476_ = lean_ctor_get(v___x_3467_, 8);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; 
v_unused_3493_ = lean_ctor_get(v___x_3467_, 5);
lean_dec(v_unused_3493_);
v___x_3478_ = v___x_3467_;
v_isShared_3479_ = v_isSharedCheck_3492_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_snapshotTasks_3476_);
lean_inc(v_infoState_3475_);
lean_inc(v_messages_3474_);
lean_inc(v_traceState_3473_);
lean_inc(v_auxDeclNGen_3472_);
lean_inc(v_ngen_3471_);
lean_inc(v_nextMacroScope_3470_);
lean_inc(v_env_3469_);
lean_dec(v___x_3467_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3492_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_asyncMode_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v_asyncMode_3480_ = lean_ctor_get(v_toEnvExtension_3468_, 2);
lean_inc(v_asyncMode_3480_);
lean_inc(v_decl_3454_);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_decl_3454_);
lean_ctor_set(v___x_3481_, 1, v_snd_3451_);
v___x_3482_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3452_, v_env_3469_, v___x_3481_, v_asyncMode_3480_, v_decl_3454_);
lean_dec(v_asyncMode_3480_);
v___x_3483_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 5, v___x_3483_);
lean_ctor_set(v___x_3478_, 0, v___x_3482_);
v___x_3485_ = v___x_3478_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_nextMacroScope_3470_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_ngen_3471_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_auxDeclNGen_3472_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v_traceState_3473_);
lean_ctor_set(v_reuseFailAlloc_3491_, 5, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3491_, 6, v_messages_3474_);
lean_ctor_set(v_reuseFailAlloc_3491_, 7, v_infoState_3475_);
lean_ctor_set(v_reuseFailAlloc_3491_, 8, v_snapshotTasks_3476_);
v___x_3485_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3486_ = lean_st_ref_put(v___y_3462_, v___x_3485_);
v___x_3487_ = lean_box(0);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3487_);
v___x_3489_ = v___x_3465_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
else
{
lean_dec(v_decl_3454_);
lean_dec_ref(v_a_3452_);
lean_dec(v_snd_3451_);
return v___x_3463_;
}
}
v___jp_3496_:
{
lean_object* v___x_3499_; lean_object* v_env_3500_; lean_object* v___x_3501_; 
v___x_3499_ = lean_st_ref_get(v___y_3498_);
v_env_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc_ref(v_env_3500_);
lean_dec(v___x_3499_);
v___x_3501_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3500_, v_decl_3454_);
lean_dec_ref(v_env_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec(v_fst_3453_);
v___y_3461_ = v___y_3497_;
v___y_3462_ = v___y_3498_;
goto v___jp_3460_;
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3501_, 1);
lean_dec_ref(v_a_3452_);
lean_dec(v_snd_3451_);
lean_dec_ref(v_validate_3450_);
v___x_3502_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3453_, v_decl_3454_, v___y_3497_, v___y_3498_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3507_, lean_object* v_snd_3508_, lean_object* v_a_3509_, lean_object* v_fst_3510_, lean_object* v_decl_3511_, lean_object* v_stx_3512_, lean_object* v_kind_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_kind_boxed_3517_; lean_object* v_res_3518_; 
v_kind_boxed_3517_ = lean_unbox(v_kind_3513_);
v_res_3518_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3507_, v_snd_3508_, v_a_3509_, v_fst_3510_, v_decl_3511_, v_stx_3512_, v_kind_boxed_3517_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3519_, lean_object* v_decl_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3524_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3525_ = l_Lean_MessageData_ofName(v_fst_3519_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3528_, v___y_3521_, v___y_3522_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3530_, lean_object* v_decl_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3530_, v_decl_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_decl_3531_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3536_, lean_object* v_a_3537_, lean_object* v_ref_3538_, uint8_t v_applicationTime_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_ref_3538_);
lean_dec_ref(v_a_3537_);
lean_dec_ref(v_validate_3536_);
v___x_3542_ = l_List_reverse___redArg(v_a_3541_);
return v___x_3542_;
}
else
{
lean_object* v_head_3543_; lean_object* v_snd_3544_; lean_object* v_tail_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3560_; 
v_head_3543_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_head_3543_);
v_snd_3544_ = lean_ctor_get(v_head_3543_, 1);
lean_inc(v_snd_3544_);
v_tail_3545_ = lean_ctor_get(v_a_3540_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3540_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_a_3540_, 0);
lean_dec(v_unused_3561_);
v___x_3547_ = v_a_3540_;
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_tail_3545_);
lean_dec(v_a_3540_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_fst_3549_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v___f_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v_fst_3549_ = lean_ctor_get(v_head_3543_, 0);
lean_inc_n(v_fst_3549_, 3);
lean_dec(v_head_3543_);
v_fst_3550_ = lean_ctor_get(v_snd_3544_, 0);
lean_inc(v_fst_3550_);
v_snd_3551_ = lean_ctor_get(v_snd_3544_, 1);
lean_inc(v_snd_3551_);
lean_dec(v_snd_3544_);
v___f_3552_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3552_, 0, v_fst_3549_);
lean_inc_ref(v_a_3537_);
lean_inc_ref(v_validate_3536_);
v___f_3553_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3553_, 0, v_validate_3536_);
lean_closure_set(v___f_3553_, 1, v_snd_3551_);
lean_closure_set(v___f_3553_, 2, v_a_3537_);
lean_closure_set(v___f_3553_, 3, v_fst_3549_);
lean_inc(v_ref_3538_);
v___x_3554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3554_, 0, v_ref_3538_);
lean_ctor_set(v___x_3554_, 1, v_fst_3549_);
lean_ctor_set(v___x_3554_, 2, v_fst_3550_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3, v_applicationTime_3539_);
v___x_3555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___f_3553_);
lean_ctor_set(v___x_3555_, 2, v___f_3552_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3541_);
lean_ctor_set(v___x_3547_, 0, v___x_3555_);
v___x_3557_ = v___x_3547_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_a_3541_);
v___x_3557_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
v_a_3540_ = v_tail_3545_;
v_a_3541_ = v___x_3557_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3562_, lean_object* v_a_3563_, lean_object* v_ref_3564_, lean_object* v_applicationTime_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
uint8_t v_applicationTime_boxed_3568_; lean_object* v_res_3569_; 
v_applicationTime_boxed_3568_ = lean_unbox(v_applicationTime_3565_);
v_res_3569_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3562_, v_a_3563_, v_ref_3564_, v_applicationTime_boxed_3568_, v_a_3566_, v_a_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3583_, lean_object* v_validate_3584_, uint8_t v_applicationTime_3585_, lean_object* v_ref_3586_){
_start:
{
lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___f_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3591_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3592_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3593_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3594_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3595_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3586_);
v___x_3596_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3596_, 0, v_ref_3586_);
lean_ctor_set(v___x_3596_, 1, v___f_3592_);
lean_ctor_set(v___x_3596_, 2, v___f_3593_);
lean_ctor_set(v___x_3596_, 3, v___f_3591_);
lean_ctor_set(v___x_3596_, 4, v___f_3590_);
lean_ctor_set(v___x_3596_, 5, v___f_3589_);
lean_ctor_set(v___x_3596_, 6, v___x_3594_);
lean_ctor_set(v___x_3596_, 7, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___f_3588_);
v___x_3598_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc_n(v_a_3599_, 2);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3584_, v_a_3599_, v_ref_3586_, v_applicationTime_3585_, v_attrDescrs_3583_, v___x_3600_);
lean_inc(v___x_3601_);
v___x_3602_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3610_; 
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v___x_3602_, 0);
lean_dec(v_unused_3611_);
v___x_3604_ = v___x_3602_;
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v___x_3602_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
lean_ctor_set(v___x_3606_, 1, v_a_3599_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3606_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v___x_3601_);
lean_dec(v_a_3599_);
v_a_3612_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3602_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_ref_3586_);
lean_dec_ref(v_validate_3584_);
lean_dec(v_attrDescrs_3583_);
v_a_3620_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3598_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3598_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3628_, lean_object* v_validate_3629_, lean_object* v_applicationTime_3630_, lean_object* v_ref_3631_, lean_object* v_a_3632_){
_start:
{
uint8_t v_applicationTime_boxed_3633_; lean_object* v_res_3634_; 
v_applicationTime_boxed_3633_ = lean_unbox(v_applicationTime_3630_);
v_res_3634_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3628_, v_validate_3629_, v_applicationTime_boxed_3633_, v_ref_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3635_, lean_object* v_attrDescrs_3636_, lean_object* v_validate_3637_, uint8_t v_applicationTime_3638_, lean_object* v_ref_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3636_, v_validate_3637_, v_applicationTime_3638_, v_ref_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3642_, lean_object* v_attrDescrs_3643_, lean_object* v_validate_3644_, lean_object* v_applicationTime_3645_, lean_object* v_ref_3646_, lean_object* v_a_3647_){
_start:
{
uint8_t v_applicationTime_boxed_3648_; lean_object* v_res_3649_; 
v_applicationTime_boxed_3648_ = lean_unbox(v_applicationTime_3645_);
v_res_3649_ = l_Lean_registerEnumAttributes(v_00_u03b1_3642_, v_attrDescrs_3643_, v_validate_3644_, v_applicationTime_boxed_3648_, v_ref_3646_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3650_, lean_object* v_env_3651_, lean_object* v_as_3652_, size_t v_i_3653_, size_t v_stop_3654_, lean_object* v_b_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3651_, v_as_3652_, v_i_3653_, v_stop_3654_, v_b_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3657_, lean_object* v_env_3658_, lean_object* v_as_3659_, lean_object* v_i_3660_, lean_object* v_stop_3661_, lean_object* v_b_3662_){
_start:
{
size_t v_i_boxed_3663_; size_t v_stop_boxed_3664_; lean_object* v_res_3665_; 
v_i_boxed_3663_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_stop_boxed_3664_ = lean_unbox_usize(v_stop_3661_);
lean_dec(v_stop_3661_);
v_res_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3657_, v_env_3658_, v_as_3659_, v_i_boxed_3663_, v_stop_boxed_3664_, v_b_3662_);
lean_dec_ref(v_as_3659_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3666_, lean_object* v_newState_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3667_, v_x_3668_, v_x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3671_, lean_object* v_newState_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3671_, v_newState_3672_, v_x_3673_, v_x_3674_);
lean_dec(v_newState_3672_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3676_, lean_object* v_validate_3677_, lean_object* v_a_3678_, lean_object* v_ref_3679_, uint8_t v_applicationTime_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3677_, v_a_3678_, v_ref_3679_, v_applicationTime_3680_, v_a_3681_, v_a_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3684_, lean_object* v_validate_3685_, lean_object* v_a_3686_, lean_object* v_ref_3687_, lean_object* v_applicationTime_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
uint8_t v_applicationTime_boxed_3691_; lean_object* v_res_3692_; 
v_applicationTime_boxed_3691_ = lean_unbox(v_applicationTime_3688_);
v_res_3692_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3684_, v_validate_3685_, v_a_3686_, v_ref_3687_, v_applicationTime_boxed_3691_, v_a_3689_, v_a_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3693_, lean_object* v_attr_3694_, lean_object* v_env_3695_, lean_object* v_decl_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_box(1);
v___x_3698_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3695_, v_decl_3696_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_ext_3699_; lean_object* v_toEnvExtension_3700_; lean_object* v_asyncMode_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v_inst_3693_);
v_ext_3699_ = lean_ctor_get(v_attr_3694_, 1);
lean_inc_ref(v_ext_3699_);
lean_dec_ref(v_attr_3694_);
v_toEnvExtension_3700_ = lean_ctor_get(v_ext_3699_, 0);
v_asyncMode_3701_ = lean_ctor_get(v_toEnvExtension_3700_, 2);
lean_inc(v_asyncMode_3701_);
lean_inc(v_decl_3696_);
v___x_3702_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3697_, v_ext_3699_, v_env_3695_, v_asyncMode_3701_, v_decl_3696_);
lean_dec(v_asyncMode_3701_);
lean_dec_ref(v_ext_3699_);
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3702_, v_decl_3696_);
lean_dec(v_decl_3696_);
lean_dec(v___x_3702_);
return v___x_3703_;
}
else
{
lean_object* v_val_3704_; lean_object* v_ext_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3735_; 
v_val_3704_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_val_3704_);
lean_dec_ref_known(v___x_3698_, 1);
v_ext_3705_ = lean_ctor_get(v_attr_3694_, 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_attr_3694_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_attr_3694_, 0);
lean_dec(v_unused_3736_);
v___x_3707_ = v_attr_3694_;
v_isShared_3708_ = v_isSharedCheck_3735_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_ext_3705_);
lean_dec(v_attr_3694_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3735_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3709_ = 0;
v___x_3710_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3697_, v_ext_3705_, v_env_3695_, v_val_3704_, v___x_3709_);
lean_dec(v_val_3704_);
lean_dec_ref(v_env_3695_);
lean_dec_ref(v_ext_3705_);
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v___x_3710_);
v___x_3713_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v___x_3710_);
lean_del_object(v___x_3707_);
lean_dec(v_decl_3696_);
lean_dec(v_inst_3693_);
v___x_3714_ = lean_box(0);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_nat_sub(v___x_3712_, v___x_3715_);
v___x_3717_ = lean_nat_dec_le(v___x_3711_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_dec(v___x_3716_);
lean_dec_ref(v___x_3710_);
lean_del_object(v___x_3707_);
lean_dec(v_decl_3696_);
lean_dec(v_inst_3693_);
v___x_3718_ = lean_box(0);
return v___x_3718_;
}
else
{
lean_object* v___f_3719_; lean_object* v___x_3721_; 
v___f_3719_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 1, v_inst_3693_);
lean_ctor_set(v___x_3707_, 0, v_decl_3696_);
v___x_3721_ = v___x_3707_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_decl_3696_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_inst_3693_);
v___x_3721_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3723_ = l_Array_binSearchAux___redArg(v___f_3719_, v___x_3722_, v___x_3710_, v___x_3721_, v___x_3711_, v___x_3716_);
lean_dec_ref(v___x_3710_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_box(0);
return v___x_3724_;
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3733_; 
v_val_3725_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3727_ = v___x_3723_;
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_val_3725_);
lean_dec(v___x_3723_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; 
v_snd_3729_ = lean_ctor_get(v_val_3725_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_val_3725_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v_snd_3729_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_snd_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3737_, lean_object* v_inst_3738_, lean_object* v_attr_3739_, lean_object* v_env_3740_, lean_object* v_decl_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3738_, v_attr_3739_, v_env_3740_, v_decl_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3751_, lean_object* v_env_3752_, lean_object* v_decl_3753_, lean_object* v_val_3754_){
_start:
{
lean_object* v_ext_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3818_; 
v_ext_3755_ = lean_ctor_get(v_attrs_3751_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_attrs_3751_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_attrs_3751_, 0);
lean_dec(v_unused_3819_);
v___x_3757_ = v_attrs_3751_;
v_isShared_3758_ = v_isSharedCheck_3818_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_ext_3755_);
lean_dec(v_attrs_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3818_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_toEnvExtension_3759_; lean_object* v_name_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v_pfx_3770_; lean_object* v___x_3771_; 
v_toEnvExtension_3759_ = lean_ctor_get(v_ext_3755_, 0);
v_name_3760_ = lean_ctor_get(v_ext_3755_, 1);
v___x_3761_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3762_ = 1;
lean_inc(v_name_3760_);
v___x_3763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3760_, v___x_3762_);
v___x_3764_ = lean_string_append(v___x_3761_, v___x_3763_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
lean_inc(v_decl_3753_);
v___x_3767_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3753_, v___x_3762_);
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
v___x_3771_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3752_, v_decl_3753_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_asyncMode_3772_; uint8_t v___x_3773_; 
v_asyncMode_3772_ = lean_ctor_get(v_toEnvExtension_3759_, 2);
lean_inc(v_asyncMode_3772_);
lean_inc(v_decl_3753_);
lean_inc_ref(v_env_3752_);
v___x_3773_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3752_, v_decl_3753_, v_asyncMode_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___y_3777_; lean_object* v___x_3781_; 
lean_dec(v_asyncMode_3772_);
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
v___x_3774_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3775_ = lean_string_append(v_pfx_3770_, v___x_3774_);
v___x_3781_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3752_);
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
v___x_3785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3783_, v___x_3762_);
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
v___x_3779_ = lean_string_append(v___x_3778_, v___x_3769_);
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_box(1);
lean_inc(v_decl_3753_);
lean_inc_ref(v_env_3752_);
v___x_3791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3790_, v_ext_3755_, v_env_3752_, v_asyncMode_3772_, v_decl_3753_);
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3791_, v_decl_3753_);
lean_dec(v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; 
lean_dec_ref(v_pfx_3770_);
lean_inc(v_decl_3753_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v_val_3754_);
lean_ctor_set(v___x_3757_, 0, v_decl_3753_);
v___x_3794_ = v___x_3757_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_decl_3753_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_val_3754_);
v___x_3794_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3755_, v_env_3752_, v___x_3794_, v_asyncMode_3772_, v_decl_3753_);
lean_dec(v_asyncMode_3772_);
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
return v___x_3796_;
}
}
else
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_asyncMode_3772_);
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
lean_dec_ref(v_env_3752_);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; 
v_unused_3807_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3807_);
v___x_3799_ = v___x_3792_;
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v___x_3792_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3801_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3802_ = lean_string_append(v_pfx_3770_, v___x_3801_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3802_);
v___x_3804_ = v___x_3799_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
lean_dec_ref(v_env_3752_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3771_, 0);
lean_dec(v_unused_3817_);
v___x_3809_ = v___x_3771_;
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v___x_3771_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3811_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3812_ = lean_string_append(v_pfx_3770_, v___x_3811_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3820_, lean_object* v_attrs_3821_, lean_object* v_env_3822_, lean_object* v_decl_3823_, lean_object* v_val_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3821_, v_env_3822_, v_decl_3823_, v_val_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3828_ = lean_st_mk_ref(v___x_3827_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3834_, lean_object* v_builder_3835_){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3837_ = l_Lean_attributeImplBuilderTableRef;
v___x_3838_ = lean_st_ref_get(v___x_3837_);
v___x_3839_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3838_, v_builderId_3834_);
lean_dec(v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3840_ = lean_st_ref_take(v___x_3837_);
v___x_3841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3840_, v_builderId_3834_, v_builder_3835_);
v___x_3842_ = lean_st_ref_put(v___x_3837_, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec_ref(v_builder_3835_);
v___x_3844_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3834_, v___x_3839_);
v___x_3846_ = lean_string_append(v___x_3844_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3848_ = lean_string_append(v___x_3846_, v___x_3847_);
v___x_3849_ = lean_mk_io_user_error(v___x_3848_);
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3851_, lean_object* v_builder_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_registerAttributeImplBuilder(v_builderId_3851_, v_builder_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3855_){
_start:
{
if (lean_obj_tag(v_e_3855_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3865_; 
v_a_3857_ = lean_ctor_get(v_e_3855_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_e_3855_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3859_ = v_e_3855_;
v_isShared_3860_ = v_isSharedCheck_3865_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v_e_3855_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3865_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_mk_io_user_error(v_a_3857_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set_tag(v___x_3859_, 1);
lean_ctor_set(v___x_3859_, 0, v___x_3861_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
v_a_3866_ = lean_ctor_get(v_e_3855_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_e_3855_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v_e_3855_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v_e_3855_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 0);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3877_, lean_object* v_e_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3881_, lean_object* v_e_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3881_, v_e_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3885_, lean_object* v_x_3886_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_box(0);
return v___x_3887_;
}
else
{
lean_object* v_key_3888_; lean_object* v_value_3889_; lean_object* v_tail_3890_; uint8_t v___x_3891_; 
v_key_3888_ = lean_ctor_get(v_x_3886_, 0);
v_value_3889_ = lean_ctor_get(v_x_3886_, 1);
v_tail_3890_ = lean_ctor_get(v_x_3886_, 2);
v___x_3891_ = lean_name_eq(v_key_3888_, v_a_3885_);
if (v___x_3891_ == 0)
{
v_x_3886_ = v_tail_3890_;
goto _start;
}
else
{
lean_object* v___x_3893_; 
lean_inc(v_value_3889_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v_value_3889_);
return v___x_3893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3894_, v_x_3895_);
lean_dec(v_x_3895_);
lean_dec(v_a_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_buckets_3899_; lean_object* v___x_3900_; uint64_t v___y_3902_; 
v_buckets_3899_ = lean_ctor_get(v_m_3897_, 1);
v___x_3900_ = lean_array_get_size(v_buckets_3899_);
if (lean_obj_tag(v_a_3898_) == 0)
{
uint64_t v___x_3916_; 
v___x_3916_ = 1723ULL;
v___y_3902_ = v___x_3916_;
goto v___jp_3901_;
}
else
{
uint64_t v_hash_3917_; 
v_hash_3917_ = lean_ctor_get_uint64(v_a_3898_, sizeof(void*)*2);
v___y_3902_ = v_hash_3917_;
goto v___jp_3901_;
}
v___jp_3901_:
{
uint64_t v___x_3903_; uint64_t v___x_3904_; uint64_t v_fold_3905_; uint64_t v___x_3906_; uint64_t v___x_3907_; uint64_t v___x_3908_; size_t v___x_3909_; size_t v___x_3910_; size_t v___x_3911_; size_t v___x_3912_; size_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3903_ = 32ULL;
v___x_3904_ = lean_uint64_shift_right(v___y_3902_, v___x_3903_);
v_fold_3905_ = lean_uint64_xor(v___y_3902_, v___x_3904_);
v___x_3906_ = 16ULL;
v___x_3907_ = lean_uint64_shift_right(v_fold_3905_, v___x_3906_);
v___x_3908_ = lean_uint64_xor(v_fold_3905_, v___x_3907_);
v___x_3909_ = lean_uint64_to_usize(v___x_3908_);
v___x_3910_ = lean_usize_of_nat(v___x_3900_);
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_sub(v___x_3910_, v___x_3911_);
v___x_3913_ = lean_usize_land(v___x_3909_, v___x_3912_);
v___x_3914_ = lean_array_uget_borrowed(v_buckets_3899_, v___x_3913_);
v___x_3915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3898_, v___x_3914_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3918_, v_a_3919_);
lean_dec(v_a_3919_);
lean_dec_ref(v_m_3918_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3922_){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v_builderId_3926_; lean_object* v_ref_3927_; lean_object* v_args_3928_; lean_object* v___x_3929_; 
v___x_3924_ = l_Lean_attributeImplBuilderTableRef;
v___x_3925_ = lean_st_ref_get(v___x_3924_);
v_builderId_3926_ = lean_ctor_get(v_e_3922_, 0);
lean_inc(v_builderId_3926_);
v_ref_3927_ = lean_ctor_get(v_e_3922_, 1);
lean_inc(v_ref_3927_);
v_args_3928_ = lean_ctor_get(v_e_3922_, 2);
lean_inc(v_args_3928_);
lean_dec_ref(v_e_3922_);
v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3925_, v_builderId_3926_);
lean_dec(v___x_3925_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v_args_3928_);
lean_dec(v_ref_3927_);
v___x_3930_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3931_ = 1;
v___x_3932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3926_, v___x_3931_);
v___x_3933_ = lean_string_append(v___x_3930_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3935_ = lean_string_append(v___x_3933_, v___x_3934_);
v___x_3936_ = lean_mk_io_user_error(v___x_3935_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v_builderId_3926_);
v_val_3938_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3939_ = lean_apply_2(v_val_3938_, v_ref_3927_, v_args_3928_);
v___x_3940_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_mkAttributeImplOfEntry(v_e_3941_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3944_, lean_object* v_m_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3945_, v_a_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3948_, lean_object* v_m_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3948_, v_m_3949_, v_a_3950_);
lean_dec(v_a_3950_);
lean_dec_ref(v_m_3949_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3952_, lean_object* v_a_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3953_, v_x_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3956_, lean_object* v_a_3957_, lean_object* v_x_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3956_, v_a_3957_, v_x_3958_);
lean_dec(v_x_3958_);
lean_dec(v_a_3957_);
return v_res_3959_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3960_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3963_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3966_ = l_Lean_attributeMapRef;
v___x_3967_ = lean_st_ref_get(v___x_3966_);
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v___x_3967_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3978_, lean_object* v_opts_3979_, lean_object* v_declName_3980_){
_start:
{
uint8_t v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = 0;
lean_inc(v_declName_3980_);
lean_inc_ref(v_env_3978_);
v___x_3984_ = l_Lean_Environment_find_x3f(v_env_3978_, v_declName_3980_, v___x_3983_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec_ref(v_env_3978_);
v___x_3985_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3986_ = 1;
v___x_3987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3980_, v___x_3986_);
v___x_3988_ = lean_string_append(v___x_3985_, v___x_3987_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3990_ = lean_string_append(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
else
{
lean_object* v_val_3992_; lean_object* v___x_3993_; 
v_val_3992_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3993_ = l_Lean_ConstantInfo_type(v_val_3992_);
lean_dec(v_val_3992_);
if (lean_obj_tag(v___x_3993_) == 4)
{
lean_object* v_declName_3994_; 
v_declName_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_declName_3994_);
lean_dec_ref_known(v___x_3993_, 2);
if (lean_obj_tag(v_declName_3994_) == 1)
{
lean_object* v_pre_3995_; 
v_pre_3995_ = lean_ctor_get(v_declName_3994_, 0);
lean_inc(v_pre_3995_);
if (lean_obj_tag(v_pre_3995_) == 1)
{
lean_object* v_pre_3996_; 
v_pre_3996_ = lean_ctor_get(v_pre_3995_, 0);
if (lean_obj_tag(v_pre_3996_) == 0)
{
lean_object* v_str_3997_; lean_object* v_str_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v_str_3997_ = lean_ctor_get(v_declName_3994_, 1);
lean_inc_ref(v_str_3997_);
lean_dec_ref_known(v_declName_3994_, 2);
v_str_3998_ = lean_ctor_get(v_pre_3995_, 1);
lean_inc_ref(v_str_3998_);
lean_dec_ref_known(v_pre_3995_, 2);
v___x_3999_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4000_ = lean_string_dec_eq(v_str_3998_, v___x_3999_);
lean_dec_ref(v_str_3998_);
if (v___x_4000_ == 0)
{
lean_dec_ref(v_str_3997_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
else
{
lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4001_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4002_ = lean_string_dec_eq(v_str_3997_, v___x_4001_);
lean_dec_ref(v_str_3997_);
if (v___x_4002_ == 0)
{
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
else
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Environment_evalConst___redArg(v_env_3978_, v_opts_3979_, v_declName_3980_, v___x_4002_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
return v___x_4003_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3995_, 2);
lean_dec_ref_known(v_declName_3994_, 2);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v_pre_3995_);
lean_dec_ref_known(v_declName_3994_, 2);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v_declName_3994_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec_ref(v___x_3993_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
v___jp_3981_:
{
lean_object* v___x_3982_; 
v___x_3982_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4004_, lean_object* v_opts_4005_, lean_object* v_declName_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4004_, v_opts_4005_, v_declName_4006_);
lean_dec_ref(v_opts_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4008_, size_t v_i_4009_, size_t v_stop_4010_, lean_object* v_b_4011_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_eq(v_i_4009_, v_stop_4010_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_array_uget_borrowed(v_as_4008_, v_i_4009_);
lean_inc(v___x_4014_);
v___x_4015_ = l_Lean_mkAttributeImplOfEntry(v___x_4014_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v_toAttributeImplCore_4017_; lean_object* v_name_4018_; lean_object* v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v_toAttributeImplCore_4017_ = lean_ctor_get(v_a_4016_, 0);
v_name_4018_ = lean_ctor_get(v_toAttributeImplCore_4017_, 1);
lean_inc(v_name_4018_);
v___x_4019_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4011_, v_name_4018_, v_a_4016_);
v___x_4020_ = ((size_t)1ULL);
v___x_4021_ = lean_usize_add(v_i_4009_, v___x_4020_);
v_i_4009_ = v___x_4021_;
v_b_4011_ = v___x_4019_;
goto _start;
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v_b_4011_);
v_a_4023_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4015_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4015_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_b_4011_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4032_, lean_object* v_i_4033_, lean_object* v_stop_4034_, lean_object* v_b_4035_, lean_object* v___y_4036_){
_start:
{
size_t v_i_boxed_4037_; size_t v_stop_boxed_4038_; lean_object* v_res_4039_; 
v_i_boxed_4037_ = lean_unbox_usize(v_i_4033_);
lean_dec(v_i_4033_);
v_stop_boxed_4038_ = lean_unbox_usize(v_stop_4034_);
lean_dec(v_stop_4034_);
v_res_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4032_, v_i_boxed_4037_, v_stop_boxed_4038_, v_b_4035_);
lean_dec_ref(v_as_4032_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4040_, size_t v_i_4041_, size_t v_stop_4042_, lean_object* v_b_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_a_4047_; lean_object* v___y_4052_; uint8_t v___x_4054_; 
v___x_4054_ = lean_usize_dec_eq(v_i_4041_, v_stop_4042_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4055_ = lean_array_uget_borrowed(v_as_4040_, v_i_4041_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = lean_array_get_size(v___x_4055_);
v___x_4058_ = lean_nat_dec_lt(v___x_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
v_a_4047_ = v_b_4043_;
goto v___jp_4046_;
}
else
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_nat_dec_le(v___x_4057_, v___x_4057_);
if (v___x_4059_ == 0)
{
if (v___x_4058_ == 0)
{
v_a_4047_ = v_b_4043_;
goto v___jp_4046_;
}
else
{
size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = ((size_t)0ULL);
v___x_4061_ = lean_usize_of_nat(v___x_4057_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4055_, v___x_4060_, v___x_4061_, v_b_4043_);
v___y_4052_ = v___x_4062_;
goto v___jp_4051_;
}
}
else
{
size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((size_t)0ULL);
v___x_4064_ = lean_usize_of_nat(v___x_4057_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4055_, v___x_4063_, v___x_4064_, v_b_4043_);
v___y_4052_ = v___x_4065_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_b_4043_);
return v___x_4066_;
}
v___jp_4046_:
{
size_t v___x_4048_; size_t v___x_4049_; 
v___x_4048_ = ((size_t)1ULL);
v___x_4049_ = lean_usize_add(v_i_4041_, v___x_4048_);
v_i_4041_ = v___x_4049_;
v_b_4043_ = v_a_4047_;
goto _start;
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4052_) == 0)
{
lean_object* v_a_4053_; 
v_a_4053_ = lean_ctor_get(v___y_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___y_4052_, 1);
v_a_4047_ = v_a_4053_;
goto v___jp_4046_;
}
else
{
return v___y_4052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4067_, lean_object* v_i_4068_, lean_object* v_stop_4069_, lean_object* v_b_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_i_boxed_4073_; size_t v_stop_boxed_4074_; lean_object* v_res_4075_; 
v_i_boxed_4073_ = lean_unbox_usize(v_i_4068_);
lean_dec(v_i_4068_);
v_stop_boxed_4074_ = lean_unbox_usize(v_stop_4069_);
lean_dec(v_stop_4069_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4067_, v_i_boxed_4073_, v_stop_boxed_4074_, v_b_4070_, v___y_4071_);
lean_dec_ref(v___y_4071_);
lean_dec_ref(v_as_4067_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_a_4080_; lean_object* v___y_4085_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4095_ = l_Lean_attributeMapRef;
v___x_4096_ = lean_st_ref_get(v___x_4095_);
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = lean_array_get_size(v_es_4076_);
v___x_4099_ = lean_nat_dec_lt(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
v_a_4080_ = v___x_4096_;
goto v___jp_4079_;
}
else
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_nat_dec_le(v___x_4098_, v___x_4098_);
if (v___x_4100_ == 0)
{
if (v___x_4099_ == 0)
{
v_a_4080_ = v___x_4096_;
goto v___jp_4079_;
}
else
{
size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = ((size_t)0ULL);
v___x_4102_ = lean_usize_of_nat(v___x_4098_);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4076_, v___x_4101_, v___x_4102_, v___x_4096_, v_a_4077_);
v___y_4085_ = v___x_4103_;
goto v___jp_4084_;
}
}
else
{
size_t v___x_4104_; size_t v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = ((size_t)0ULL);
v___x_4105_ = lean_usize_of_nat(v___x_4098_);
v___x_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4076_, v___x_4104_, v___x_4105_, v___x_4096_, v_a_4077_);
v___y_4085_ = v___x_4106_;
goto v___jp_4084_;
}
}
v___jp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = lean_box(0);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_a_4080_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
v___jp_4084_:
{
if (lean_obj_tag(v___y_4085_) == 0)
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___y_4085_, 1);
v_a_4080_ = v_a_4086_;
goto v___jp_4079_;
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___y_4085_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___y_4085_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___y_4085_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___y_4085_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4107_, v_a_4108_);
lean_dec_ref(v_a_4108_);
lean_dec_ref(v_es_4107_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4111_, size_t v_i_4112_, size_t v_stop_4113_, lean_object* v_b_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4111_, v_i_4112_, v_stop_4113_, v_b_4114_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4118_, lean_object* v_i_4119_, lean_object* v_stop_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
size_t v_i_boxed_4124_; size_t v_stop_boxed_4125_; lean_object* v_res_4126_; 
v_i_boxed_4124_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_stop_boxed_4125_ = lean_unbox_usize(v_stop_4120_);
lean_dec(v_stop_4120_);
v_res_4126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4118_, v_i_boxed_4124_, v_stop_boxed_4125_, v_b_4121_, v___y_4122_);
lean_dec_ref(v___y_4122_);
lean_dec_ref(v_as_4118_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4127_, lean_object* v_e_4128_){
_start:
{
lean_object* v_snd_4129_; lean_object* v_toAttributeImplCore_4130_; lean_object* v_fst_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4149_; 
v_snd_4129_ = lean_ctor_get(v_e_4128_, 1);
lean_inc(v_snd_4129_);
v_toAttributeImplCore_4130_ = lean_ctor_get(v_snd_4129_, 0);
v_fst_4131_ = lean_ctor_get(v_e_4128_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_e_4128_);
if (v_isSharedCheck_4149_ == 0)
{
lean_object* v_unused_4150_; 
v_unused_4150_ = lean_ctor_get(v_e_4128_, 1);
lean_dec(v_unused_4150_);
v___x_4133_ = v_e_4128_;
v_isShared_4134_ = v_isSharedCheck_4149_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_fst_4131_);
lean_dec(v_e_4128_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4149_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_newEntries_4135_; lean_object* v_map_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4148_; 
v_newEntries_4135_ = lean_ctor_get(v_s_4127_, 0);
v_map_4136_ = lean_ctor_get(v_s_4127_, 1);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_s_4127_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4138_ = v_s_4127_;
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_map_4136_);
lean_inc(v_newEntries_4135_);
lean_dec(v_s_4127_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v_name_4140_; lean_object* v___x_4142_; 
v_name_4140_ = lean_ctor_get(v_toAttributeImplCore_4130_, 1);
lean_inc(v_name_4140_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 1);
lean_ctor_set(v___x_4133_, 1, v_newEntries_4135_);
v___x_4142_ = v___x_4133_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_fst_4131_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_newEntries_4135_);
v___x_4142_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4136_, v_name_4140_, v_snd_4129_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 1, v___x_4143_);
lean_ctor_set(v___x_4138_, 0, v___x_4142_);
v___x_4145_ = v___x_4138_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4151_, lean_object* v_s_4152_){
_start:
{
lean_object* v_newEntries_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_newEntries_4153_ = lean_ctor_get(v_s_4152_, 0);
lean_inc(v_newEntries_4153_);
lean_dec_ref(v_s_4152_);
v___x_4154_ = l_List_reverse___redArg(v_newEntries_4153_);
v___x_4155_ = lean_array_mk(v___x_4154_);
lean_inc_ref_n(v___x_4155_, 2);
v___x_4156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4157_, lean_object* v_s_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4157_, v_s_4158_);
lean_dec_ref(v_x_4157_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4160_){
_start:
{
lean_object* v_newEntries_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4172_; 
v_newEntries_4161_ = lean_ctor_get(v_s_4160_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v_s_4160_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; 
v_unused_4173_ = lean_ctor_get(v_s_4160_, 1);
lean_dec(v_unused_4173_);
v___x_4163_ = v_s_4160_;
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_newEntries_4161_);
lean_dec(v_s_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4165_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4166_ = l_List_lengthTR___redArg(v_newEntries_4161_);
lean_dec(v_newEntries_4161_);
v___x_4167_ = l_Nat_reprFast(v___x_4166_);
v___x_4168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set_tag(v___x_4163_, 5);
lean_ctor_set(v___x_4163_, 1, v___x_4168_);
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4170_ = v___x_4163_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4174_){
_start:
{
lean_object* v_newEntries_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_newEntries_4175_ = lean_ctor_get(v_s_4174_, 0);
lean_inc(v_newEntries_4175_);
lean_dec_ref(v_s_4174_);
v___x_4176_ = l_List_reverse___redArg(v_newEntries_4175_);
v___x_4177_ = lean_array_mk(v___x_4176_);
return v___x_4177_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___f_4189_; lean_object* v___f_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4187_ = lean_box(0);
v___x_4188_ = lean_box(2);
v___f_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4190_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4191_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4192_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4193_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4194_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4195_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4193_);
lean_ctor_set(v___x_4195_, 2, v___x_4192_);
lean_ctor_set(v___x_4195_, 3, v___x_4191_);
lean_ctor_set(v___x_4195_, 4, v___f_4190_);
lean_ctor_set(v___x_4195_, 5, v___f_4189_);
lean_ctor_set(v___x_4195_, 6, v___x_4188_);
lean_ctor_set(v___x_4195_, 7, v___x_4187_);
return v___x_4195_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___f_4196_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4197_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set(v___x_4198_, 1, v___f_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4201_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4206_ = l_Lean_attributeMapRef;
v___x_4207_ = lean_st_ref_get(v___x_4206_);
v___x_4208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4207_, v_n_4204_);
lean_dec(v___x_4207_);
v___x_4209_ = lean_box(v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_isBuiltinAttribute(v_n_4211_);
lean_dec(v_n_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4214_, lean_object* v_x_4215_){
_start:
{
if (lean_obj_tag(v_x_4215_) == 0)
{
return v_x_4214_;
}
else
{
lean_object* v_key_4216_; lean_object* v_tail_4217_; lean_object* v___x_4218_; 
v_key_4216_ = lean_ctor_get(v_x_4215_, 0);
v_tail_4217_ = lean_ctor_get(v_x_4215_, 2);
lean_inc(v_key_4216_);
v___x_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4218_, 0, v_key_4216_);
lean_ctor_set(v___x_4218_, 1, v_x_4214_);
v_x_4214_ = v___x_4218_;
v_x_4215_ = v_tail_4217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4220_, lean_object* v_x_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4220_, v_x_4221_);
lean_dec(v_x_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4223_, size_t v_i_4224_, size_t v_stop_4225_, lean_object* v_b_4226_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_eq(v_i_4224_, v_stop_4225_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; size_t v___x_4230_; size_t v___x_4231_; 
v___x_4228_ = lean_array_uget_borrowed(v_as_4223_, v_i_4224_);
v___x_4229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4226_, v___x_4228_);
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_i_4224_, v___x_4230_);
v_i_4224_ = v___x_4231_;
v_b_4226_ = v___x_4229_;
goto _start;
}
else
{
return v_b_4226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4233_, lean_object* v_i_4234_, lean_object* v_stop_4235_, lean_object* v_b_4236_){
_start:
{
size_t v_i_boxed_4237_; size_t v_stop_boxed_4238_; lean_object* v_res_4239_; 
v_i_boxed_4237_ = lean_unbox_usize(v_i_4234_);
lean_dec(v_i_4234_);
v_stop_boxed_4238_ = lean_unbox_usize(v_stop_4235_);
lean_dec(v_stop_4235_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4233_, v_i_boxed_4237_, v_stop_boxed_4238_, v_b_4236_);
lean_dec_ref(v_as_4233_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v_buckets_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v___x_4241_ = l_Lean_attributeMapRef;
v___x_4242_ = lean_st_ref_get(v___x_4241_);
v_buckets_4243_ = lean_ctor_get(v___x_4242_, 1);
lean_inc_ref(v_buckets_4243_);
lean_dec(v___x_4242_);
v___x_4244_ = lean_box(0);
v___x_4245_ = lean_unsigned_to_nat(0u);
v___x_4246_ = lean_array_get_size(v_buckets_4243_);
v___x_4247_ = lean_nat_dec_lt(v___x_4245_, v___x_4246_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; 
lean_dec_ref(v_buckets_4243_);
v___x_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4244_);
return v___x_4248_;
}
else
{
size_t v___x_4249_; size_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4249_ = ((size_t)0ULL);
v___x_4250_ = lean_usize_of_nat(v___x_4246_);
v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4243_, v___x_4249_, v___x_4250_, v___x_4244_);
lean_dec_ref(v_buckets_4243_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_getBuiltinAttributeNames();
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = l_Lean_attributeMapRef;
v___x_4259_ = lean_st_ref_get(v___x_4258_);
v___x_4260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4259_, v_attrName_4256_);
lean_dec(v___x_4259_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4261_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4262_ = 1;
v___x_4263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4256_, v___x_4262_);
v___x_4264_ = lean_string_append(v___x_4261_, v___x_4263_);
lean_dec_ref(v___x_4263_);
v___x_4265_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
v___x_4267_ = lean_mk_io_user_error(v___x_4266_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
return v___x_4268_;
}
else
{
lean_object* v_val_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_attrName_4256_);
v_val_4269_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4260_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_val_4269_);
lean_dec(v___x_4260_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
lean_ctor_set_tag(v___x_4271_, 0);
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_val_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4280_, lean_object* v_attrName_4281_){
_start:
{
lean_object* v___x_4282_; lean_object* v_toEnvExtension_4283_; lean_object* v_asyncMode_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_map_4288_; uint8_t v___x_4289_; 
v___x_4282_ = l_Lean_attributeExtension;
v_toEnvExtension_4283_ = lean_ctor_get(v___x_4282_, 0);
v_asyncMode_4284_ = lean_ctor_get(v_toEnvExtension_4283_, 2);
v___x_4285_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4286_ = lean_box(0);
v___x_4287_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4285_, v___x_4282_, v_env_4280_, v_asyncMode_4284_, v___x_4286_);
v_map_4288_ = lean_ctor_get(v___x_4287_, 1);
lean_inc_ref(v_map_4288_);
lean_dec(v___x_4287_);
v___x_4289_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4288_, v_attrName_4281_);
lean_dec_ref(v_map_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4290_, lean_object* v_attrName_4291_){
_start:
{
uint8_t v_res_4292_; lean_object* v_r_4293_; 
v_res_4292_ = l_Lean_isAttribute(v_env_4290_, v_attrName_4291_);
lean_dec(v_attrName_4291_);
v_r_4293_ = lean_box(v_res_4292_);
return v_r_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4294_){
_start:
{
lean_object* v___x_4295_; lean_object* v_toEnvExtension_4296_; lean_object* v_asyncMode_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v_map_4301_; lean_object* v_buckets_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4295_ = l_Lean_attributeExtension;
v_toEnvExtension_4296_ = lean_ctor_get(v___x_4295_, 0);
v_asyncMode_4297_ = lean_ctor_get(v_toEnvExtension_4296_, 2);
v___x_4298_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4299_ = lean_box(0);
v___x_4300_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4298_, v___x_4295_, v_env_4294_, v_asyncMode_4297_, v___x_4299_);
v_map_4301_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_map_4301_);
lean_dec(v___x_4300_);
v_buckets_4302_ = lean_ctor_get(v_map_4301_, 1);
lean_inc_ref(v_buckets_4302_);
lean_dec_ref(v_map_4301_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_get_size(v_buckets_4302_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v_buckets_4302_);
return v___x_4303_;
}
else
{
size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((size_t)0ULL);
v___x_4308_ = lean_usize_of_nat(v___x_4305_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4302_, v___x_4307_, v___x_4308_, v___x_4303_);
lean_dec_ref(v_buckets_4302_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4310_, lean_object* v_attrName_4311_){
_start:
{
lean_object* v___x_4312_; lean_object* v_toEnvExtension_4313_; lean_object* v_asyncMode_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v_map_4318_; lean_object* v___x_4319_; 
v___x_4312_ = l_Lean_attributeExtension;
v_toEnvExtension_4313_ = lean_ctor_get(v___x_4312_, 0);
v_asyncMode_4314_ = lean_ctor_get(v_toEnvExtension_4313_, 2);
v___x_4315_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4316_ = lean_box(0);
v___x_4317_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4315_, v___x_4312_, v_env_4310_, v_asyncMode_4314_, v___x_4316_);
v_map_4318_ = lean_ctor_get(v___x_4317_, 1);
lean_inc_ref(v_map_4318_);
lean_dec(v___x_4317_);
v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4318_, v_attrName_4311_);
lean_dec_ref(v_map_4318_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4320_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4321_ = 1;
v___x_4322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4311_, v___x_4321_);
v___x_4323_ = lean_string_append(v___x_4320_, v___x_4322_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
v___x_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
return v___x_4326_;
}
else
{
lean_object* v_val_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_attrName_4311_);
v_val_4327_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4319_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_val_4327_);
lean_dec(v___x_4319_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_val_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4335_, lean_object* v_builderId_4336_, lean_object* v_ref_4337_, lean_object* v_args_4338_){
_start:
{
lean_object* v_entry_4340_; lean_object* v___x_4341_; 
v_entry_4340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4340_, 0, v_builderId_4336_);
lean_ctor_set(v_entry_4340_, 1, v_ref_4337_);
lean_ctor_set(v_entry_4340_, 2, v_args_4338_);
lean_inc_ref(v_entry_4340_);
v___x_4341_ = l_Lean_mkAttributeImplOfEntry(v_entry_4340_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4367_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4367_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4367_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_toAttributeImplCore_4346_; lean_object* v_name_4347_; uint8_t v___x_4348_; 
v_toAttributeImplCore_4346_ = lean_ctor_get(v_a_4342_, 0);
v_name_4347_ = lean_ctor_get(v_toAttributeImplCore_4346_, 1);
lean_inc_ref(v_env_4335_);
v___x_4348_ = l_Lean_isAttribute(v_env_4335_, v_name_4347_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; lean_object* v_toEnvExtension_4350_; lean_object* v_asyncMode_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4349_ = l_Lean_attributeExtension;
v_toEnvExtension_4350_ = lean_ctor_get(v___x_4349_, 0);
v_asyncMode_4351_ = lean_ctor_get(v_toEnvExtension_4350_, 2);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_entry_4340_);
lean_ctor_set(v___x_4352_, 1, v_a_4342_);
v___x_4353_ = lean_box(0);
v___x_4354_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4349_, v_env_4335_, v___x_4352_, v_asyncMode_4351_, v___x_4353_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4354_);
v___x_4356_ = v___x_4344_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
lean_inc(v_name_4347_);
lean_dec(v_a_4342_);
lean_dec_ref_known(v_entry_4340_, 3);
lean_dec_ref(v_env_4335_);
v___x_4358_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4347_, v___x_4348_);
v___x_4360_ = lean_string_append(v___x_4358_, v___x_4359_);
lean_dec_ref(v___x_4359_);
v___x_4361_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4362_ = lean_string_append(v___x_4360_, v___x_4361_);
v___x_4363_ = lean_mk_io_user_error(v___x_4362_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set_tag(v___x_4344_, 1);
lean_ctor_set(v___x_4344_, 0, v___x_4363_);
v___x_4365_ = v___x_4344_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec_ref_known(v_entry_4340_, 3);
lean_dec_ref(v_env_4335_);
v_a_4368_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4341_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4341_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4376_, lean_object* v_builderId_4377_, lean_object* v_ref_4378_, lean_object* v_args_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_registerAttributeOfBuilder(v_env_4376_, v_builderId_4377_, v_ref_4378_, v_args_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
if (lean_obj_tag(v_x_4382_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_a_4386_ = lean_ctor_get(v_x_4382_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v_x_4382_, 1);
v___x_4387_ = l_Lean_stringToMessageData(v_a_4386_);
v___x_4388_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4387_, v___y_4383_, v___y_4384_);
return v___x_4388_;
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
v_a_4389_ = lean_ctor_get(v_x_4382_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_x_4382_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v_x_4382_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v_x_4382_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set_tag(v___x_4391_, 0);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4402_, lean_object* v_attrName_4403_, lean_object* v_stx_4404_, uint8_t v_kind_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; lean_object* v_env_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4409_ = lean_st_ref_get(v_a_4407_);
v_env_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc_ref(v_env_4410_);
lean_dec(v___x_4409_);
v___x_4411_ = l_Lean_getAttributeImpl(v_env_4410_, v_attrName_4403_);
v___x_4412_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4411_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v_add_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v_add_4414_ = lean_ctor_get(v_a_4413_, 1);
lean_inc_ref(v_add_4414_);
lean_dec(v_a_4413_);
v___x_4415_ = lean_box(v_kind_4405_);
lean_inc(v_a_4407_);
lean_inc_ref(v_a_4406_);
v___x_4416_ = lean_apply_6(v_add_4414_, v_declName_4402_, v_stx_4404_, v___x_4415_, v_a_4406_, v_a_4407_, lean_box(0));
return v___x_4416_;
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec(v_stx_4404_);
lean_dec(v_declName_4402_);
v_a_4417_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4412_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4412_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4425_, lean_object* v_attrName_4426_, lean_object* v_stx_4427_, lean_object* v_kind_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_kind_boxed_4432_; lean_object* v_res_4433_; 
v_kind_boxed_4432_ = lean_unbox(v_kind_4428_);
v_res_4433_ = l_Lean_Attribute_add(v_declName_4425_, v_attrName_4426_, v_stx_4427_, v_kind_boxed_4432_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4435_, v___y_4436_, v___y_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4440_, v_x_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4446_, lean_object* v_attrName_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v___x_4451_; lean_object* v_env_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4451_ = lean_st_ref_get(v_a_4449_);
v_env_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc_ref(v_env_4452_);
lean_dec(v___x_4451_);
v___x_4453_ = l_Lean_getAttributeImpl(v_env_4452_, v_attrName_4447_);
v___x_4454_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4453_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v_erase_4456_; lean_object* v___x_4457_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v_erase_4456_ = lean_ctor_get(v_a_4455_, 2);
lean_inc_ref(v_erase_4456_);
lean_dec(v_a_4455_);
lean_inc(v_a_4449_);
lean_inc_ref(v_a_4448_);
v___x_4457_ = lean_apply_4(v_erase_4456_, v_declName_4446_, v_a_4448_, v_a_4449_, lean_box(0));
return v___x_4457_;
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec(v_declName_4446_);
v_a_4458_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4454_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4454_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4466_, lean_object* v_attrName_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Attribute_erase(v_declName_4466_, v_attrName_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4472_, lean_object* v_x_4473_){
_start:
{
if (lean_obj_tag(v_x_4473_) == 0)
{
return v_x_4472_;
}
else
{
lean_object* v_key_4474_; lean_object* v_value_4475_; lean_object* v_tail_4476_; lean_object* v_newEntries_4477_; lean_object* v_map_4478_; uint8_t v___x_4479_; 
v_key_4474_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_key_4474_);
v_value_4475_ = lean_ctor_get(v_x_4473_, 1);
lean_inc(v_value_4475_);
v_tail_4476_ = lean_ctor_get(v_x_4473_, 2);
lean_inc(v_tail_4476_);
lean_dec_ref_known(v_x_4473_, 3);
v_newEntries_4477_ = lean_ctor_get(v_x_4472_, 0);
v_map_4478_ = lean_ctor_get(v_x_4472_, 1);
v___x_4479_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4478_, v_key_4474_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4488_; 
lean_inc_ref(v_map_4478_);
lean_inc(v_newEntries_4477_);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_x_4472_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; lean_object* v_unused_4490_; 
v_unused_4489_ = lean_ctor_get(v_x_4472_, 1);
lean_dec(v_unused_4489_);
v_unused_4490_ = lean_ctor_get(v_x_4472_, 0);
lean_dec(v_unused_4490_);
v___x_4481_ = v_x_4472_;
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v_x_4472_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4478_, v_key_4474_, v_value_4475_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v___x_4483_);
v___x_4485_ = v___x_4481_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_newEntries_4477_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
v_x_4472_ = v___x_4485_;
v_x_4473_ = v_tail_4476_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4475_);
lean_dec(v_key_4474_);
v_x_4473_ = v_tail_4476_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4492_, size_t v_i_4493_, size_t v_stop_4494_, lean_object* v_b_4495_){
_start:
{
uint8_t v___x_4496_; 
v___x_4496_ = lean_usize_dec_eq(v_i_4493_, v_stop_4494_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; size_t v___x_4499_; size_t v___x_4500_; 
v___x_4497_ = lean_array_uget_borrowed(v_as_4492_, v_i_4493_);
lean_inc(v___x_4497_);
v___x_4498_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4495_, v___x_4497_);
v___x_4499_ = ((size_t)1ULL);
v___x_4500_ = lean_usize_add(v_i_4493_, v___x_4499_);
v_i_4493_ = v___x_4500_;
v_b_4495_ = v___x_4498_;
goto _start;
}
else
{
return v_b_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4502_, lean_object* v_i_4503_, lean_object* v_stop_4504_, lean_object* v_b_4505_){
_start:
{
size_t v_i_boxed_4506_; size_t v_stop_boxed_4507_; lean_object* v_res_4508_; 
v_i_boxed_4506_ = lean_unbox_usize(v_i_4503_);
lean_dec(v_i_4503_);
v_stop_boxed_4507_ = lean_unbox_usize(v_stop_4504_);
lean_dec(v_stop_4504_);
v_res_4508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4502_, v_i_boxed_4506_, v_stop_boxed_4507_, v_b_4505_);
lean_dec_ref(v_as_4502_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4509_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___y_4515_; lean_object* v_toEnvExtension_4518_; lean_object* v_asyncMode_4519_; lean_object* v_buckets_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4511_ = l_Lean_attributeMapRef;
v___x_4512_ = lean_st_ref_get(v___x_4511_);
v___x_4513_ = l_Lean_attributeExtension;
v_toEnvExtension_4518_ = lean_ctor_get(v___x_4513_, 0);
v_asyncMode_4519_ = lean_ctor_get(v_toEnvExtension_4518_, 2);
v_buckets_4520_ = lean_ctor_get(v___x_4512_, 1);
lean_inc_ref(v_buckets_4520_);
lean_dec(v___x_4512_);
v___x_4521_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4522_ = lean_box(0);
lean_inc_ref(v_env_4509_);
v___x_4523_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4521_, v___x_4513_, v_env_4509_, v_asyncMode_4519_, v___x_4522_);
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = lean_array_get_size(v_buckets_4520_);
v___x_4526_ = lean_nat_dec_lt(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_dec_ref(v_buckets_4520_);
v___y_4515_ = v___x_4523_;
goto v___jp_4514_;
}
else
{
size_t v___x_4527_; size_t v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((size_t)0ULL);
v___x_4528_ = lean_usize_of_nat(v___x_4525_);
v___x_4529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4520_, v___x_4527_, v___x_4528_, v___x_4523_);
lean_dec_ref(v_buckets_4520_);
v___y_4515_ = v___x_4529_;
goto v___jp_4514_;
}
v___jp_4514_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4513_, v_env_4509_, v___y_4515_);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = lean_update_env_attributes(v_env_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_size_4536_; lean_object* v___x_4537_; 
v___x_4534_ = l_Lean_attributeMapRef;
v___x_4535_ = lean_st_ref_get(v___x_4534_);
v_size_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_size_4536_);
lean_dec(v___x_4535_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_size_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = lean_get_num_attributes();
return v_res_4539_;
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
