// Lean compiler output
// Module: Lake.Util.Git
// Imports: Init.System.IO Init.Data.ToString Lake.Util.Log Lake.Util.Proc
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
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_instToStringGitRepo;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__0;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__2;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__2;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__0;
static lean_object* l_Lake_GitRepo_quietInit___closed__4;
static lean_object* l_Lake_GitRepo_captureGit_x3f___closed__0;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_branchExists___closed__0;
static lean_object* l_Lake_GitRepo_cwd___closed__0;
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_object* l_Lake_GitRepo_fetch___closed__1;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__3;
static lean_object* l_Lake_GitRepo_getHeadRevision_x3f___closed__0;
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getTags___closed__2;
static lean_object* l_Lake_GitRepo_quietInit___closed__1;
static lean_object* l_Lake_GitRepo_quietInit___closed__3;
static lean_object* l_Lake_Git_upstreamBranch___closed__0;
static lean_object* l_Lake_GitRepo_clone___closed__0;
lean_object* l_Lake_captureProc_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_clone___closed__2;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_fetch___closed__6;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_object* l_Lake_GitRepo_clone___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_cwd;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_object* l_Lake_GitRepo_getHeadRevision___closed__0;
LEAN_EXPORT lean_object* l_String_split___at___Lake_GitRepo_getTags_spec__0(lean_object*);
static lean_object* l_Lake_Git_filterUrl_x3f___closed__5;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__0;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_GitRepo_getTags_spec__0___boxed(lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_branchExists___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
lean_object* l_Lake_testProc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_defaultRemote;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__2;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__0;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getTags___closed__1;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
static lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__1;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__2;
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__1;
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_captureGit_x3f___closed__1;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__0;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lake_GitRepo_revisionExists___closed__2;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__4;
static lean_object* l_Lake_GitRepo_fetch___closed__0;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_object* l_Lake_GitRepo_quietInit___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__0;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_getTags___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Git_defaultRemote___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_object* l_Lake_GitRepo_quietInit___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__1;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_object* l_Lake_GitRepo_fetch___closed__2;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object*);
static lean_object* l_Lake_instToStringGitRepo___closed__0;
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_upstreamBranch;
static lean_object* _init_l_Lake_Git_defaultRemote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("origin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_defaultRemote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_defaultRemote___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Git_upstreamBranch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_upstreamBranch() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_upstreamBranch___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Git_filterUrl_x3f___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Git_filterUrl_x3f___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Git_filterUrl_x3f___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".git", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Git_filterUrl_x3f___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Git_filterUrl_x3f___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Git_filterUrl_x3f___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Substring_nextn(x_4, x_5, x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Lake_Git_filterUrl_x3f___closed__2;
x_9 = l_Substring_beq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(4u);
lean_inc(x_3);
x_11 = l_Substring_prevn(x_4, x_10, x_3);
lean_dec_ref(x_4);
lean_inc(x_11);
lean_inc_ref(x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = l_Lake_Git_filterUrl_x3f___closed__5;
x_14 = l_Substring_beq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_utf8_extract(x_1, x_2, x_11);
lean_dec(x_11);
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_18 = lean_box(0);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_8; uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_dec(x_4);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; uint32_t x_18; uint8_t x_19; 
x_11 = lean_string_utf8_get(x_2, x_4);
x_18 = 48;
x_19 = lean_uint32_dec_le(x_18, x_11);
if (x_19 == 0)
{
x_12 = x_19;
goto block_17;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 57;
x_21 = lean_uint32_dec_le(x_11, x_20);
x_12 = x_21;
goto block_17;
}
block_17:
{
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 97;
x_14 = lean_uint32_dec_le(x_13, x_11);
if (x_14 == 0)
{
x_8 = x_14;
goto block_9;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 102;
x_16 = lean_uint32_dec_le(x_11, x_15);
x_8 = x_16;
goto block_9;
}
}
else
{
goto block_7;
}
}
}
block_7:
{
lean_object* x_5; 
x_5 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_5;
goto _start;
}
block_9:
{
if (x_8 == 0)
{
if (x_1 == 0)
{
goto block_7;
}
else
{
lean_dec(x_4);
return x_1;
}
}
else
{
goto block_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(x_4, x_1, x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
return x_4;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___Lake_Git_isFullObjectName_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Git_isFullObjectName(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeFilePathGitRepo() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeFilePathGitRepo___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeFilePathGitRepo___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instToStringGitRepo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeFilePathGitRepo___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToStringGitRepo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToStringGitRepo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_cwd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_cwd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_GitRepo_cwd___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_GitRepo_dirExists(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_captureGit_x3f___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_captureGit_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_5 = l_Lake_Git_filterUrl_x3f___closed__0;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_captureProc_x3f(x_10, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_6 = l_Lake_Git_filterUrl_x3f___closed__0;
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_Lake_proc(x_11, x_9, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_5 = l_Lake_Git_filterUrl_x3f___closed__0;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10, x_3);
return x_11;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clone", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_clone___closed__0;
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_6 = l_Lake_Git_filterUrl_x3f___closed__0;
x_7 = l_Lake_GitRepo_clone___closed__2;
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_box(0);
x_11 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_proc(x_14, x_12, x_3, x_4);
return x_15;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-q", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__0;
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_quietInit___closed__1;
x_2 = l_Lake_GitRepo_quietInit___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lake_GitRepo_quietInit___closed__4;
x_5 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_6 = l_Lake_Git_filterUrl_x3f___closed__0;
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_Lake_proc(x_11, x_9, x_2, x_3);
return x_12;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--is-inside-work-tree", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_insideWorkTree___closed__0;
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_insideWorkTree___closed__1;
x_2 = l_Lake_GitRepo_insideWorkTree___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lake_GitRepo_insideWorkTree___closed__3;
x_4 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_5 = l_Lake_Git_filterUrl_x3f___closed__0;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10, x_2);
return x_11;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fetch", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--tags", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--force", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_fetch___closed__0;
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_fetch___closed__1;
x_2 = l_Lake_GitRepo_fetch___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_fetch___closed__2;
x_2 = l_Lake_GitRepo_fetch___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_fetch___closed__6;
x_6 = lean_array_push(x_5, x_2);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_8 = l_Lake_Git_filterUrl_x3f___closed__0;
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_proc(x_13, x_11, x_3, x_4);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-B", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutBranch___closed__0;
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutBranch___closed__1;
x_2 = l_Lake_GitRepo_checkoutBranch___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_checkoutBranch___closed__3;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_8 = l_Lake_Git_filterUrl_x3f___closed__0;
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_proc(x_13, x_11, x_3, x_4);
return x_14;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--detach", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutBranch___closed__0;
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_checkoutDetach___closed__0;
x_2 = l_Lake_GitRepo_checkoutDetach___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lake_GitRepo_checkoutDetach___closed__1;
x_6 = l_Lake_GitRepo_checkoutDetach___closed__3;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_5);
x_9 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_10 = l_Lake_Git_filterUrl_x3f___closed__0;
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_13 = 1;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
x_16 = l_Lake_proc(x_15, x_13, x_3, x_4);
return x_16;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--verify", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--end-of-options", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_insideWorkTree___closed__0;
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__1;
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_7 = l_Lake_Git_filterUrl_x3f___closed__0;
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12, x_3);
return x_13;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevision_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEAD", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_GitRepo_getHeadRevision_x3f___closed__0;
x_4 = l_Lake_GitRepo_resolveRevision_x3f(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevision___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again", 113, 113);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_GitRepo_getHeadRevision_x3f___closed__0;
lean_inc_ref(x_1);
x_5 = l_Lake_GitRepo_resolveRevision_x3f(x_4, x_1, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lake_GitRepo_getHeadRevision___closed__0;
x_10 = lean_string_append(x_1, x_9);
x_11 = 3;
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = lean_array_push(x_2, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Lake_GitRepo_getHeadRevision___closed__0;
x_18 = lean_string_append(x_1, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_2);
x_22 = lean_array_push(x_2, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec_ref(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec_ref(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": revision not found '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRemoteRevision___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lake_Git_isFullObjectName(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lake_GitRepo_resolveRemoteRevision___closed__0;
x_8 = lean_string_append(x_2, x_7);
x_9 = lean_string_append(x_8, x_1);
lean_inc_ref(x_3);
x_10 = l_Lake_GitRepo_resolveRevision_x3f(x_9, x_3, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_13 = l_Lake_GitRepo_resolveRevision_x3f(x_1, x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lake_GitRepo_resolveRemoteRevision___closed__1;
x_18 = lean_string_append(x_3, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = l_Lake_GitRepo_resolveRemoteRevision___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = 3;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = lean_array_get_size(x_4);
x_25 = lean_array_push(x_4, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Lake_GitRepo_resolveRemoteRevision___closed__1;
x_29 = lean_string_append(x_3, x_28);
x_30 = lean_string_append(x_29, x_1);
lean_dec_ref(x_1);
x_31 = l_Lake_GitRepo_resolveRemoteRevision___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_4);
x_36 = lean_array_push(x_4, x_34);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_13, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec_ref(x_14);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_13, 0, x_42);
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_ctor_get(x_14, 0);
lean_inc(x_44);
lean_dec_ref(x_14);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
lean_dec_ref(x_11);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
lean_ctor_set(x_10, 0, x_50);
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_dec(x_10);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec_ref(x_11);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_4);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_5);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_6 = l_Lake_GitRepo_fetch(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lake_Git_upstreamBranch___closed__0;
x_11 = l_Lake_GitRepo_resolveRemoteRevision(x_10, x_3, x_1, x_9, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec_ref(x_7);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lake_GitRepo_resolveRemoteRevision(x_14, x_3, x_1, x_13, x_12);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_25 = x_7;
} else {
 lean_dec_ref(x_7);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("show-ref", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refs/heads/", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_branchExists___closed__0;
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
x_2 = l_Lake_GitRepo_branchExists___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lake_GitRepo_branchExists___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_GitRepo_branchExists___closed__3;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_9 = l_Lake_Git_filterUrl_x3f___closed__0;
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_testProc(x_14, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_branchExists(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("^{commit}", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_insideWorkTree___closed__0;
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_resolveRevision_x3f___closed__0;
x_2 = l_Lake_GitRepo_revisionExists___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lake_GitRepo_revisionExists___closed__0;
x_5 = lean_string_append(x_1, x_4);
x_6 = l_Lake_GitRepo_revisionExists___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_9 = l_Lake_Git_filterUrl_x3f___closed__0;
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_testProc(x_14, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 10;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___redArg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_GitRepo_getTags_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_getTags___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getTags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_getTags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_getTags___closed__0;
x_2 = l_Lake_GitRepo_getTags___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lake_GitRepo_getTags___closed__2;
x_4 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_5 = l_Lake_Git_filterUrl_x3f___closed__0;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_captureProc_x3f(x_10, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = l_String_split___at___Lake_GitRepo_getTags_spec__0(x_21);
lean_dec(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec_ref(x_12);
x_25 = l_String_split___at___Lake_GitRepo_getTags_spec__0(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_GitRepo_getTags_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_GitRepo_getTags_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_GitRepo_getTags_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("describe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exact-match", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_findTag_x3f___closed__0;
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_fetch___closed__1;
x_2 = l_Lake_GitRepo_findTag_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_findTag_x3f___closed__1;
x_2 = l_Lake_GitRepo_findTag_x3f___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_findTag_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_7 = l_Lake_Git_filterUrl_x3f___closed__0;
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12, x_3);
return x_13;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("remote", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get-url", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__0;
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__1;
x_2 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
x_5 = lean_array_push(x_4, x_1);
x_6 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_7 = l_Lake_Git_filterUrl_x3f___closed__0;
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12, x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Lake_Git_filterUrl_x3f(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = l_Lake_Git_filterUrl_x3f(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diff", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exit-code", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_hasNoDiff___closed__0;
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_GitRepo_hasNoDiff___closed__1;
x_2 = l_Lake_GitRepo_hasNoDiff___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lake_GitRepo_hasNoDiff___closed__3;
x_4 = l_Lake_GitRepo_captureGit_x3f___closed__0;
x_5 = l_Lake_Git_filterUrl_x3f___closed__0;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lake_GitRepo_captureGit_x3f___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_GitRepo_hasNoDiff(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Git_defaultRemote___closed__0 = _init_l_Lake_Git_defaultRemote___closed__0();
lean_mark_persistent(l_Lake_Git_defaultRemote___closed__0);
l_Lake_Git_defaultRemote = _init_l_Lake_Git_defaultRemote();
lean_mark_persistent(l_Lake_Git_defaultRemote);
l_Lake_Git_upstreamBranch___closed__0 = _init_l_Lake_Git_upstreamBranch___closed__0();
lean_mark_persistent(l_Lake_Git_upstreamBranch___closed__0);
l_Lake_Git_upstreamBranch = _init_l_Lake_Git_upstreamBranch();
lean_mark_persistent(l_Lake_Git_upstreamBranch);
l_Lake_Git_filterUrl_x3f___closed__0 = _init_l_Lake_Git_filterUrl_x3f___closed__0();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__0);
l_Lake_Git_filterUrl_x3f___closed__1 = _init_l_Lake_Git_filterUrl_x3f___closed__1();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__1);
l_Lake_Git_filterUrl_x3f___closed__2 = _init_l_Lake_Git_filterUrl_x3f___closed__2();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__2);
l_Lake_Git_filterUrl_x3f___closed__3 = _init_l_Lake_Git_filterUrl_x3f___closed__3();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__3);
l_Lake_Git_filterUrl_x3f___closed__4 = _init_l_Lake_Git_filterUrl_x3f___closed__4();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__4);
l_Lake_Git_filterUrl_x3f___closed__5 = _init_l_Lake_Git_filterUrl_x3f___closed__5();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__5);
l_Lake_instCoeFilePathGitRepo = _init_l_Lake_instCoeFilePathGitRepo();
lean_mark_persistent(l_Lake_instCoeFilePathGitRepo);
l_Lake_instToStringGitRepo___closed__0 = _init_l_Lake_instToStringGitRepo___closed__0();
lean_mark_persistent(l_Lake_instToStringGitRepo___closed__0);
l_Lake_instToStringGitRepo = _init_l_Lake_instToStringGitRepo();
lean_mark_persistent(l_Lake_instToStringGitRepo);
l_Lake_GitRepo_cwd___closed__0 = _init_l_Lake_GitRepo_cwd___closed__0();
lean_mark_persistent(l_Lake_GitRepo_cwd___closed__0);
l_Lake_GitRepo_cwd = _init_l_Lake_GitRepo_cwd();
lean_mark_persistent(l_Lake_GitRepo_cwd);
l_Lake_GitRepo_captureGit_x3f___closed__0 = _init_l_Lake_GitRepo_captureGit_x3f___closed__0();
lean_mark_persistent(l_Lake_GitRepo_captureGit_x3f___closed__0);
l_Lake_GitRepo_captureGit_x3f___closed__1 = _init_l_Lake_GitRepo_captureGit_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_captureGit_x3f___closed__1);
l_Lake_GitRepo_clone___closed__0 = _init_l_Lake_GitRepo_clone___closed__0();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__0);
l_Lake_GitRepo_clone___closed__1 = _init_l_Lake_GitRepo_clone___closed__1();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__1);
l_Lake_GitRepo_clone___closed__2 = _init_l_Lake_GitRepo_clone___closed__2();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__2);
l_Lake_GitRepo_quietInit___closed__0 = _init_l_Lake_GitRepo_quietInit___closed__0();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__0);
l_Lake_GitRepo_quietInit___closed__1 = _init_l_Lake_GitRepo_quietInit___closed__1();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__1);
l_Lake_GitRepo_quietInit___closed__2 = _init_l_Lake_GitRepo_quietInit___closed__2();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__2);
l_Lake_GitRepo_quietInit___closed__3 = _init_l_Lake_GitRepo_quietInit___closed__3();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__3);
l_Lake_GitRepo_quietInit___closed__4 = _init_l_Lake_GitRepo_quietInit___closed__4();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__4);
l_Lake_GitRepo_insideWorkTree___closed__0 = _init_l_Lake_GitRepo_insideWorkTree___closed__0();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__0);
l_Lake_GitRepo_insideWorkTree___closed__1 = _init_l_Lake_GitRepo_insideWorkTree___closed__1();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__1);
l_Lake_GitRepo_insideWorkTree___closed__2 = _init_l_Lake_GitRepo_insideWorkTree___closed__2();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__2);
l_Lake_GitRepo_insideWorkTree___closed__3 = _init_l_Lake_GitRepo_insideWorkTree___closed__3();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__3);
l_Lake_GitRepo_fetch___closed__0 = _init_l_Lake_GitRepo_fetch___closed__0();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__0);
l_Lake_GitRepo_fetch___closed__1 = _init_l_Lake_GitRepo_fetch___closed__1();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__1);
l_Lake_GitRepo_fetch___closed__2 = _init_l_Lake_GitRepo_fetch___closed__2();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__2);
l_Lake_GitRepo_fetch___closed__3 = _init_l_Lake_GitRepo_fetch___closed__3();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__3);
l_Lake_GitRepo_fetch___closed__4 = _init_l_Lake_GitRepo_fetch___closed__4();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__4);
l_Lake_GitRepo_fetch___closed__5 = _init_l_Lake_GitRepo_fetch___closed__5();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__5);
l_Lake_GitRepo_fetch___closed__6 = _init_l_Lake_GitRepo_fetch___closed__6();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__6);
l_Lake_GitRepo_checkoutBranch___closed__0 = _init_l_Lake_GitRepo_checkoutBranch___closed__0();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__0);
l_Lake_GitRepo_checkoutBranch___closed__1 = _init_l_Lake_GitRepo_checkoutBranch___closed__1();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__1);
l_Lake_GitRepo_checkoutBranch___closed__2 = _init_l_Lake_GitRepo_checkoutBranch___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__2);
l_Lake_GitRepo_checkoutBranch___closed__3 = _init_l_Lake_GitRepo_checkoutBranch___closed__3();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__3);
l_Lake_GitRepo_checkoutDetach___closed__0 = _init_l_Lake_GitRepo_checkoutDetach___closed__0();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__0);
l_Lake_GitRepo_checkoutDetach___closed__1 = _init_l_Lake_GitRepo_checkoutDetach___closed__1();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__1);
l_Lake_GitRepo_checkoutDetach___closed__2 = _init_l_Lake_GitRepo_checkoutDetach___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__2);
l_Lake_GitRepo_checkoutDetach___closed__3 = _init_l_Lake_GitRepo_checkoutDetach___closed__3();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__3);
l_Lake_GitRepo_resolveRevision_x3f___closed__0 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__0();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__0);
l_Lake_GitRepo_resolveRevision_x3f___closed__1 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__1);
l_Lake_GitRepo_resolveRevision_x3f___closed__2 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__2);
l_Lake_GitRepo_resolveRevision_x3f___closed__3 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__3);
l_Lake_GitRepo_resolveRevision_x3f___closed__4 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__4);
l_Lake_GitRepo_getHeadRevision_x3f___closed__0 = _init_l_Lake_GitRepo_getHeadRevision_x3f___closed__0();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevision_x3f___closed__0);
l_Lake_GitRepo_getHeadRevision___closed__0 = _init_l_Lake_GitRepo_getHeadRevision___closed__0();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevision___closed__0);
l_Lake_GitRepo_resolveRemoteRevision___closed__0 = _init_l_Lake_GitRepo_resolveRemoteRevision___closed__0();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___closed__0);
l_Lake_GitRepo_resolveRemoteRevision___closed__1 = _init_l_Lake_GitRepo_resolveRemoteRevision___closed__1();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___closed__1);
l_Lake_GitRepo_resolveRemoteRevision___closed__2 = _init_l_Lake_GitRepo_resolveRemoteRevision___closed__2();
lean_mark_persistent(l_Lake_GitRepo_resolveRemoteRevision___closed__2);
l_Lake_GitRepo_branchExists___closed__0 = _init_l_Lake_GitRepo_branchExists___closed__0();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__0);
l_Lake_GitRepo_branchExists___closed__1 = _init_l_Lake_GitRepo_branchExists___closed__1();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__1);
l_Lake_GitRepo_branchExists___closed__2 = _init_l_Lake_GitRepo_branchExists___closed__2();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__2);
l_Lake_GitRepo_branchExists___closed__3 = _init_l_Lake_GitRepo_branchExists___closed__3();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__3);
l_Lake_GitRepo_revisionExists___closed__0 = _init_l_Lake_GitRepo_revisionExists___closed__0();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__0);
l_Lake_GitRepo_revisionExists___closed__1 = _init_l_Lake_GitRepo_revisionExists___closed__1();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__1);
l_Lake_GitRepo_revisionExists___closed__2 = _init_l_Lake_GitRepo_revisionExists___closed__2();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__2);
l_Lake_GitRepo_getTags___closed__0 = _init_l_Lake_GitRepo_getTags___closed__0();
lean_mark_persistent(l_Lake_GitRepo_getTags___closed__0);
l_Lake_GitRepo_getTags___closed__1 = _init_l_Lake_GitRepo_getTags___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getTags___closed__1);
l_Lake_GitRepo_getTags___closed__2 = _init_l_Lake_GitRepo_getTags___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getTags___closed__2);
l_Lake_GitRepo_findTag_x3f___closed__0 = _init_l_Lake_GitRepo_findTag_x3f___closed__0();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__0);
l_Lake_GitRepo_findTag_x3f___closed__1 = _init_l_Lake_GitRepo_findTag_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__1);
l_Lake_GitRepo_findTag_x3f___closed__2 = _init_l_Lake_GitRepo_findTag_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__2);
l_Lake_GitRepo_findTag_x3f___closed__3 = _init_l_Lake_GitRepo_findTag_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__3);
l_Lake_GitRepo_findTag_x3f___closed__4 = _init_l_Lake_GitRepo_findTag_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__4);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__0();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__2 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__3 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
l_Lake_GitRepo_hasNoDiff___closed__0 = _init_l_Lake_GitRepo_hasNoDiff___closed__0();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__0);
l_Lake_GitRepo_hasNoDiff___closed__1 = _init_l_Lake_GitRepo_hasNoDiff___closed__1();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__1);
l_Lake_GitRepo_hasNoDiff___closed__2 = _init_l_Lake_GitRepo_hasNoDiff___closed__2();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__2);
l_Lake_GitRepo_hasNoDiff___closed__3 = _init_l_Lake_GitRepo_hasNoDiff___closed__3();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
