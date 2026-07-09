// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Lake.Util.String
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRev_head___closed__0 = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_head = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
static const lean_string_object l_Lake_GitRev_fetchHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FETCH_HEAD"};
static const lean_object* l_Lake_GitRev_fetchHead___closed__0 = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_fetchHead = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_withRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRev_withRemote___closed__0 = (const lean_object*)&l_Lake_GitRev_withRemote___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_GitRepo_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_GitRepo_instCoeFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_GitRepo_instCoeFilePath___closed__0 = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instCoeFilePath = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instToString = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_bareInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bare"};
static const lean_object* l_Lake_GitRepo_bareInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_bareInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_bareInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "worktree"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__1_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__2 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__3;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__4;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findCommit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_findCommit_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findCommit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--refetch"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--filter=tree:0"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__5;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__6;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = ": could not resolve 'FETCH_HEAD' to a commit after fetching; this may be an issue with Lake; please report it"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__7 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__0;
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_setRemoteUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "set-url"};
static const lean_object* l_Lake_GitRepo_setRemoteUrl___closed__0 = (const lean_object*)&l_Lake_GitRepo_setRemoteUrl___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_setRemoteUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_setRemoteUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_7_ = lean_string_utf8_byte_size(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_11_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_28_ = lean_string_utf8_byte_size(v_url_11_);
v___x_29_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__3, &l_Lake_Git_filterUrl_x3f___closed__3_once, _init_l_Lake_Git_filterUrl_x3f___closed__3);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_memcmp(v_url_11_, v___x_27_, v___x_31_, v___x_31_, v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_33_; 
lean_dec_ref(v_url_11_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_string_utf8_byte_size(v_url_11_);
v___x_15_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__1, &l_Lake_Git_filterUrl_x3f___closed__1_once, _init_l_Lake_Git_filterUrl_x3f___closed__1);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_11_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_20_ = lean_string_memcmp(v_url_11_, v___x_13_, v___x_19_, v___x_18_, v___x_15_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_url_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v_url_11_);
v___x_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_23_, 0, v_url_11_);
lean_ctor_set(v___x_23_, 1, v___x_18_);
lean_ctor_set(v___x_23_, 2, v___x_14_);
v___x_24_ = l_String_Slice_Pos_prevn(v___x_23_, v___x_14_, v___x_22_);
lean_dec_ref_known(v___x_23_, 3);
v___x_25_ = lean_string_utf8_extract(v_url_11_, v___x_18_, v___x_24_);
lean_dec(v___x_24_);
lean_dec_ref(v_url_11_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_string_utf8_byte_size(v_rev_34_);
v___x_36_ = lean_unsigned_to_nat(40u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Lake_isHex(v_rev_34_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lake_Git_isFullObjectName(v_rev_39_);
lean_dec_ref(v_rev_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object* v_rev_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_string_utf8_byte_size(v_rev_46_);
v___x_48_ = lean_unsigned_to_nat(40u);
v___x_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Lake_isHex(v_rev_46_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object* v_rev_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lake_GitRev_isFullSha1(v_rev_51_);
lean_dec_ref(v_rev_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object* v_remote_55_, lean_object* v_rev_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_58_ = lean_string_append(v_remote_55_, v___x_57_);
v___x_59_ = lean_string_append(v___x_58_, v_rev_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object* v_remote_60_, lean_object* v_rev_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_GitRev_withRemote(v_remote_60_, v_rev_61_);
lean_dec_ref(v_rev_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object* v_x_63_){
_start:
{
lean_inc_ref(v_x_63_);
return v_x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_64_);
lean_dec_ref(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_71_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_System_FilePath_isDir(v_repo_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_GitRepo_dirExists(v_repo_74_);
lean_dec_ref(v_repo_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_82_, lean_object* v_repo_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_86_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_87_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v_repo_83_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_91_ = 1;
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_93_, 0, v___x_86_);
lean_ctor_set(v___x_93_, 1, v___x_87_);
lean_ctor_set(v___x_93_, 2, v_args_82_);
lean_ctor_set(v___x_93_, 3, v___x_88_);
lean_ctor_set(v___x_93_, 4, v___x_90_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*5, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*5 + 1, v___x_92_);
v___x_94_ = l_Lake_captureProc_x27(v___x_93_, v_a_84_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_111_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_111_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_111_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_111_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_stdout_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_str_104_; lean_object* v_startInclusive_105_; lean_object* v_endExclusive_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v_stdout_100_ = lean_ctor_get(v_a_95_, 0);
lean_inc_ref(v_stdout_100_);
lean_dec(v_a_95_);
v___x_101_ = lean_string_utf8_byte_size(v_stdout_100_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v_stdout_100_);
lean_ctor_set(v___x_102_, 1, v___x_89_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
v___x_103_ = l_String_Slice_trimAscii(v___x_102_);
v_str_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_str_104_);
v_startInclusive_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_startInclusive_105_);
v_endExclusive_106_ = lean_ctor_get(v___x_103_, 2);
lean_inc(v_endExclusive_106_);
lean_dec_ref(v___x_103_);
v___x_107_ = lean_string_utf8_extract(v_str_104_, v_startInclusive_105_, v_endExclusive_106_);
lean_dec(v_endExclusive_106_);
lean_dec(v_startInclusive_105_);
lean_dec_ref(v_str_104_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_107_);
v___x_109_ = v___x_98_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_96_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_112_ = lean_ctor_get(v___x_94_, 0);
v_a_113_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_94_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_inc(v_a_112_);
lean_dec(v___x_94_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_112_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_121_, lean_object* v_repo_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lake_GitRepo_captureGit(v_args_121_, v_repo_122_, v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_126_, lean_object* v_repo_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_129_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_130_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_repo_127_);
v___x_132_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_133_ = 1;
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_135_, 0, v___x_129_);
lean_ctor_set(v___x_135_, 1, v___x_130_);
lean_ctor_set(v___x_135_, 2, v_args_126_);
lean_ctor_set(v___x_135_, 3, v___x_131_);
lean_ctor_set(v___x_135_, 4, v___x_132_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5 + 1, v___x_134_);
v___x_136_ = l_Lake_captureProc_x3f(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_137_, lean_object* v_repo_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_GitRepo_captureGit_x3f(v_args_137_, v_repo_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_141_, lean_object* v_repo_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_145_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_146_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v_repo_142_);
v___x_148_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_149_ = 1;
v___x_150_ = 0;
v___x_151_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_146_);
lean_ctor_set(v___x_151_, 2, v_args_141_);
lean_ctor_set(v___x_151_, 3, v___x_147_);
lean_ctor_set(v___x_151_, 4, v___x_148_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*5, v___x_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*5 + 1, v___x_150_);
v___x_152_ = lean_box(0);
v___x_153_ = l_Lake_proc(v___x_151_, v___x_149_, v___x_152_, v_a_143_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_154_, lean_object* v_repo_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lake_GitRepo_execGit(v_args_154_, v_repo_155_, v_a_156_);
return v_res_158_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_159_, lean_object* v_repo_160_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_162_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_163_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v_repo_160_);
v___x_165_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_166_ = 1;
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_168_, 0, v___x_162_);
lean_ctor_set(v___x_168_, 1, v___x_163_);
lean_ctor_set(v___x_168_, 2, v_args_159_);
lean_ctor_set(v___x_168_, 3, v___x_164_);
lean_ctor_set(v___x_168_, 4, v___x_165_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*5, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*5 + 1, v___x_167_);
v___x_169_ = l_Lake_testProc(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_170_, lean_object* v_repo_171_, lean_object* v_a_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lake_GitRepo_testGit(v_args_170_, v_repo_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_177_ = lean_unsigned_to_nat(3u);
v___x_178_ = lean_mk_empty_array_with_capacity(v___x_177_);
v___x_179_ = lean_array_push(v___x_178_, v___x_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_180_, lean_object* v_repo_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_184_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_185_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_186_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_187_ = lean_array_push(v___x_186_, v_url_180_);
v___x_188_ = lean_array_push(v___x_187_, v_repo_181_);
v___x_189_ = lean_box(0);
v___x_190_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_191_ = 1;
v___x_192_ = 0;
v___x_193_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_193_, 0, v___x_184_);
lean_ctor_set(v___x_193_, 1, v___x_185_);
lean_ctor_set(v___x_193_, 2, v___x_188_);
lean_ctor_set(v___x_193_, 3, v___x_189_);
lean_ctor_set(v___x_193_, 4, v___x_190_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*5, v___x_191_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*5 + 1, v___x_192_);
v___x_194_ = l_Lake_proc(v___x_193_, v___x_191_, v___x_189_, v_a_182_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_195_, lean_object* v_repo_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lake_GitRepo_clone(v_url_195_, v_repo_196_, v_a_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_211_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_212_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_213_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_repo_208_);
v___x_215_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_216_ = 1;
v___x_217_ = 0;
v___x_218_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_218_, 0, v___x_212_);
lean_ctor_set(v___x_218_, 1, v___x_213_);
lean_ctor_set(v___x_218_, 2, v___x_211_);
lean_ctor_set(v___x_218_, 3, v___x_214_);
lean_ctor_set(v___x_218_, 4, v___x_215_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5, v___x_216_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*5 + 1, v___x_217_);
v___x_219_ = lean_box(0);
v___x_220_ = l_Lake_proc(v___x_218_, v___x_216_, v___x_219_, v_a_209_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lake_GitRepo_quietInit(v_repo_221_, v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object* v_repo_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_237_ = ((lean_object*)(l_Lake_GitRepo_bareInit___closed__1));
v___x_238_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_239_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_repo_234_);
v___x_241_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_242_ = 1;
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_244_, 0, v___x_238_);
lean_ctor_set(v___x_244_, 1, v___x_239_);
lean_ctor_set(v___x_244_, 2, v___x_237_);
lean_ctor_set(v___x_244_, 3, v___x_240_);
lean_ctor_set(v___x_244_, 4, v___x_241_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*5 + 1, v___x_243_);
v___x_245_ = lean_box(0);
v___x_246_ = l_Lake_proc(v___x_244_, v___x_242_, v___x_245_, v_a_235_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object* v_repo_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_GitRepo_bareInit(v_repo_247_, v_a_248_);
return v_res_250_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_261_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_262_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_263_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_repo_259_);
v___x_265_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_266_ = 1;
v___x_267_ = 0;
v___x_268_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_268_, 0, v___x_262_);
lean_ctor_set(v___x_268_, 1, v___x_263_);
lean_ctor_set(v___x_268_, 2, v___x_261_);
lean_ctor_set(v___x_268_, 3, v___x_264_);
lean_ctor_set(v___x_268_, 4, v___x_265_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*5, v___x_266_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*5 + 1, v___x_267_);
v___x_269_ = l_Lake_testProc(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_270_, lean_object* v_a_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lake_GitRepo_insideWorkTree(v_repo_270_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_278_ = lean_unsigned_to_nat(4u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_array_push(v___x_279_, v___x_277_);
return v___x_280_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_282_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_285_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_286_ = lean_array_push(v___x_285_, v___x_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_287_, lean_object* v_remote_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_291_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_292_ = lean_array_push(v___x_291_, v_remote_288_);
v___x_293_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_294_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_repo_287_);
v___x_296_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_297_ = 1;
v___x_298_ = 0;
v___x_299_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_299_, 0, v___x_293_);
lean_ctor_set(v___x_299_, 1, v___x_294_);
lean_ctor_set(v___x_299_, 2, v___x_292_);
lean_ctor_set(v___x_299_, 3, v___x_295_);
lean_ctor_set(v___x_299_, 4, v___x_296_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*5, v___x_297_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*5 + 1, v___x_298_);
v___x_300_ = lean_box(0);
v___x_301_ = l_Lake_proc(v___x_299_, v___x_297_, v___x_300_, v_a_289_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_302_, lean_object* v_remote_303_, lean_object* v_a_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lake_GitRepo_fetch(v_repo_302_, v_remote_303_, v_a_304_);
return v_res_306_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__3(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__0));
v___x_311_ = lean_unsigned_to_nat(5u);
v___x_312_ = lean_mk_empty_array_with_capacity(v___x_311_);
v___x_313_ = lean_array_push(v___x_312_, v___x_310_);
return v___x_313_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__4(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_315_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__3, &l_Lake_GitRepo_addWorktreeDetach___closed__3_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__3);
v___x_316_ = lean_array_push(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__5(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_318_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__4, &l_Lake_GitRepo_addWorktreeDetach___closed__4_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__4);
v___x_319_ = lean_array_push(v___x_318_, v___x_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object* v_path_320_, lean_object* v_rev_321_, lean_object* v_repo_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_325_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__5, &l_Lake_GitRepo_addWorktreeDetach___closed__5_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__5);
v___x_326_ = lean_array_push(v___x_325_, v_path_320_);
v___x_327_ = lean_array_push(v___x_326_, v_rev_321_);
v___x_328_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_329_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_repo_322_);
v___x_331_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_332_ = 1;
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_334_, 0, v___x_328_);
lean_ctor_set(v___x_334_, 1, v___x_329_);
lean_ctor_set(v___x_334_, 2, v___x_327_);
lean_ctor_set(v___x_334_, 3, v___x_330_);
lean_ctor_set(v___x_334_, 4, v___x_331_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*5 + 1, v___x_333_);
v___x_335_ = lean_box(0);
v___x_336_ = l_Lake_proc(v___x_334_, v___x_332_, v___x_335_, v_a_323_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object* v_path_337_, lean_object* v_rev_338_, lean_object* v_repo_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lake_GitRepo_addWorktreeDetach(v_path_337_, v_rev_338_, v_repo_339_, v_a_340_);
return v_res_342_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_array_push(v___x_347_, v___x_345_);
return v___x_348_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_350_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_351_ = lean_array_push(v___x_350_, v___x_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_352_, lean_object* v_repo_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_356_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_357_ = lean_array_push(v___x_356_, v_branch_352_);
v___x_358_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_359_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_repo_353_);
v___x_361_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_362_ = 1;
v___x_363_ = 0;
v___x_364_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_364_, 0, v___x_358_);
lean_ctor_set(v___x_364_, 1, v___x_359_);
lean_ctor_set(v___x_364_, 2, v___x_357_);
lean_ctor_set(v___x_364_, 3, v___x_360_);
lean_ctor_set(v___x_364_, 4, v___x_361_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*5, v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*5 + 1, v___x_363_);
v___x_365_ = lean_box(0);
v___x_366_ = l_Lake_proc(v___x_364_, v___x_362_, v___x_365_, v_a_354_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_367_, lean_object* v_repo_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_GitRepo_checkoutBranch(v_branch_367_, v_repo_368_, v_a_369_);
return v_res_371_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_374_ = lean_unsigned_to_nat(4u);
v___x_375_ = lean_mk_empty_array_with_capacity(v___x_374_);
v___x_376_ = lean_array_push(v___x_375_, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_378_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__1, &l_Lake_GitRepo_checkoutDetach___closed__1_once, _init_l_Lake_GitRepo_checkoutDetach___closed__1);
v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_380_, lean_object* v_repo_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_384_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_385_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_386_ = lean_array_push(v___x_385_, v_hash_380_);
v___x_387_ = lean_array_push(v___x_386_, v___x_384_);
v___x_388_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_389_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_repo_381_);
v___x_391_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_392_ = 1;
v___x_393_ = 0;
v___x_394_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_394_, 0, v___x_388_);
lean_ctor_set(v___x_394_, 1, v___x_389_);
lean_ctor_set(v___x_394_, 2, v___x_387_);
lean_ctor_set(v___x_394_, 3, v___x_390_);
lean_ctor_set(v___x_394_, 4, v___x_391_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*5, v___x_392_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*5 + 1, v___x_393_);
v___x_395_ = lean_box(0);
v___x_396_ = l_Lake_proc(v___x_394_, v___x_392_, v___x_395_, v_a_382_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_397_, lean_object* v_repo_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lake_GitRepo_checkoutDetach(v_hash_397_, v_repo_398_, v_a_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_413_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_414_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_415_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_repo_410_);
v___x_417_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_418_ = 1;
v___x_419_ = 0;
v___x_420_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_420_, 0, v___x_414_);
lean_ctor_set(v___x_420_, 1, v___x_415_);
lean_ctor_set(v___x_420_, 2, v___x_413_);
lean_ctor_set(v___x_420_, 3, v___x_416_);
lean_ctor_set(v___x_420_, 4, v___x_417_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*5 + 1, v___x_419_);
v___x_421_ = lean_box(0);
v___x_422_ = l_Lake_proc(v___x_420_, v___x_418_, v___x_421_, v_a_411_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lake_GitRepo_clean(v_repo_423_, v_a_424_);
return v_res_426_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_430_ = lean_unsigned_to_nat(4u);
v___x_431_ = lean_mk_empty_array_with_capacity(v___x_430_);
v___x_432_ = lean_array_push(v___x_431_, v___x_429_);
return v___x_432_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_434_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_435_ = lean_array_push(v___x_434_, v___x_433_);
return v___x_435_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_437_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_438_ = lean_array_push(v___x_437_, v___x_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_439_, lean_object* v_repo_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_442_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_443_ = lean_array_push(v___x_442_, v_rev_439_);
v___x_444_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_445_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v_repo_440_);
v___x_447_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_448_ = 1;
v___x_449_ = 0;
v___x_450_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_450_, 0, v___x_444_);
lean_ctor_set(v___x_450_, 1, v___x_445_);
lean_ctor_set(v___x_450_, 2, v___x_443_);
lean_ctor_set(v___x_450_, 3, v___x_446_);
lean_ctor_set(v___x_450_, 4, v___x_447_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5, v___x_448_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*5 + 1, v___x_449_);
v___x_451_ = l_Lake_captureProc_x3f(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_452_, lean_object* v_repo_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_452_, v_repo_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object* v_rev_457_, lean_object* v_repo_458_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_460_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_461_ = lean_string_append(v_rev_457_, v___x_460_);
v___x_462_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_463_ = lean_array_push(v___x_462_, v___x_461_);
v___x_464_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_465_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v_repo_458_);
v___x_467_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_468_ = 1;
v___x_469_ = 0;
v___x_470_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_470_, 0, v___x_464_);
lean_ctor_set(v___x_470_, 1, v___x_465_);
lean_ctor_set(v___x_470_, 2, v___x_463_);
lean_ctor_set(v___x_470_, 3, v___x_466_);
lean_ctor_set(v___x_470_, 4, v___x_467_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*5, v___x_468_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*5 + 1, v___x_469_);
v___x_471_ = l_Lake_captureProc_x3f(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object* v_rev_472_, lean_object* v_repo_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lake_GitRepo_findCommit_x3f(v_rev_472_, v_repo_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_478_, lean_object* v_repo_479_, lean_object* v_a_480_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Lake_GitRev_isFullSha1(v_rev_478_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_inc_ref(v_repo_479_);
lean_inc_ref(v_rev_478_);
v___x_483_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_478_, v_repo_479_);
if (lean_obj_tag(v___x_483_) == 1)
{
lean_object* v_val_484_; lean_object* v___x_485_; 
lean_dec_ref(v_repo_479_);
lean_dec_ref(v_rev_478_);
v_val_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v___x_483_, 1);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_val_484_);
lean_ctor_set(v___x_485_, 1, v_a_480_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_483_);
v___x_486_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_487_ = lean_string_append(v_repo_479_, v___x_486_);
v___x_488_ = lean_string_append(v___x_487_, v_rev_478_);
lean_dec_ref(v_rev_478_);
v___x_489_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_490_ = lean_string_append(v___x_488_, v___x_489_);
v___x_491_ = 3;
v___x_492_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set_uint8(v___x_492_, sizeof(void*)*1, v___x_491_);
v___x_493_ = lean_array_get_size(v_a_480_);
v___x_494_ = lean_array_push(v_a_480_, v___x_492_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; 
lean_dec_ref(v_repo_479_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v_rev_478_);
lean_ctor_set(v___x_496_, 1, v_a_480_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_497_, lean_object* v_repo_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_GitRepo_resolveRevision(v_rev_497_, v_repo_498_, v_a_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
v___x_505_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_504_, v_repo_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
lean_inc_ref(v_repo_510_);
v___x_514_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_513_, v_repo_510_);
if (lean_obj_tag(v___x_514_) == 1)
{
lean_object* v_val_515_; lean_object* v___x_516_; 
lean_dec_ref(v_repo_510_);
v_val_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_val_515_);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_val_515_);
lean_ctor_set(v___x_516_, 1, v_a_511_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v___x_514_);
v___x_517_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_518_ = lean_string_append(v_repo_510_, v___x_517_);
v___x_519_ = 3;
v___x_520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
v___x_521_ = lean_array_get_size(v_a_511_);
v___x_522_ = lean_array_push(v_a_511_, v___x_520_);
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lake_GitRepo_getHeadRevision(v_repo_524_, v_a_525_);
return v_res_527_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_530_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_531_ = lean_unsigned_to_nat(7u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_array_push(v___x_532_, v___x_530_);
return v___x_533_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_535_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__2, &l_Lake_GitRepo_fetchRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2);
v___x_536_ = lean_array_push(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_538_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__3, &l_Lake_GitRepo_fetchRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3);
v___x_539_ = lean_array_push(v___x_538_, v___x_537_);
return v___x_539_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__0));
v___x_541_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__4, &l_Lake_GitRepo_fetchRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4);
v___x_542_ = lean_array_push(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__1));
v___x_544_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__5, &l_Lake_GitRepo_fetchRevision_x3f___closed__5_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5);
v___x_545_ = lean_array_push(v___x_544_, v___x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object* v_repo_547_, lean_object* v_remote_548_, lean_object* v_rev_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_552_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__6, &l_Lake_GitRepo_fetchRevision_x3f___closed__6_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6);
v___x_553_ = lean_array_push(v___x_552_, v_remote_548_);
v___x_554_ = lean_array_push(v___x_553_, v_rev_549_);
v___x_555_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_556_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
lean_inc_ref(v_repo_547_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v_repo_547_);
v___x_558_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_559_ = 1;
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_561_, 0, v___x_555_);
lean_ctor_set(v___x_561_, 1, v___x_556_);
lean_ctor_set(v___x_561_, 2, v___x_554_);
lean_ctor_set(v___x_561_, 3, v___x_557_);
lean_ctor_set(v___x_561_, 4, v___x_558_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*5, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*5 + 1, v___x_560_);
v___x_562_ = l_Lake_testProc(v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_repo_547_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v_a_550_);
return v___x_564_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lake_GitRev_fetchHead___closed__0));
lean_inc_ref(v_repo_547_);
v___x_566_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_565_, v_repo_547_);
if (lean_obj_tag(v___x_566_) == 1)
{
lean_object* v___x_567_; 
lean_dec_ref(v_repo_547_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_a_550_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_566_);
v___x_568_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__7));
v___x_569_ = lean_string_append(v_repo_547_, v___x_568_);
v___x_570_ = 3;
v___x_571_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*1, v___x_570_);
v___x_572_ = lean_array_get_size(v_a_550_);
v___x_573_ = lean_array_push(v_a_550_, v___x_571_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object* v_repo_575_, lean_object* v_remote_576_, lean_object* v_rev_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_575_, v_remote_576_, v_rev_577_, v_a_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_585_);
lean_dec_ref(v_s_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_it_593_; lean_object* v_startInclusive_594_; lean_object* v_endExclusive_595_; 
if (lean_obj_tag(v_a_590_) == 0)
{
lean_object* v_currPos_600_; lean_object* v_searcher_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_627_; 
v_currPos_600_ = lean_ctor_get(v_a_590_, 0);
v_searcher_601_ = lean_ctor_get(v_a_590_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_590_);
if (v_isSharedCheck_627_ == 0)
{
v___x_603_ = v_a_590_;
v_isShared_604_ = v_isSharedCheck_627_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_searcher_601_);
lean_inc(v_currPos_600_);
lean_dec(v_a_590_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_627_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_startInclusive_605_; lean_object* v_endExclusive_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_startInclusive_605_ = lean_ctor_get(v___x_588_, 1);
v_endExclusive_606_ = lean_ctor_get(v___x_588_, 2);
v___x_607_ = lean_nat_sub(v_endExclusive_606_, v_startInclusive_605_);
v___x_608_ = lean_nat_dec_eq(v_searcher_601_, v___x_607_);
lean_dec(v___x_607_);
if (v___x_608_ == 0)
{
uint32_t v___x_609_; uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_609_ = 10;
v___x_610_ = lean_string_utf8_get_fast(v___x_587_, v_searcher_601_);
v___x_611_ = lean_uint32_dec_eq(v___x_610_, v___x_609_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_string_utf8_next_fast(v___x_587_, v_searcher_601_);
lean_dec(v_searcher_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_612_);
v___x_614_ = v___x_603_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_currPos_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_590_ = v___x_614_;
goto _start;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_slice_620_; lean_object* v_nextIt_622_; 
v___x_617_ = lean_string_utf8_next_fast(v___x_587_, v_searcher_601_);
v___x_618_ = lean_nat_sub(v___x_617_, v_searcher_601_);
v___x_619_ = lean_nat_add(v_searcher_601_, v___x_618_);
lean_dec(v___x_618_);
v_slice_620_ = l_String_Slice_subslice_x21(v___x_588_, v_currPos_600_, v_searcher_601_);
lean_inc(v___x_619_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v___x_619_);
lean_ctor_set(v___x_603_, 0, v___x_619_);
v_nextIt_622_ = v___x_603_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_619_);
v_nextIt_622_ = v_reuseFailAlloc_625_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v_startInclusive_623_; lean_object* v_endExclusive_624_; 
v_startInclusive_623_ = lean_ctor_get(v_slice_620_, 0);
lean_inc(v_startInclusive_623_);
v_endExclusive_624_ = lean_ctor_get(v_slice_620_, 1);
lean_inc(v_endExclusive_624_);
lean_dec_ref(v_slice_620_);
v_it_593_ = v_nextIt_622_;
v_startInclusive_594_ = v_startInclusive_623_;
v_endExclusive_595_ = v_endExclusive_624_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_626_; 
lean_del_object(v___x_603_);
lean_dec(v_searcher_601_);
v___x_626_ = lean_box(1);
lean_inc(v___x_589_);
v_it_593_ = v___x_626_;
v_startInclusive_594_ = v_currPos_600_;
v_endExclusive_595_ = v___x_589_;
goto v___jp_592_;
}
}
}
else
{
lean_dec(v___x_589_);
lean_dec_ref(v___x_587_);
return v_b_591_;
}
v___jp_592_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_inc_ref(v___x_587_);
v___x_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_596_, 0, v___x_587_);
lean_ctor_set(v___x_596_, 1, v_startInclusive_594_);
lean_ctor_set(v___x_596_, 2, v_endExclusive_595_);
v___x_597_ = l_String_Slice_toString(v___x_596_);
lean_dec_ref_known(v___x_596_, 3);
v___x_598_ = lean_array_push(v_b_591_, v___x_597_);
v_a_590_ = v_it_593_;
v_b_591_ = v___x_598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v_a_631_, lean_object* v_b_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_628_, v___x_629_, v___x_630_, v_a_631_, v_b_632_);
lean_dec_ref(v___x_629_);
return v_res_633_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_643_ = lean_unsigned_to_nat(2u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_array_push(v___x_644_, v___x_642_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_646_, lean_object* v_n_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___y_651_; lean_object* v_args_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_args_697_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v_n_647_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_700_ = l_Nat_reprFast(v_n_647_);
v___x_701_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_702_ = lean_array_push(v___x_701_, v___x_700_);
v___x_703_ = l_Array_append___redArg(v_args_697_, v___x_702_);
lean_dec_ref(v___x_702_);
v___y_651_ = v___x_703_;
goto v___jp_650_;
}
else
{
lean_dec(v_n_647_);
v___y_651_ = v_args_697_;
goto v___jp_650_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_652_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_653_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v_repo_646_);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_657_ = 1;
v___x_658_ = 0;
v___x_659_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_659_, 0, v___x_652_);
lean_ctor_set(v___x_659_, 1, v___x_653_);
lean_ctor_set(v___x_659_, 2, v___y_651_);
lean_ctor_set(v___x_659_, 3, v___x_654_);
lean_ctor_set(v___x_659_, 4, v___x_656_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*5, v___x_657_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*5 + 1, v___x_658_);
v___x_660_ = l_Lake_captureProc_x27(v___x_659_, v_a_648_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_687_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_a_662_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_687_ == 0)
{
v___x_664_ = v___x_660_;
v_isShared_665_ = v_isSharedCheck_687_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_687_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_stdout_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_str_670_; lean_object* v_startInclusive_671_; lean_object* v_endExclusive_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_686_; 
v_stdout_666_ = lean_ctor_get(v_a_661_, 0);
lean_inc_ref(v_stdout_666_);
lean_dec(v_a_661_);
v___x_667_ = lean_string_utf8_byte_size(v_stdout_666_);
v___x_668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_668_, 0, v_stdout_666_);
lean_ctor_set(v___x_668_, 1, v___x_655_);
lean_ctor_set(v___x_668_, 2, v___x_667_);
v___x_669_ = l_String_Slice_trimAscii(v___x_668_);
v_str_670_ = lean_ctor_get(v___x_669_, 0);
v_startInclusive_671_ = lean_ctor_get(v___x_669_, 1);
v_endExclusive_672_ = lean_ctor_get(v___x_669_, 2);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_674_ = v___x_669_;
v_isShared_675_ = v_isSharedCheck_686_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_endExclusive_672_);
lean_inc(v_startInclusive_671_);
lean_inc(v_str_670_);
lean_dec(v___x_669_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_686_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_676_ = lean_string_utf8_extract(v_str_670_, v_startInclusive_671_, v_endExclusive_672_);
lean_dec(v_endExclusive_672_);
lean_dec(v_startInclusive_671_);
lean_dec_ref(v_str_670_);
v___x_677_ = lean_string_utf8_byte_size(v___x_676_);
lean_inc_ref(v___x_676_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 2, v___x_677_);
lean_ctor_set(v___x_674_, 1, v___x_655_);
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_679_ = v___x_674_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_677_);
v___x_679_ = v_reuseFailAlloc_685_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_680_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_679_);
v___x_681_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_676_, v___x_679_, v___x_677_, v___x_680_, v___x_656_);
lean_dec_ref(v___x_679_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_681_);
v___x_683_ = v___x_664_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_a_662_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_688_ = lean_ctor_get(v___x_660_, 0);
v_a_689_ = lean_ctor_get(v___x_660_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_660_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_660_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_704_, lean_object* v_n_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lake_GitRepo_getHeadRevisions(v_repo_704_, v_n_705_, v_a_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_inst_712_, lean_object* v_R_713_, lean_object* v_a_714_, lean_object* v_b_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_709_, v___x_710_, v___x_711_, v_a_714_, v_b_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v___x_719_, lean_object* v_inst_720_, lean_object* v_R_721_, lean_object* v_a_722_, lean_object* v_b_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_717_, v___x_718_, v___x_719_, v_inst_720_, v_R_721_, v_a_722_, v_b_723_);
lean_dec_ref(v___x_718_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_725_, lean_object* v_remote_726_, lean_object* v_repo_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_rev_731_; lean_object* v___y_732_; uint8_t v___x_734_; 
v___x_734_ = l_Lake_GitRev_isFullSha1(v_rev_725_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_736_ = lean_string_append(v_remote_726_, v___x_735_);
v___x_737_ = lean_string_append(v___x_736_, v_rev_725_);
lean_inc_ref(v_repo_727_);
v___x_738_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_737_, v_repo_727_);
if (lean_obj_tag(v___x_738_) == 1)
{
lean_object* v_val_739_; 
lean_dec_ref(v_repo_727_);
lean_dec_ref(v_rev_725_);
v_val_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_738_, 1);
v_rev_731_ = v_val_739_;
v___y_732_ = v_a_728_;
goto v___jp_730_;
}
else
{
lean_object* v___x_740_; 
lean_dec(v___x_738_);
lean_inc_ref(v_repo_727_);
lean_inc_ref(v_rev_725_);
v___x_740_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_725_, v_repo_727_);
if (lean_obj_tag(v___x_740_) == 1)
{
lean_object* v_val_741_; 
lean_dec_ref(v_repo_727_);
lean_dec_ref(v_rev_725_);
v_val_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_740_, 1);
v_rev_731_ = v_val_741_;
v___y_732_ = v_a_728_;
goto v___jp_730_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v___x_740_);
v___x_742_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_743_ = lean_string_append(v_repo_727_, v___x_742_);
v___x_744_ = lean_string_append(v___x_743_, v_rev_725_);
lean_dec_ref(v_rev_725_);
v___x_745_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_746_ = lean_string_append(v___x_744_, v___x_745_);
v___x_747_ = 3;
v___x_748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_747_);
v___x_749_ = lean_array_get_size(v_a_728_);
v___x_750_ = lean_array_push(v_a_728_, v___x_748_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
return v___x_751_;
}
}
}
else
{
lean_object* v___x_752_; 
lean_dec_ref(v_repo_727_);
lean_dec_ref(v_remote_726_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_rev_725_);
lean_ctor_set(v___x_752_, 1, v_a_728_);
return v___x_752_;
}
v___jp_730_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_rev_731_);
lean_ctor_set(v___x_733_, 1, v___y_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_753_, lean_object* v_remote_754_, lean_object* v_repo_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_753_, v_remote_754_, v_repo_755_, v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_759_, lean_object* v_rev_x3f_760_, lean_object* v_remote_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_764_; 
lean_inc_ref(v_remote_761_);
lean_inc_ref(v_repo_759_);
v___x_764_ = l_Lake_GitRepo_fetch(v_repo_759_, v_remote_761_, v_a_762_);
if (lean_obj_tag(v___x_764_) == 0)
{
if (lean_obj_tag(v_rev_x3f_760_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 2);
v___x_766_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_767_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_766_, v_remote_761_, v_repo_759_, v_a_765_);
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v_val_769_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_764_, 2);
v_val_769_ = lean_ctor_get(v_rev_x3f_760_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_rev_x3f_760_, 1);
v___x_770_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_769_, v_remote_761_, v_repo_759_, v_a_768_);
return v___x_770_;
}
}
else
{
lean_object* v_a_771_; lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v_remote_761_);
lean_dec(v_rev_x3f_760_);
lean_dec_ref(v_repo_759_);
v_a_771_ = lean_ctor_get(v___x_764_, 0);
v_a_772_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_764_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_inc(v_a_771_);
lean_dec(v___x_764_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_771_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_780_, lean_object* v_rev_x3f_781_, lean_object* v_remote_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lake_GitRepo_findRemoteRevision(v_repo_780_, v_rev_x3f_781_, v_remote_782_, v_a_783_);
return v_res_785_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_789_ = lean_unsigned_to_nat(3u);
v___x_790_ = lean_mk_empty_array_with_capacity(v___x_789_);
v___x_791_ = lean_array_push(v___x_790_, v___x_788_);
return v___x_791_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_793_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_794_ = lean_array_push(v___x_793_, v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_795_, lean_object* v_repo_796_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_798_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_799_ = lean_string_append(v___x_798_, v_rev_795_);
v___x_800_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_801_ = lean_array_push(v___x_800_, v___x_799_);
v___x_802_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_803_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_repo_796_);
v___x_805_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_806_ = 1;
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_803_);
lean_ctor_set(v___x_808_, 2, v___x_801_);
lean_ctor_set(v___x_808_, 3, v___x_804_);
lean_ctor_set(v___x_808_, 4, v___x_805_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5 + 1, v___x_807_);
v___x_809_ = l_Lake_testProc(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_810_, lean_object* v_repo_811_, lean_object* v_a_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lake_GitRepo_branchExists(v_rev_810_, v_repo_811_);
lean_dec_ref(v_rev_810_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_816_ = lean_unsigned_to_nat(3u);
v___x_817_ = lean_mk_empty_array_with_capacity(v___x_816_);
v___x_818_ = lean_array_push(v___x_817_, v___x_815_);
return v___x_818_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_820_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__0, &l_Lake_GitRepo_revisionExists___closed__0_once, _init_l_Lake_GitRepo_revisionExists___closed__0);
v___x_821_ = lean_array_push(v___x_820_, v___x_819_);
return v___x_821_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_822_, lean_object* v_repo_823_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_825_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_826_ = lean_string_append(v_rev_822_, v___x_825_);
v___x_827_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_828_ = lean_array_push(v___x_827_, v___x_826_);
v___x_829_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_830_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v_repo_823_);
v___x_832_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_833_ = 1;
v___x_834_ = 0;
v___x_835_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_835_, 0, v___x_829_);
lean_ctor_set(v___x_835_, 1, v___x_830_);
lean_ctor_set(v___x_835_, 2, v___x_828_);
lean_ctor_set(v___x_835_, 3, v___x_831_);
lean_ctor_set(v___x_835_, 4, v___x_832_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*5, v___x_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*5 + 1, v___x_834_);
v___x_836_ = l_Lake_testProc(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_837_, lean_object* v_repo_838_, lean_object* v_a_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l_Lake_GitRepo_revisionExists(v_rev_837_, v_repo_838_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_847_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; uint8_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_849_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_850_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_851_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v_repo_847_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_855_ = 1;
v___x_856_ = 0;
v___x_857_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_857_, 0, v___x_850_);
lean_ctor_set(v___x_857_, 1, v___x_851_);
lean_ctor_set(v___x_857_, 2, v___x_849_);
lean_ctor_set(v___x_857_, 3, v___x_852_);
lean_ctor_set(v___x_857_, 4, v___x_854_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*5, v___x_855_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*5 + 1, v___x_856_);
v___x_858_ = l_Lake_captureProc_x3f(v___x_857_);
if (lean_obj_tag(v___x_858_) == 1)
{
lean_object* v_val_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_val_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc_n(v_val_859_, 2);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_string_utf8_byte_size(v_val_859_);
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v_val_859_);
lean_ctor_set(v___x_861_, 1, v___x_853_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
v___x_862_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_861_);
v___x_863_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_859_, v___x_861_, v___x_860_, v___x_862_, v___x_854_);
lean_dec_ref_known(v___x_861_, 3);
v___x_864_ = lean_array_to_list(v___x_863_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; 
lean_dec(v___x_858_);
v___x_865_ = lean_box(0);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lake_GitRepo_getTags(v_repo_866_);
return v_res_868_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_871_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_872_ = lean_unsigned_to_nat(4u);
v___x_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_874_ = lean_array_push(v___x_873_, v___x_871_);
return v___x_874_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_876_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_877_ = lean_array_push(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_879_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_880_ = lean_array_push(v___x_879_, v___x_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_881_, lean_object* v_repo_882_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_884_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_885_ = lean_array_push(v___x_884_, v_rev_881_);
v___x_886_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_887_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_888_, 0, v_repo_882_);
v___x_889_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_890_ = 1;
v___x_891_ = 0;
v___x_892_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_892_, 0, v___x_886_);
lean_ctor_set(v___x_892_, 1, v___x_887_);
lean_ctor_set(v___x_892_, 2, v___x_885_);
lean_ctor_set(v___x_892_, 3, v___x_888_);
lean_ctor_set(v___x_892_, 4, v___x_889_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*5, v___x_890_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*5 + 1, v___x_891_);
v___x_893_ = l_Lake_captureProc_x3f(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_894_, lean_object* v_repo_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lake_GitRepo_findTag_x3f(v_rev_894_, v_repo_895_);
return v_res_897_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_901_ = lean_unsigned_to_nat(3u);
v___x_902_ = lean_mk_empty_array_with_capacity(v___x_901_);
v___x_903_ = lean_array_push(v___x_902_, v___x_900_);
return v___x_903_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_905_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_906_ = lean_array_push(v___x_905_, v___x_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_907_, lean_object* v_repo_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_910_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_911_ = lean_array_push(v___x_910_, v_remote_907_);
v___x_912_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_913_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_repo_908_);
v___x_915_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_916_ = 1;
v___x_917_ = 0;
v___x_918_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_918_, 0, v___x_912_);
lean_ctor_set(v___x_918_, 1, v___x_913_);
lean_ctor_set(v___x_918_, 2, v___x_911_);
lean_ctor_set(v___x_918_, 3, v___x_914_);
lean_ctor_set(v___x_918_, 4, v___x_915_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5, v___x_916_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*5 + 1, v___x_917_);
v___x_919_ = l_Lake_captureProc_x3f(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_920_, lean_object* v_repo_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_920_, v_repo_921_);
return v_res_923_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__0(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_925_ = lean_unsigned_to_nat(4u);
v___x_926_ = lean_mk_empty_array_with_capacity(v___x_925_);
v___x_927_ = lean_array_push(v___x_926_, v___x_924_);
return v___x_927_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_929_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_930_ = lean_array_push(v___x_929_, v___x_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object* v_remote_931_, lean_object* v_url_932_, lean_object* v_repo_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_936_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__1, &l_Lake_GitRepo_addRemote___closed__1_once, _init_l_Lake_GitRepo_addRemote___closed__1);
v___x_937_ = lean_array_push(v___x_936_, v_remote_931_);
v___x_938_ = lean_array_push(v___x_937_, v_url_932_);
v___x_939_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_940_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_repo_933_);
v___x_942_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_943_ = 1;
v___x_944_ = 0;
v___x_945_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_945_, 0, v___x_939_);
lean_ctor_set(v___x_945_, 1, v___x_940_);
lean_ctor_set(v___x_945_, 2, v___x_938_);
lean_ctor_set(v___x_945_, 3, v___x_941_);
lean_ctor_set(v___x_945_, 4, v___x_942_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*5, v___x_943_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*5 + 1, v___x_944_);
v___x_946_ = lean_box(0);
v___x_947_ = l_Lake_proc(v___x_945_, v___x_943_, v___x_946_, v_a_934_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object* v_remote_948_, lean_object* v_url_949_, lean_object* v_repo_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lake_GitRepo_addRemote(v_remote_948_, v_url_949_, v_repo_950_, v_a_951_);
return v_res_953_;
}
}
static lean_object* _init_l_Lake_GitRepo_setRemoteUrl___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = ((lean_object*)(l_Lake_GitRepo_setRemoteUrl___closed__0));
v___x_956_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_957_ = lean_array_push(v___x_956_, v___x_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object* v_remote_958_, lean_object* v_url_959_, lean_object* v_repo_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_963_ = lean_obj_once(&l_Lake_GitRepo_setRemoteUrl___closed__1, &l_Lake_GitRepo_setRemoteUrl___closed__1_once, _init_l_Lake_GitRepo_setRemoteUrl___closed__1);
v___x_964_ = lean_array_push(v___x_963_, v_remote_958_);
v___x_965_ = lean_array_push(v___x_964_, v_url_959_);
v___x_966_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_967_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v_repo_960_);
v___x_969_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_970_ = 1;
v___x_971_ = 0;
v___x_972_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_972_, 0, v___x_966_);
lean_ctor_set(v___x_972_, 1, v___x_967_);
lean_ctor_set(v___x_972_, 2, v___x_965_);
lean_ctor_set(v___x_972_, 3, v___x_968_);
lean_ctor_set(v___x_972_, 4, v___x_969_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*5, v___x_970_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*5 + 1, v___x_971_);
v___x_973_ = lean_box(0);
v___x_974_ = l_Lake_proc(v___x_972_, v___x_970_, v___x_973_, v_a_961_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object* v_remote_975_, lean_object* v_url_976_, lean_object* v_repo_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lake_GitRepo_setRemoteUrl(v_remote_975_, v_url_976_, v_repo_977_, v_a_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_981_, lean_object* v_repo_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_981_, v_repo_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_986_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lake_Git_filterUrl_x3f(v_val_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_987_, lean_object* v_repo_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_987_, v_repo_988_);
return v_res_990_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_1001_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1003_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_1004_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1005_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_repo_1001_);
v___x_1007_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1008_ = 1;
v___x_1009_ = 0;
v___x_1010_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1010_, 0, v___x_1004_);
lean_ctor_set(v___x_1010_, 1, v___x_1005_);
lean_ctor_set(v___x_1010_, 2, v___x_1003_);
lean_ctor_set(v___x_1010_, 3, v___x_1006_);
lean_ctor_set(v___x_1010_, 4, v___x_1007_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*5, v___x_1008_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*5 + 1, v___x_1009_);
v___x_1011_ = l_Lake_testProc(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = l_Lake_GitRepo_hasNoDiff(v_repo_1012_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_1016_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = l_Lake_GitRepo_hasNoDiff(v_repo_1016_);
if (v___x_1018_ == 0)
{
uint8_t v___x_1019_; 
v___x_1019_ = 1;
return v___x_1019_;
}
else
{
uint8_t v___x_1020_; 
v___x_1020_ = 0;
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_1021_, lean_object* v_a_1022_){
_start:
{
uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_res_1023_ = l_Lake_GitRepo_hasDiff(v_repo_1021_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
