void acl_create_entry(int *other_p, int *entry_p) {
  if(!other_p || !entry_p) {
    if(entry_p)
      *entry_p = 5;

    return;
  }

  *entry_p = 6;
}
