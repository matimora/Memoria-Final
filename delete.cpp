if (aux_leaf->vect.size() > 256 / 2)
  {

    aux_leaf->vect.erase(aux_leaf->vect.begin() + pos);
    input_value(leaf_open);
    update_value(leaf_open);
  }
  else
  {
    /**PEDIR PARENTESIS BLOQUE ANTERIOR**/
    if (aux_leaf->prev != NULL && aux_leaf->prev->vect.size() > 256 / 2)
    {
      Node *parent_leaf = aux_leaf->prev->leaf;

      aux_leaf->vect.insert(aux_leaf->vect.begin(), aux_leaf->prev->vect[aux_leaf->prev->vect.size()]);
      aux_leaf->prev->vect.erase(aux_leaf->prev->vect.begin() + aux_leaf->prev->vect.size());
      input_value(parent_leaf);
      update_value(parent_leaf);
      aux_leaf->vect.erase(aux_leaf->vect.begin() + (pos + 1));
      input_value(leaf_open);
      update_value(leaf_open);
    }
    /**PEDIR PARENTESIS BLOQUE SIGUIENTE**/
    else if (aux_leaf->next != NULL && aux_leaf->prev->vect.size() < 256 / 2 && aux_leaf->next->vect.size() > 256 / 2)
    {
      Node *parent_leaf = aux_leaf->next->leaf;

      aux_leaf->vect.insert(aux_leaf->vect.begin() + aux_leaf->vect.size(), aux_leaf->next->vect[aux_leaf->next->vect[0]]);
      aux_leaf->next->vect.erase(aux_leaf->next->vect.begin());
      input_value(parent_leaf);
      update_value(parent_leaf);
      aux_leaf->vect.erase(aux_leaf->vect.begin() + pos);
      input_value(leaf_open);
      update_value(leaf_open);
    }
    /**FUSION CON EL BLOQUE ANTERIOR**/
    else if (aux_leaf->prev != NULL && aux_leaf->prev->vect.size() < 256 / 2)
    {
      int size_prev = aux_leaf->prev->vect.size();
      Node *parent_aux = aux_leaf->prev->leaf->parent;
      Node *leaf_prev = aux_leaf->prev->leaf;
      for (int i = 0; i < size_prev; i++)
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + i, aux_leaf->prev->vect[i]);
      }
      for (int i = 0; i < size_prev; i++)
      {
        aux_leaf->prev->vect.erase(aux_leaf->prev->vect.begin() + i);
      }
      input_value(leaf_prev);
      update_value(leaf_prev);
      aux_leaf->vect.erase(aux_leaf->vect.begin() + (pos + size_prev));
      input_value(leaf_open);
      update_value(leaf_open);
      aux_leaf->prev = aux_leaf->prev->prev;
      aux_leaf->prev->prev->next = aux_leaf;
      if (parent_aux->right == leaf_prev)
      {
        parent_aux->right = NULL;
      }
      if (parent_aux->left == leaf_prev)
      {
        parent_aux->left = NULL;
      }
      delete leaf_prev->y;
      delete leaf_prev;
      if (parent_aux->left == NULL && parent_aux->right == NULL)
      {
        // p = reestruct(p);
      }
    }
    /**FUSION BLOQUE SIGUIENTE**/
    else if (aux_leaf->next != NULL && aux_leaf->next->vect.size() < 256 / 2)
    {
      Node *parent_aux = aux_leaf->next->leaf->parent;
      Node *leaf_next = aux_leaf->next->leaf;
      int size_next = aux_leaf->next->vect.size();
      for (int i = 0; i < size_next; i++)
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + (aux_leaf->vect.size() + i), aux_leaf->next->vect[i]);
      }
      for (int i = 0; i < size_next; i++)
      {
        aux_leaf->next->vect.erase(aux_leaf->next->vect.begin() + i);
      }
      input_value(leaf_next);
      update_value(leaf_next);
      aux_leaf->vect.erase(aux_leaf->vect.begin() + pos);
      input_value(leaf_open);
      update_value(leaf_open);
      aux_leaf->next = aux_leaf->next->next;
      aux_leaf->next->next->prev = aux_leaf;
      if (parent_aux->right == leaf_next)
      {
        parent_aux->right = NULL;
      }
      if (parent_aux->left == leaf_next)
      {
        parent_aux->left = NULL;
      }
      Block **aux_delete = &(leaf_next->y);
      leaf_next->y->leaf = NULL;
      leaf_next->x = NULL;
      leaf_next->y->next = NULL;
      leaf_next->y->prev = NULL;
      leaf_next->parent = NULL;
      leaf_next->y = NULL;
      delete *aux_delete;
      // delete *aux_delete;
      //  delete leaf_next;
      //  parent_aux->update_tree(parent_aux);
      if (parent_aux->left == NULL && parent_aux->right == NULL)
      {
        // p = reestruct(p);
      }
    }
  }
  /**Parentesis de cierre**/

  if (aux_close->vect.size() > 256 / 2)
  {
    aux_close->vect.erase(aux_close->vect.begin() + close);
    input_value(leaf_close);
    update_value(leaf_close);
  }
  /**FALTA EL ELSE**/
  else
  {
    /**PEDIR PARENTESIS BLOQUE ANTERIOR**/
    if (aux_close->prev->vect.size() > 256 / 2)
    {
      Node *parent_leaf = aux_close->prev->leaf;

      aux_close->vect.insert(aux_close->vect.begin(), aux_close->prev->vect[aux_close->prev->vect.size()]);
      aux_close->prev->vect.erase(aux_close->prev->vect.begin() + aux_close->prev->vect.size());
      input_value(parent_leaf);
      update_value(parent_leaf);
      aux_leaf->vect.erase(aux_leaf->vect.begin() + (pos + 1));
      input_value(leaf_close);
      update_value(leaf_close);
    }
    /**PEDIR PARENTESIS BLOQUE SIGUIENTE**/
    else if (aux_close->next->vect.size() > 256 / 2)
    {
      Node *parent_leaf = aux_close->next->leaf;

      aux_close->vect.insert(aux_close->vect.begin() + aux_close->vect.size(), aux_close->next->vect[aux_close->next->vect[0]]);
      aux_close->next->vect.erase(aux_close->next->vect.begin());
      input_value(parent_leaf);
      update_value(parent_leaf);
      aux_close->vect.erase(aux_close->vect.begin() + pos);
      input_value(leaf_close);
      update_value(leaf_close);
    }
    /**FUSION CON EL BLOQUE ANTERIOR**/
    else if (aux_close->prev != NULL && aux_close->prev->vect.size() < 256 / 2)
    {
      int size_prev = aux_close->prev->vect.size();
      Node *parent_aux = aux_close->prev->leaf->parent;
      Node *leaf_prev = aux_close->prev->leaf;
      for (int i = 0; i < size_prev; i++)
      {
        aux_close->vect.insert(aux_close->vect.begin() + i, aux_close->prev->vect[i]);
      }
      for (int i = 0; i < size_prev; i++)
      {
        aux_close->prev->vect.erase(aux_close->prev->vect.begin() + i);
      }
      input_value(leaf_prev);
      update_value(leaf_prev);
      aux_close->vect.erase(aux_close->vect.begin() + (pos + size_prev));
      input_value(leaf_close);
      update_value(leaf_close);
      aux_close->prev = aux_close->prev->prev;
      aux_close->prev->prev->next = aux_close;
      delete leaf_prev;
      delete aux_close->prev;
      // parent_aux->update_tree(parent_aux);
      if (parent_aux->left == NULL && parent_aux->right == NULL)
      {
        // p = reestruct(p);
      }
    }
    /**FUSION BLOQUE SIGUIENTE**/
    else if (aux_close->next != NULL && aux_close->next->vect.size() < 256 / 2)
    {
      Node *parent_aux = aux_close->next->leaf->parent;
      Node *leaf_next = aux_close->next->leaf;
      int size_next = aux_close->next->vect.size();
      for (int i = 0; i < size_next; i++)
      {
        aux_close->vect.insert(aux_close->vect.begin() + (aux_close->vect.size() + i), aux_close->next->vect[i]);
      }
      for (int i = 0; i < size_next; i++)
      {
        aux_close->next->vect.erase(aux_close->prev->vect.begin() + i);
      }
      input_value(leaf_next);
      update_value(leaf_next);
      aux_close->vect.erase(aux_close->vect.begin() + pos);
      input_value(leaf_close);
      update_value(leaf_close);
      aux_close->next = aux_close->next->next;
      aux_close->next->next->prev = aux_close;
      delete leaf_next;
      delete aux_close->next;
      // parent_aux->update_tree(parent_aux);
      if (parent_aux->left == NULL && parent_aux->right == NULL)
      {
        // p = reestruct(p);
      }
    }
  }