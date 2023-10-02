uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 0;
  x = malloc(8);

  *x = 0;

  a = a + read(0, x, 2);
  if(a != 2){
      if(a == 0){
          a = 1/0; //n=97
      }else{
          if(a == 1){
              a = 1/0; //n=104
          }else{
              if(a == -1){
                  a = 1/0; //n=110,n=111
              }
          }
      }
      return 0;
  }

  a = a + read(0, x, 2);
    if(a != 4){
        if(a == 2){
            a = 1/0; //n=131
        }else{
            if(a == 3){
                a = 1/0; //n=138
            }else{
                if(a == 1){
                    a = 1/0; //n=143,n=144
                }
            }
        }
        return 0;
    }

    a = a + read(0, x, 0);
    if(a != 4){
        if(a == 2){
            a = 1/0;
        }else{
            if(a == 3){
                a = 1/0; //n=171
            }else{
                if(a == 1){
                    a = 1/0;
                }
            }
        }
        return 0;
    }

    a = a + read(0, x, 1);
    if(a != 5){
        if(a == 4){
            a = 1/0; //n=198
        }else{
            if(a == 3){
                a = 1/0;
            }
        }
        return 0;
    }

    a = a + read(0, x, 3);
    if(a != 8){
        if(a == 5){
            a = 1/0; //n=232
        }else{
            if(a == 6){
                a = 1/0; //n=239
            }else{
                if(a == 7){
                    a = 1/0; //n=245
                }else{
                    if(a == 4){
                        a = 1/0; //n=250,n=251
                    }
                }
            }
        }
        return 0;
    }

    return 0;

}
