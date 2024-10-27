create table obj (
    k char(1) primary key,
    v int
);

--- For postgres
ALTER DATABASE tla SET default_transaction_isolation TO 'repeatable read';

insert into obj (k,v) values ('x', 0), ('y', 0);

--
update obj set v=0;
--



-- T1
begin;
select k,v from obj where k='y';

                                        -- T2
                                        begin;
                                        select k,v from obj where k='x';
                                        update obj set v=1 where k='y';
                                        commit;

update obj set v=1 where k='x';
commit;

-- T1
begin;
select k,v from obj where k='y';

                                        -- T2
                                        begin;
                                        update obj set v=1 where k='y';
                                        commit;

update obj set v=1 where k='x';

                                                                                -- T3
                                                                                begin;
                                                                                select k,v from obj where k='x';
                                                                                select k,v from obj where k='y';
                                                                                commit;

commit;


------------------------

-- T1
begin;
update obj set v=1 where k='x';


-- T2
begin;
update obj set v=2 where k='y';
update obj set v=2 where k='x';

-- T1
update obj set v=2 where k='y';