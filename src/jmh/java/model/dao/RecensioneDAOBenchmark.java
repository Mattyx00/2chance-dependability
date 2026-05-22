package model.dao;

import model.beans.Prodotto;
import model.beans.Recensione;
import model.beans.Utente;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.SQLException;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS) // Use ms as DB ops are slow
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class RecensioneDAOBenchmark {

    private RecensioneDAO recensioneDAO;
    private Recensione validRecensione;

    private Utente validUtente;
    private Utente invalidUtente;
    private Utente nonExistentUtente;

    private Prodotto validProdotto;
    private Prodotto invalidProdotto;
    private Prodotto nonExistentProdotto;

    @Setup(Level.Trial)
    public void setup() {
        recensioneDAO = new RecensioneDAO();

        // Setup for addRecensione
        validRecensione = new Recensione();
        Utente u = new Utente();
        u.setId(1);
        validRecensione.setUtente(u);

        Prodotto p = new Prodotto();
        p.setId(1);
        validRecensione.setProdotto(p);

        validRecensione.setTesto("Valid review text for benchmark.");
        validRecensione.setValutazione(5);

        // Setup for query benchmarks
        validUtente = new Utente();
        validUtente.setId(10); // Valid user with reviews in db_import.sql

        invalidUtente = new Utente();
        invalidUtente.setId(-1);

        nonExistentUtente = new Utente();
        nonExistentUtente.setId(999);

        validProdotto = new Prodotto();
        validProdotto.setId(11); // Valid product with reviews in db_import.sql

        invalidProdotto = new Prodotto();
        invalidProdotto.setId(-1);

        nonExistentProdotto = new Prodotto();
        nonExistentProdotto.setId(999);
    }

    @Benchmark
    public void benchmarkAddRecensione(Blackhole bh) {
        try {
            recensioneDAO.addRecensione(validRecensione);
        } catch (SQLException e) {
            bh.consume(e);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByProdottoValid(Blackhole bh) {
        try {
            bh.consume(recensioneDAO.getRecensioniByProdotto(validProdotto));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByProdottoNonExistent(Blackhole bh) {
        try {
            bh.consume(recensioneDAO.getRecensioniByProdotto(nonExistentProdotto));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByProdottoInvalid(Blackhole bh) {
        try {
            recensioneDAO.getRecensioniByProdotto(invalidProdotto);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByUtenteValid(Blackhole bh) {
        try {
            bh.consume(recensioneDAO.getRecensioniByUtente(validUtente));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByUtenteNonExistent(Blackhole bh) {
        try {
            bh.consume(recensioneDAO.getRecensioniByUtente(nonExistentUtente));
        } catch (SQLException e) {
            bh.consume(e);
        }
    }

    @Benchmark
    public void benchmarkGetRecensioniByUtenteInvalid(Blackhole bh) {
        try {
            recensioneDAO.getRecensioniByUtente(invalidUtente);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }
}
