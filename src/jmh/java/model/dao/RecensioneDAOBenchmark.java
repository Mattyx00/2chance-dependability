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

    @Setup(Level.Trial)
    public void setup() {
        recensioneDAO = new RecensioneDAO();

        validRecensione = new Recensione();
        Utente u = new Utente();
        u.setId(1);
        validRecensione.setUtente(u);

        Prodotto p = new Prodotto();
        p.setId(1);
        validRecensione.setProdotto(p);

        validRecensione.setTesto("Valid review text for benchmark.");
        validRecensione.setValutazione(5);
    }

    @Benchmark
    public void benchmarkAddRecensione(Blackhole bh) {
        try {
            // This will execute validation logic and attempt DB insertion
            // If DB is offline, it will throw SQLException which we catch
            // If DB is online, it will insert (benchmark side effect)
            recensioneDAO.addRecensione(validRecensione);
        } catch (SQLException e) {
            bh.consume(e);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        }
    }
}
